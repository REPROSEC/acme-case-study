open Acme
open Web_Messages
open WebMessagesWrapper
open Trace
open Urls
open Log
open Pyops
module ACME_Serialization = ACME_Data_SerializationHelpers


(** Request a fresh replay nonce from the ACME server *)
let send_fresh_nonce_request (domain:string) (http_req:http_request) =
  let http_method = http_method_to_string http_req.req_method in
  let url = create_http_url domain http_req in
  let response, _ = Pythonhelpers.do_http_request ~http_method:http_method url in
  let dict_obj = response.@$("headers") in
  let nonce = Py.Object.to_string (Py.Mapping.find_string dict_obj "Replay-Nonce") in
  Trace.string_to_nonce nonce


(**
  Given a python object that is a string representing the status of an acme order, this function
  creates a status of the type acme_status.
@raise Not_found if the string is not an acme status
 *)
let py_status_to_acme_status (status:Pytypes.pyobject) : ACME_Data.acme_status =
  match Py.Object.to_string status with
  | "pending" -> Pending
  | "ready" -> Ready
  | "processing" -> Processing
  | "valid" -> Valid
  | "invalid" -> Invalid
  | _ -> raise Not_found



(**
  Given a string, this function returns an optional [ACME_Data.acme_challenge_type].
 *)
let str_to_challenge_type s : ACME_Data.acme_challenge_type option =
  match s with
  | "http-01" -> Some HTTP01
  | _ -> None


(** Create an URL from an [Pytypes.pyobject option]. [None] if the input argument is [None]. *)
let opt_py_string_to_url (opt_py_finalize_url:Pytypes.pyobject option) : Web_Messages.url option =
  match opt_py_finalize_url with
  | None -> None
  | Some py_finalize_url -> Some (string_to_url (Py.Object.to_string py_finalize_url))


(** Given an optional python object that is a list of strings representing URLs, this function
   creates an optional FStar sequence of Web.Messages.url.  *)
let create_list_of_urls (py_list:Pytypes.pyobject option) : ((Web_Messages.url FStar_Seq_Base.seq) option) =
  match py_list with
  | None -> None
  | Some py_authz_list -> (
    let list_of_str_authz = Py.List.to_list_map (fun x -> Py.Object.to_string x) py_authz_list in
    let list_of_authz_urls = List.map string_to_url list_of_str_authz in
    Some (FStar_Seq_Base.MkSeq list_of_authz_urls)
  )


(**
   Given a single python dictionary that corresponds to an acme challenge sent by the server, this
   function creates an [ACME_Data.acme_challenge].

    Example of one challenge contained in a real-world http response:
    {
      "type": "http-01",
      "status": "pending",
      "url": "https://acme-staging-v02.api.letsencrypt.org/acme/chall-v3/98765/12345",
      "token": "some-nonce-123456789"
    }
 *)
let py_challenge_dict_to_acme_challenge (challenge_dict:Pytypes.pyobject) : ACME_Data.acme_challenge =
  let type_str = Py.Object.to_string challenge_dict.%$["type"] in
  let status_py_str = challenge_dict.%$["status"] in
  let url_str = Py.Object.to_string challenge_dict.%$["url"] in
  let token_str = Py.Object.to_string challenge_dict.%$["token"] in
  match str_to_challenge_type type_str with
  | Some challenge_type ->
     {
       acme_challenge_challenge_type = challenge_type;
       acme_challenge_url = string_to_url url_str;
       acme_challenge_status = py_status_to_acme_status status_py_str;
       acme_challenge_token = Trace.string_to_nonce token_str
     }
  | _ -> raise (AcmeClientWrapperHelpers.Acme_error (__LOC__, "Unsupported challenge type: " ^ type_str))


(** Given a python object that is a list of dictionaries, where each of these dictionaries
   corresponds to an acme challenge, this function returns a list of [ACME_Data.acme_challenge]
   (filtering out any challenge that is not of type 'http-01').  *)
let py_extract_and_filter_challenges (py_challenges:Pytypes.pyobject) =
  let append_supported_chall l c =
    if "http-01" = Py.String.to_string c.%$["type"] then
      c :: l
    else l
  in
  let filtered_challenges = Py.List.fold_left append_supported_chall [] py_challenges in
  List.map py_challenge_dict_to_acme_challenge filtered_challenges


(** Given a python object that corresponds to the JSON content of an http response, this function
   returns an [ACME_Data.acme_authorization] object (if possible). *)
let py_challenge_dict_to_acme_authorization (resp_dict:Pytypes.pyobject) : ACME_Data.acme_authorization =
  (* The authorization contains one identifier. We now extract the value (domain) of this
     identifier. *)
  let identifier_string = Py.Object.to_string resp_dict.%$["identifier"].%$["value"] in
  let identifier = Root identifier_string in
  (* The authorization response contains several challenges, each having its own type (e.g.,
  'http-01' or 'dns-01'), a status, a url, and a token. *)
  let challenges = py_extract_and_filter_challenges resp_dict.%$["challenges"] in
  {
    acme_authorization_identifier = identifier;
    acme_authorization_status = py_status_to_acme_status resp_dict.%$["status"];
    acme_authorization_challenges = FStar_Seq_Base.MkSeq challenges
  }


(** Given a python object that corresponds to the JSON content of an http response, this function
   returns an [ACME_Data.acme_order] object (if possible).  *)
let py_challenge_dict_to_acme_order (resp_dict:Pytypes.pyobject) : ACME_Data.acme_order =
  let ( .%%$[] ) = Py.Dict.get_item_string in
  let identifiers = resp_dict.%$["identifiers"]
                    |> Py.List.to_list_map (fun id -> Py.Object.to_string id.%$["value"])
                    |> List.map (fun d -> Root d) in
  {
    acme_order_status = Some (py_status_to_acme_status resp_dict.%$["status"]);
    acme_order_identifiers = FStar_Seq_Base.MkSeq identifiers;
    acme_order_authorizations = create_list_of_urls resp_dict.%%$["authorizations"];
    acme_order_finalize = opt_py_string_to_url resp_dict.%%$["finalize"];
    acme_order_certificate = opt_py_string_to_url resp_dict.%%$["certificate"]
  }


(**
  Helper function creating a "real" CSR from the given ACME CSR.

  The resulting CSR is a Python string of the base64url-encoded version of the DER format, see also
  Section 7.4 of RFC 8555.
 *)
let create_payload_from_acme_csr_helper (acme_csr:ACME_Data.acme_csr) : Pytypes.pyobject =
  let py_base64 = Py.import "base64" in
  let py_rsa_crypto = Py.import "cryptography.hazmat.primitives.asymmetric.rsa" in
  let py_oid = Py.import "cryptography.x509.oid" in
  let py_x509 = Py.import "cryptography.x509" in
  let py_hashes = Py.import "cryptography.hazmat.primitives.hashes" in
  let py_serialization = Py.import "cryptography.hazmat.primitives.serialization" in
  let py_sha256 = py_hashes.&("SHA256") [| |] in
  let py_encoding = py_serialization.@$("Encoding") in
  let py_encoding_der = py_encoding.@$("DER") in

  (* Create private key *)
  let priv_key_rsa = Py.Callable.to_function_with_keywords
                       py_rsa_crypto.@$("generate_private_key")
                       [| |]
                       [("public_exponent", Py.Int.of_int 65537); ("key_size", Py.Int.of_int 2048)] in

  (* "Store" the created private and public key in our F* bytes <-> OCaml string mapping *)
  let csr_private_key =
    match acme_csr.acme_csr_pub_key with
    | DY_Crypto.PK priv_key -> priv_key
    | _ -> raise (Invalid_argument "ACME CSR public key is not a PK bytes")
  in
  let priv_key_str = Py.Bytes.to_string (priv_key_rsa.&("private_bytes")
                                           [| py_encoding.@$("PEM");
                                              py_serialization.@$("PrivateFormat").@$("PKCS8");
                                              py_serialization.&("NoEncryption") [| |]
                                           |]) in
  Trace.extend_nonce_string_mapping csr_private_key priv_key_str;
  let pub_key_str = Py.Bytes.to_string ((priv_key_rsa.&("public_key") [| |]).&("public_bytes")
                                          [| py_encoding.@$("PEM");
                                             py_serialization.@$("PublicFormat").@$("SubjectPublicKeyInfo")
                                          |]) in
  Trace.extend_nonce_string_mapping (DY_Crypto.pk csr_private_key) pub_key_str;

  (* Now we can finally build the actual CSR *)
  let builder = py_x509.&("CertificateSigningRequestBuilder") [| |] in
  let py_name_oid = py_oid.&("NameOID") [| |] in

  let identifiers = acme_csr.acme_csr_identifiers |> FstarWrapperUtils.fstar_sequence_to_list |> List.map domain_to_string in

  let identifier_to_name_attr id = py_x509.&("NameAttribute") [| py_name_oid.@$("COMMON_NAME"); Py.String.of_string id |] in
  let name_attributes = List.map identifier_to_name_attr identifiers in
  let name = py_x509.&("Name") [| Py.List.of_list name_attributes |] in
  let builder = builder.&("subject_name") [| name |] in

  let identifier_to_dns_name id = py_x509.&("DNSName") [| Py.String.of_string id |] in
  let dns_names = List.map identifier_to_dns_name identifiers in
  let san = py_x509.&("SubjectAlternativeName") [| Py.List.of_list dns_names |] in
  let builder = builder.&("add_extension") [| san; Py.Bool.f |] in

  (* Create CSR *)
  let csr = builder.&("sign") [| priv_key_rsa; py_sha256 |] in

  (* Encoding *)
  let der_csr = csr.&("public_bytes") [| py_encoding_der |] in
  let base64_der_csr = py_base64.&("urlsafe_b64encode") [| der_csr |] in
  (* Need UTF-8, see RFC 8555, Sec. 5 *)
  let encoded_csr = base64_der_csr.&("decode") [| Py.String.of_string "UTF-8" |] in
  (* String trailing '=', see RFC 8555, Sec. 6.1 (last paragraph) *)
  encoded_csr.&("rstrip") [| Py.String.of_string "=" |]


(** Create the payload for an http request containing the CSR. *)
let create_payload_from_acme_csr (acme_csr:ACME_Data.acme_csr) : Pytypes.pyobject =
  Logs.debug (fun m -> m "Started creating payload for CSR request.");
  let csr = create_payload_from_acme_csr_helper acme_csr in
  let payload = Py.Dict.singleton_string "csr" csr in
  Logs.debug (fun m -> m "Finished creating payload for CSR request.");
  payload



(** This function creates the final payload of the real-world http request. The
   [jws_acme_req_payload] is the DY_Crypto bytes that is contained in the payload of the
   [jws_acme_request] of http requests created by the FStar client code.  *)
let create_final_request_payload jws_acme_req_payload : Pytypes.pyobject =
  let open Helpers in
  (* We basically "try" several ways of decoding the payload DY* bytes to determine which kind of
     request we're dealing with *)
  match
    DY_Crypto.bytes_to_string jws_acme_req_payload,
    ACME_Serialization.parse_acme_csr jws_acme_req_payload,
    ACME_Serialization.parse_acme_order jws_acme_req_payload
  with
  | Success str_payload, _, _ -> Py.Bytes.of_string str_payload
  | _, Success csr, _  -> create_payload_from_acme_csr csr
  | _, _, Success order -> (
    order.acme_order_identifiers
    |> FstarWrapperUtils.fstar_sequence_to_list
    |> List.map (domain_to_string)
    |> List.map Pythonhelpers.create_pyobj_dict_from_domain_string
    |> Pythonhelpers.create_payload_from_identifier_list
  )
  | _, _, _ -> raise (
                   AcmeClientWrapperHelpers.Acme_error (
                       __LOC__,
                       "Could not determine payload type of JWS: " ^ (DY_Crypto.sprint_bytes jws_acme_req_payload)
                 ))


(** Kinds of responses that an ACME client may receive from an ACME server. For answer types with a
   JSON HTTP body, the JSON body is passed with the kind. *)
type response_kind =
  | Order of Pytypes.pyobject
  | Challenge of Pytypes.pyobject
  | Authorization of Pytypes.pyobject
  | OrderNotReady
  | Certificate


(** Given a python object that corresponds to an http response, this function returns the
   payload of a corresponding [Web_Messages.http_response].
@raise AcmeClientWrapperHelpers.Acme_error if anything in the message does not match the expected
   format *)
let get_body_from_resp_helper (response:Pytypes.pyobject) =
  let exc loc = raise (AcmeClientWrapperHelpers.Acme_error (loc, "Could not parse reponse body.")) in
  (* We have to "try" a few things to determine the type of response (i.e., what kind of object is
     contained in this response?). *)
  let kind_of_response =
    try
      let response_json = response.&("json") [| |] in
      let order_not_ready_str = Py.String.of_string "urn:ietf:params:acme:error:orderNotReady" in
      match
        Py.Dict.find_string_opt response_json "authorizations",
        Py.Dict.find_string_opt response_json "token",
        Py.Dict.find_string_opt response_json "challenges",
        Py.Dict.find_string_opt response_json "type"
      with
      | Some _, _, _, _ -> Order response_json
      | _, Some _, _, _ -> Challenge response_json
      | _, _, Some _, _ -> Authorization response_json
      | _, _, _, Some order_not_ready_str  -> OrderNotReady
      | _, _, _, _ -> exc __LOC__
    with Py.E (_, _) -> Certificate
  in
  match kind_of_response with
  | Order response_json ->
     response_json
     |> py_challenge_dict_to_acme_order
     |> ACME_Serialization.serialize_acme_order
  | Authorization response_json ->
     response_json
     |> py_challenge_dict_to_acme_authorization
     |> ACME_Serialization.serialize_acme_authorization
  | Challenge response_json ->
     response_json
     |> py_challenge_dict_to_acme_challenge
     |> ACME_Serialization.serialize_acme_challenge
  | OrderNotReady -> DY_Crypto.string_to_bytes ""
  | Certificate -> (
    let response_body = response.@$("text").&("encode") [| |] in
    let py_x509 = Py.import "cryptography.x509" in
    let py_serialization = Py.import "cryptography.hazmat.primitives.serialization" in
    let py_encoding = py_serialization.@$("Encoding").@$("PEM") in
    let py_pub_format = py_serialization.@$("PublicFormat").@$("SubjectPublicKeyInfo") in
    let py_pem_backed = (Py.import "cryptography.hazmat.backends").&("default_backend") [| |] in
    let py_cert = py_x509.&("load_pem_x509_certificate") [| response_body; py_pem_backed |] in
    let py_issuer = py_cert.@$("issuer").&("rfc4514_string") [| |] in
    let py_pub_key = (py_cert.&("public_key") [| |]).&("public_bytes") [| py_encoding; py_pub_format |] in
    let py_ids = (py_cert.@$("extensions").&("get_extension_for_class") [| py_x509.@$("SubjectAlternativeName") |])
                 .@$("value").&("get_values_for_type") [| py_x509.@$("DNSName") |] in
    let ids = Py.List.to_list_map (fun i -> Root (Py.String.to_string i)) py_ids in
    (* Note that in the following line, we have to "invent" the server's private key (i.e., bytes
       describing that key), because we obviously don't have the actual private key. *)
    let server_priv_key_bytes = DY_Crypto.string_to_bytes ("server_priv_key for: " ^ (Py.String.to_string py_issuer)) in
    let cert_pub_key = Trace.string_to_bytes_exn (Py.Bytes.to_string py_pub_key) in
    let cert_identifiers = FStar_Seq_Base.MkSeq ids in
    let cert_issuer = Root (Py.String.to_string py_issuer) in (* In F*, we use the server domain. *)
    let cert : ACME_Data.acme_certificate = {
        acme_certificate_pub_key = cert_pub_key;
        acme_certificate_issuer = cert_issuer;
        (* The following signature resembles the structure of the signature generated by our DY*
           ACME server implementation - the client does not check this value in any way. But by
           resembling the structure, we can verify that our wrapper code correctly handles all the
           relevant OCaml value <-> DY* bytes mappings. *)
        acme_certificate_signature =
          DY_Crypto.(sign server_priv_key_bytes
                       (concat
                          (concat
                             cert_pub_key
                             (SerializationHelpers.serialize_sequence_of_domains cert_identifiers)
                          )
                          (SerializationHelpers.serialize_domain cert_issuer)));
        acme_certificate_identifiers = cert_identifiers;
      } in
    let acme_cert_bytes = ACME_Serialization.serialize_acme_certificate cert in
    Trace.extend_nonce_string_mapping acme_cert_bytes (Py.Bytes.to_string response_body);
    acme_cert_bytes
  )


(**
  Given a Python object that corresponds to the headers of an http response, this function creates a
  list of headers for a [Web.Messages.http_response]. Currently, this function only considers the
  'Replay-Nonce' and 'Location' headers.
*)
let create_header_for_http_response (headers_mapping:Pytypes.pyobject) =
    let nonce = Py.Object.to_string
                  (Py.Mapping.find_string headers_mapping ("Replay-Nonce")) in
    let nonce_bytes = Trace.string_to_nonce nonce in
    let nonce_header = (DY_Crypto.string_to_bytes "Replay-Nonce", nonce_bytes) in
    (* Get the Location header, if possible *)
    match Py.Mapping.has_key_string headers_mapping "Location" with
    | true -> (
      let py_location = (Py.Mapping.find_string headers_mapping ("Location")) in
      let location = Py.Object.to_string py_location in
      let location_bytes = SerializationHelpers.serialize_url
                            (string_to_url location) in
      let location_header = (DY_Crypto.string_to_bytes "Location", location_bytes) in
      [nonce_header; location_header]
    )
    | false -> (
       [nonce_header]
    )


(** This function sends the [Web_Messages.http_request] to the ACME server, and if possible, returns
   the corresponding [Web_Messages.http_response].
@raise AcmeClientWrapperHelpers.Acme_error if anything in the request or response does not match the
   expected formats *)
let send_request config (domain:string) (http_req:http_request) =
  let http_method = http_method_to_string http_req.req_method in
  let url = create_http_url domain http_req in
   Logs.debug (fun m -> m "send_request(%s %s): %s" http_method url
                         (DY_Crypto.sprint_bytes (SerializationHelpers.serialize_http_request http_req)));
  match ACME_Serialization.parse_jws_acme_request http_req.req_body with
  | Error msg -> raise (AcmeClientWrapperHelpers.Acme_error (__LOC__, "Body is not a jws_acme_request: " ^ msg))
  | Success jws_acme_req -> (
    let jws_acme_req_key_id = jws_acme_req.key_id in
    let jws_acme_req_replay_nonce = jws_acme_req.replay_nonce in
    let jws_acme_req_url = jws_acme_req.url in
    let jws_acme_req_payload = jws_acme_req.payload in
    let kid = http_url_to_string jws_acme_req_key_id in
    let real_nonce = bytes_to_string_exn jws_acme_req_replay_nonce in
    let target_url = http_url_to_string jws_acme_req_url in
    let final_payload = create_final_request_payload jws_acme_req_payload in
    Logs.debug (fun m -> m "JWS Payload from DY* code: '%s'" (DY_Crypto.sprint_bytes jws_acme_req_payload));

    let final_jws_token = AcmeClientWrapperHelpers.create_jws config kid real_nonce target_url final_payload in
    Logs.info (fun m -> m "Sending '%s' request to %s" http_method url);
    let response, real_status = Pythonhelpers.do_http_request
                                  ~data:final_jws_token
                                  ~http_method:http_method
                                  ~headers:[("Content-Type", "application/jose+json")]
                                  url in

    (* create http_response *)
    let status = status_string_to_http_status real_status in
    let headers_dict = response.@$("headers") in
    let header_list = create_header_for_http_response headers_dict in
    let headers = FStar_Seq_Base.MkSeq header_list in
    {
      resp_req_id = http_req.req_id;
      resp_status = status;
      resp_headers = headers;
      resp_body = get_body_from_resp_helper response
    }
  )
