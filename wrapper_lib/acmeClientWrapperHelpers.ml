open Acme
open Log

(** Errors specific to ACME-related code: [(location, message)] *)
exception Acme_error of (string * string)

(* Register a pretty-printer for Acme_error *)
let () =
  Printexc.register_printer
    (function
      | Acme_error (location, msg) -> Some (Printf.sprintf "ACME Error '%s' at: %s" msg location)
      | _ -> None (* for other exceptions *)
    )

(** Retrieves the latest client state, extracts the session specified by [session_id] and parses it
   as an ACME client state.
@raise Acme_error if the session cannot be parsed as a client state
@raise FstarWrapperUtils.Fstar_error if there is no state for the given client *)
let get_client_session_state client session_id trace =
  let last_client_state_fstar = Labeled_ApplicationAPI.get_last_state client trace in
  let _, _, sessions, _ = FstarWrapperUtils.split_fstar_result_dt3 last_client_state_fstar in
  Logs.debug (fun m -> m "#Sessions: %d" (Z.to_int (FStar_Seq_Base.length sessions)));
  let session = FStar_Seq_Base.index sessions session_id in
  match ACME_Data_SerializationHelpers.parse_acme_client_state session with
  | Helpers.Success state -> state
  | Helpers.Error e -> raise (Acme_error (__LOC__, "Could not parse session as client state: " ^ e))


(** Extracts a list of all challenges stored under the given authorization session in the client's
   state. *)
let get_challenges client authz_sessionid trace =
  match get_client_session_state client authz_sessionid trace with
  | ACME_Data.ACMEAuthorziation (authz, _) -> FstarWrapperUtils.fstar_sequence_to_list authz.acme_authorization_challenges
  | _ -> raise (Acme_error (__LOC__, "Given session idx does not point to an authorization session"))


(** Extracts a certificate stored under [cert_session_idx] in the [client]'s state and uses the
   [Trace] module to "translate" the certificate DY* bytes to the "real" certificate. *)
let get_certificate_str client cert_session_idx trace =
  match get_client_session_state client cert_session_idx trace with
  | ACME_Data.ReceivedCertificate (cert, _, _) -> (
    Trace.bytes_to_string_exn (ACME_Data_SerializationHelpers.serialize_acme_certificate cert)
  )
  | _ -> raise (Acme_error (__LOC__, "Given session idx does not point to a certificate session"))


(** Provision challenge responses for all challenges in the specified authorization in a suitable
   way (i.e., such that the ACME server can retrieve them to verify the requested domains).
@raise Not_found if one of the nonces used as tokens are not registered in the trace module
@raise Acme_error if something goes wrong during state parsing *)
let provision_challenge_responses client (config:Config_reader.configuration) authz_sessionid trace =
  let open Pyops in
  let challenges = get_challenges client authz_sessionid trace in
  for challenge_idx = 0 to List.length challenges - 1 do (
    let challenge_object = List.nth challenges challenge_idx in
    let token_str = Trace.bytes_to_string_exn challenge_object.acme_challenge_token in
    let key_verification_str = token_str ^ "." ^ (Py.Object.to_string (config.key.&("thumbprint") [| |])) in
    let test_srv_api_url = "http://challenge-test-srv:8055/add-http01" in
    let authz_provisioned_automatically =
      match Sys.getenv_opt "PROVISION_KEY_AUTHZ_TO_CHALL_TEST_SRV" with
      | Some "true" -> (
        let challenge_str = Printf.sprintf "{\"token\":\"%s\", \"content\":\"%s\"}" token_str key_verification_str in
        let _, status_code = Pythonhelpers.do_http_request
                               ~http_method:"post" test_srv_api_url ~data:(Py.String.of_string challenge_str) in
        status_code = "200"
      )
      | _ -> false
    in
    if authz_provisioned_automatically then (
      Logs.app (fun m -> m "Provisioned key verification '%s' automatically on %s" key_verification_str test_srv_api_url)
    ) else (
      Logs.app (fun m -> m "Please hit enter once you made the key verification below available to the ACME \
                            server that manages the following account: %s" config.key_id);
      Logs.app (fun m -> m "Token: '%s', Content: '%s'  E.g.:" token_str key_verification_str);
      Logs.app (fun m -> m "echo '%s' > '%s'" key_verification_str token_str);
      print_string "Press enter to continue once you provisioned the key verification... ";
      let _ = read_line () in
      ()
    )
  )
  done


(**
 * Create a JWS.
 *
 * The header of the JWS contains, amongst others, the [kid], the
 * [fresh_nonce], and the [target_url]. See also Section 6.2 of RFC
 * 8555.
 *)
let create_jws
  (config:Config_reader.configuration)
  (kid:string)
  (fresh_nonce:string)
  (target_url:string)
  (payload: Pytypes.pyobject)
: Pytypes.pyobject
  =
    Logs.debug (fun m -> m "Starting creation of JWS");
    let open Pyops in
    let authlib = Py.import "authlib.jose" in
    let python_json = Py.import "json" in
    let key = config.key in
    let jsonWebSignature = Py.Callable.to_function_with_keywords
                             authlib.@$("JsonWebSignature")
                             [| |]
                             [("algorithms", Py.List.of_list [Py.String.of_string "RS256"])] in
    let protected_headers = Py.Dict.create () in
    protected_headers.%$["alg"] <- Py.String.of_string "RS256";
    protected_headers.%$["kid"] <- Py.String.of_string kid;
    protected_headers.%$["nonce"] <- Py.String.of_string fresh_nonce;
    protected_headers.%$["url"] <- Py.String.of_string target_url;
    let headers = Py.Dict.singleton_string "protected" protected_headers in
    let token = jsonWebSignature.&("serialize") [| headers; payload; key |] in
    let token = python_json.&("dumps") [| token |] in
    Logs.debug (fun m -> m "Finished creating JWS: %s" (Py.Object.to_string token));
    token
