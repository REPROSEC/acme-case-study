/// ACME.Server (implementation)
/// =================================
module ACME.Server

open FStar.Tactics
open Helpers
open Labeled.Crypto
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Labeled.ApplicationAPI
open Application.Predicates.Helpers
open Application.Predicates
friend Application.Predicates
open Application.Predicates.Lemmas
open ACME.Data
open ACME.Data.SerializationHelpers

open SerializationHelpers
open SerializationLemmas
open ACME.Data.SerializationLemmas

open ACME.Server.HelperFunctions
open ACME.Server.NewNonce
open ACME.Server.NewOrder
open ACME.Server.FinalizeOrder
open ACME.Server.ChallengeResponse
open ACME.Server.TriggerChallengeVerification
open ACME.Server.ReceiveChallengeVerification
open ACME.Server.NewNonce
open ACME.Server.KeyRollover
open FStar.Seq



#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"

let acme_server_new_order server http_request =
    _acme_server_new_order server http_request

let acme_server_new_order_nw server msg_idx =
    let (|now, sender_of_message, message|) = receive_i msg_idx server in
    match parse_http_request message with
    | Error s -> error s
    | Success http_req -> (
      serialize_parse_http_request_publishablity_lemma app_preds now message;
      if(http_request_header_contains_domain_of_server http_req server) then (
        let http_resp = acme_server_new_order server http_req in
        let serialized_http_response = serialize_http_response http_resp in
        let now' = current_trace_len () in
        let send_idx = send #now' server sender_of_message serialized_http_response in
        send_idx
      ) else(
        error "Request was sent to wrong server"
      )
    )


#push-options "--max_fuel 1 --max_ifuel 0"
let acme_server_identifier_authz acme_server_principal request =
  match parse_jws_acme_request request.req_body with
  | Error s -> error s
  | Success jws_acme_request_object -> (
    let trace_index = current_trace_len () in
    concatenation_publishable_implies_components_publishable_forall app_preds;
    serialize_parse_jws_acme_request_publishability_lemma app_preds trace_index request.req_body;
    assert(is_publishable_p app_preds trace_index (serialize_jws_acme_request jws_acme_request_object));
    if (dfst (verify_jws_acme_request trace_index request acme_server_principal jws_acme_request_object)) then
    // Note: This is a POST-as-GET request. The JWS does not contain any payload.
    let (|i, v, current_state|) = get_last_state acme_server_principal in
    (
      match retrieve_authz_by_authorization_url_from_server_st trace_index acme_server_principal jws_acme_request_object.url 0 v current_state with
      | Some (acme_authorization_object, si) ->
        let response:http_response = ({resp_req_id = request.req_id; resp_status = HTTP_STATUS_201_CREATED; resp_headers = Seq.empty; resp_body = serialize_acme_authorization acme_authorization_object}) in
        assert(Authorization? (Success?.v (parse_acme_server_state current_state.[si])));
        assert(acme_authorization_object == Authorization?.authorization (Success?.v (parse_acme_server_state current_state.[si])));
        assert(valid_acme_server_st app_preds trace_index acme_server_principal (Success?.v (parse_acme_server_state current_state.[si])));
        assert(can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_authorization acme_authorization_object) public);
        assert(acme_authorization_is_publishable app_preds trace_index acme_authorization_object);
        assert(acme_authorization_in_http_response_is_publishable app_preds trace_index response);
        http_request_is_publishable_implies_request_id_is_publishable app_preds trace_index request;
        assert(all_elements_of_http_response_are_publishable app_preds trace_index response);
        label_of_http_response_can_flow_to_public app_preds trace_index response;
        response
      | None -> error "Unknown authorization URL"
     )
    else error "Invalid signature on JWS request"
   )
#pop-options


#push-options "--max_fuel 1 --initial_fuel 1 --max_ifuel 0"
let acme_server_identifier_authz_nw server msg_idx =
   let (|now, sender_of_message, message|) = receive_i msg_idx server in
   match parse_http_request message with
   | Error s -> error s
   | Success http_req -> (
     if(http_request_header_contains_domain_of_server http_req server) then (
       assert(is_publishable_p app_preds now message);
       serialize_parse_http_request_publishablity_lemma app_preds now message;
       let http_resp = acme_server_identifier_authz server http_req in
       let now' = current_trace_len () in
       assert(now = now') by set_options "--initial_ifuel 1 --max_ifuel 1";
       let serialized_http_response:msg_at now' public = serialize_http_response http_resp in
       let send_idx = send #now' server sender_of_message serialized_http_response in
       send_idx
     ) else (
       error "Request was sent to wrong server"
     )
   )
#pop-options


(*
Happy path according to p. 53 of RFC8555:
1) We expect an empty (since we only look at HTTP01 and DNS01 challenges) payload of the jws
2) Find a pending authz object which contains a challenge with the target URL (as challenge URL)
3) Update that object (the challenge inside the authz object) with the payload of the jws
   => for HTTP01 and DNS01 challenges, nothing is updated, so the server only changes the status of the
      challenge to "processing" (sec. 7.1.6).
4) Store that updated authz object (overwriting the old one).
5) Answer with HTTP 200 and the updated challenge object
*)
let acme_server_challenge_response acme_server_principal request =
   _acme_server_challenge_response acme_server_principal request


let acme_server_challenge_response_nw server msg_idx =
    let (|now, sender_of_message, message|) = receive_i msg_idx server in
    match parse_http_request message with
    | Error s -> error s
    | Success http_req -> (
      serialize_parse_http_request_publishablity_lemma app_preds now message;
      assert(is_publishable_p app_preds now (serialize_http_request http_req));
      if(http_request_header_contains_domain_of_server http_req server) then (
        let http_resp = acme_server_challenge_response server http_req in
        let now' = current_trace_len () in
        let serialized_http_response:msg_at now' public = serialize_http_response http_resp in
        let send_idx = send #now' server sender_of_message serialized_http_response in
        send_idx
      ) else (
       error "Request was sent to wrong server"
      )
    )


let acme_server_trigger_challenge_verification server =
   _acme_server_trigger_challenge_verification server


#push-options "--max_ifuel 1 --initial_ifuel 1"
let acme_server_trigger_challenge_verification_nw server =
  let http_req = acme_server_trigger_challenge_verification server in
  match get_domain_from_request http_req with 
  | Error s -> error s
  | Success receiver_domain -> (
    let now = current_trace_len () in
    let receiver = domain_principal_mapping receiver_domain in
    let serialized_http_req = serialize_http_request http_req in
    let send_idx = send #now server receiver serialized_http_req in
    send_idx
  )
#pop-options


let acme_server_receive_challenge_verification server response sender_of_resp send_ev_idx =
   _acme_server_receive_challenge_verification server response sender_of_resp send_ev_idx


let acme_server_receive_challenge_verification_nw server msg_idx =
  let (|now, sender_of_message, message|) = authenticated_receive_i msg_idx server in
  assert(is_publishable_p app_preds now message);
  assert(is_publishable_p app_preds msg_idx message);
  print_string "acme_server_receive_challenge_verification_nw 1\n";
  match parse_http_response message with
  | Error _ -> ()
  | Success http_resp ->
    print_string "acme_server_receive_challenge_verification_nw 2\n";
    serialize_parse_http_response_publishablity_lemma app_preds msg_idx message;
    assert(is_publishable_p app_preds msg_idx (serialize_http_response http_resp));
    serialize_parse_http_response_publishablity_lemma app_preds now message;
    assert(is_publishable_p app_preds now (serialize_http_response http_resp));
    acme_server_receive_challenge_verification server http_resp sender_of_message msg_idx


let acme_server_finalize_order acme_server_principal request =
   let trace_index = current_trace_len () in
   http_request_publishable_implies_payload_of_jws_publishable app_preds trace_index request;
   assert(payload_of_jws_in_http_request_is_publishable app_preds trace_index request);
   print_string "------serialized csr http request: \n";
   print_bytes (serialize_http_request request);
   print_string "\n----\n";
   _acme_server_finalize_order acme_server_principal request


let acme_server_finalize_order_nw server msg_idx =
  let (|now, sender_of_message, message|) = receive_i msg_idx server in
  print_string "got csr request\n";
  match parse_http_request message with
  | Error s -> error s
  | Success http_req -> (
    print_string "parse http request sucess\n";
    if(http_request_header_contains_domain_of_server http_req server) then (
      print_string "if containing domain sucess\n";
      print_string "------received csr http request bytes: \n";
      print_bytes message;
      print_string "\n----\n";
      serialize_parse_http_request_publishablity_lemma app_preds now message;
      assert(is_publishable_p app_preds now (serialize_http_request http_req));
      http_request_publishable_implies_payload_of_jws_publishable app_preds now http_req;
      assert(payload_of_jws_in_http_request_is_publishable app_preds now http_req);
      let http_resp = acme_server_finalize_order server http_req in
      let now = current_trace_len () in
      print_string "functional work done\n";
      let serialized_http_response:msg_at now public = serialize_http_response http_resp in
      let send_idx = send #now server sender_of_message serialized_http_response in
      send_idx
    ) else (
      error "Request was sent to wrong server"
    )
  )


(**
  Search for an acme_certificate with the given certificate_url in server's state and return it if
  found, together with the session index at which the certificate is stored
*)
val retrieve_cert_from_server_st:
  trace_index:nat ->
  server:principal ->
  cert_url:url ->
  session_index:nat ->
  current_version_vec:version_vec ->
  current_app_state:app_state trace_index server current_version_vec ->
  Tot (opt_result:option (nat * acme_certificate){
        //the certificate is stored at the returned session index:
        Some? opt_result ==> (
          let si = fst (Some?.v opt_result) in
          let cert = snd (Some?.v opt_result) in
          si < Seq.length current_app_state /\
          (match parse_acme_server_state current_app_state.[si] with
            | Success (Certificate _ cert' _ _) -> cert' == cert
            |_ -> False
      ))})
      (decreases (Seq.length current_version_vec - session_index))

#push-options "--max_ifuel 8 --max_fuel 8"
let rec retrieve_cert_from_server_st trace_index server cert_url session_index current_version_vec current_app_state =
      if Seq.length current_version_vec <= session_index then
        None
      else
        match parse_acme_server_state current_app_state.[session_index] with
        | Success (Certificate _ cert cert_url_in_state _) -> (
            if eq_url cert_url cert_url_in_state then
              Some (session_index, cert)
            else
              retrieve_cert_from_server_st trace_index server cert_url (session_index + 1) current_version_vec current_app_state
          )
        | _ -> retrieve_cert_from_server_st trace_index server cert_url (session_index + 1) current_version_vec current_app_state
#pop-options


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 1"
let acme_server_retrieve_cert acme_server_principal request =
  let now = current_trace_len () in
  match parse_jws_acme_request request.req_body with
  | Error s -> error s
  | Success jws_acme_request_object -> (
      concatenation_publishable_implies_components_publishable_forall app_preds;
      serialize_parse_jws_acme_request_publishability_lemma app_preds now request.req_body;
      assert(is_publishable_p app_preds now (serialize_jws_acme_request jws_acme_request_object));
      if (dfst (verify_jws_acme_request now request acme_server_principal jws_acme_request_object)) then (
        let cert_url = jws_acme_request_object.url in
        let (|i, v, current_state|) = get_last_state acme_server_principal in
        // Find the cert in state
        match retrieve_cert_from_server_st now acme_server_principal cert_url 0 v current_state with
        | None -> error "Unknown certificate URL"
        | Some (cert_sess_idx, cert) -> (
          // Answer with the cert as HTTP response
          let response:http_response = {
            resp_req_id = request.req_id;
            resp_status = HTTP_STATUS_200_OK;
            resp_headers = Seq.empty; 
            resp_body = serialize_acme_certificate cert
          } in
          assert(certificate_of_http_response_is_publishable app_preds now response);
          http_request_is_publishable_implies_request_id_is_publishable app_preds now request;
          assert(is_publishable_p app_preds now request.req_id);
          assert(is_publishable_p app_preds now (serialize_sequence_of_bytes_tuples response.resp_headers));
          assert(is_publishable_p app_preds now response.resp_body);
          assert(all_elements_of_http_response_are_publishable app_preds now response);
          label_of_http_response_can_flow_to_public app_preds now response;
          response
        )
      ) else error "Invalid signature on JWS request"
    )
#pop-options


let acme_server_retrieve_cert_nw server msg_idx =
  let (|now, sender_of_message, message|) = receive_i msg_idx server in
  match parse_http_request message with
  | Error s -> error s
  | Success http_req -> (
    if(http_request_header_contains_domain_of_server http_req server) then (
      serialize_parse_http_request_publishablity_lemma app_preds now message;
      let http_resp = acme_server_retrieve_cert server http_req in
      let serialized_http_response:msg_at now public = serialize_http_response http_resp in
      let now' = current_trace_len () in
      assert(now' >= now);
      let send_idx = send #now server sender_of_message serialized_http_response in
      send_idx
    ) else (
       error "Request was sent to wrong server"
    )
    )

let acme_server_receive_challenge_verification_nw_faulty server msg_idx =
  let (|now, sender_of_message, message|) = authenticated_receive_i msg_idx server in
  assert(is_publishable_p app_preds now message);
  assert(is_publishable_p app_preds msg_idx message);
  print_string "acme_server_receive_challenge_verification_nw 1\n";
  match parse_http_response message with
  | Error _ -> ()
  | Success http_resp ->
    print_string "acme_server_receive_challenge_verification_nw 2\n";
    serialize_parse_http_response_publishablity_lemma app_preds msg_idx message;
    assert(is_publishable_p app_preds msg_idx (serialize_http_response http_resp));
    serialize_parse_http_response_publishablity_lemma app_preds now message;
    assert(is_publishable_p app_preds now (serialize_http_response http_resp));
    _acme_server_receive_challenge_verification_faulty server http_resp sender_of_message msg_idx

let acme_server_new_nonce server request =
  _acme_server_new_nonce server request

let acme_server_new_nonce_nw server msg_idx =
  let (|now, sender_of_message, message|) = receive_i msg_idx server in
  match parse_http_request message with
  | Error s -> error s
  | Success request -> (
    if  request.req_method = HTTP_METHOD_HEAD &&
        eq_path
          request.req_uri.uri_path
          (init_seq_bytes_with_list [string_to_bytes "acme"; string_to_bytes "new-nonce"]) 
    then (
      serialize_parse_http_request_publishablity_lemma app_preds now message;
      let http_resp = acme_server_new_nonce server request in 
      let now = current_trace_len () in
      let serialized_http_response:msg_at now public = serialize_http_response http_resp in
      let send_idx = send #now server sender_of_message serialized_http_response in
      send_idx
    ) else (
       error "Wrong request for replay nonce"
    )
  )


let acme_server_update_account_key server http_req = _acme_server_update_account_key server http_req


let acme_server_update_account_key_nw server msg_idx =
    let (|now, sender_of_message, message|) = receive_i msg_idx server in
    match parse_http_request message with
    | Error s -> error s
    | Success http_req -> (
      serialize_parse_http_request_publishablity_lemma app_preds now message;
      if(http_request_header_contains_domain_of_server http_req server) then (
        let http_resp = acme_server_update_account_key server http_req in
        let serialized_http_response = serialize_http_response http_resp in
        let now' = current_trace_len () in
        let send_idx = send #now' server sender_of_message serialized_http_response in
        send_idx
      ) else(
        error "Request was sent to wrong server"
      )
    )
