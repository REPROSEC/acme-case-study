/// ACME.Client (implementation)
/// ============================
module ACME.Client

open Helpers
open DY.Monad
open DY.Entry
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.Labels
open Labeled.ApplicationAPI
open Labeled.Crypto
open Web.Messages
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open Application.Predicates
friend Application.Predicates
open FStar.Seq.Base

open SerializationHelpers
open SerializationLemmas
open FStar.String
open ACME.Client.OrderCertificate
open ACME.Client.AskChallenge
open ACME.Client.TriggerChallenge
open ACME.Client.ChallengeResponse
open ACME.Client.SendCSR
open ACME.Client.RetrieveCertificate
open ACME.Client.HelperFunctions
open ACME.Client.ReceiveMessage
open ACME.Client.SaveCertificate
open ACME.Client.HelperFunctions
open ACME.Data.Predicates
open ACME.Client.RequestNonce
open ACME.Client.GetNonce
open ACME.Client.PollOrderEndpoint

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"
let acme_client_orders_certificate_http client doms idx_account =
  let (|server, req, replay_nonce|) = _acme_client_orders_certificate_save_state client doms idx_account in
    let len_now = current_trace_len () in
    label_of_http_request_can_flow_to_public app_preds len_now req;
    (|server, req, replay_nonce|)



#push-options "--z3rlimit 100 --max_fuel 4 --max_ifuel 0"
let acme_client_orders_certificate_nw client doms idx_account =
    let (|server, req, replay_nonce|) = acme_client_orders_certificate_http client doms idx_account in
    let len_now = current_trace_len () in
    assert(is_publishable_p app_preds len_now (serialize_http_request req));
    let out_msg = serialize_http_request req in
    assert(is_publishable_p app_preds len_now out_msg);
    let out_msg':msg_at len_now public = out_msg in
    let opt_send_idx = send client server out_msg' in
    //deactivate the nonce
    client_deactivates_replay_nonce client replay_nonce;
    opt_send_idx
#pop-options



(*acme.md #3*)

let acme_client_receive_order_response_http client http_resp =
  let len_now = current_trace_len () in
  let (|i, current_version_vec, current_state|) = get_last_state client in

  (*
    If the response contains a Location header (which is the url for the current acme order), the
    client saves its value.
  *)
  let opt_location_header_url = find_location_header_url_in_http_response_option len_now http_resp in
  assert(can_label_of_bytes_flow_to app_preds len_now (serialize_opt_url opt_location_header_url ) public);

  match acme_client_returns_replay_nonce_and_server_domain_for_response i http_resp current_state with
  |Success (replay_nonce, serv_dom) ->(
      let _ = _acme_client_get_nonce_save_state client replay_nonce serv_dom in
      let (|i, current_version_vec, current_state|) = get_last_state client in
      match acme_client_receives_response_for_new_order i http_resp current_state with
      |Success (updated_order, order_sess_idx) ->
      _acme_client_receive_order_response_save_state client updated_order order_sess_idx opt_location_header_url
      | _ -> error "fail to receive order response"
    )
  |_ ->(
       match acme_client_receives_response_for_new_order i http_resp current_state with
       |Success (updated_order, order_sess_idx) ->
         _acme_client_receive_order_response_save_state client updated_order order_sess_idx opt_location_header_url
       | _ -> error "fail to receive order response"
    )


let acme_client_receive_order_response_nw client msg_idx =
  let resp = receive_http_response client msg_idx in
  acme_client_receive_order_response_http client resp


let acme_client_send_authorization_request_i_http client idx_order authz_url_idx =
  let (req, server, replay_nonce) =  _acme_client_asks_for_authorization_save_state client idx_order authz_url_idx in
  let len_now = current_trace_len () in
  label_of_http_request_can_flow_to_public app_preds len_now req;
  (req, server, replay_nonce)


let acme_client_send_authorization_request_i_nw client idx_order authz_url_idx =
   let (req, server, replay_nonce) =  acme_client_send_authorization_request_i_http client idx_order authz_url_idx in
   let len_now = current_trace_len () in
    assert(is_publishable_p app_preds len_now (serialize_http_request req));
    let out_msg = serialize_http_request req in
    assert(is_publishable_p app_preds len_now out_msg);
    let out_msg':msg_at len_now public = out_msg in
    let opt_send_idx = send client server out_msg' in
    //deactivate the nonce
    client_deactivates_replay_nonce client replay_nonce;
    opt_send_idx



let acme_client_receive_authorization_response_http client http_resp =
    let (|i, current_version_vec, current_state|) = get_last_state client in
    match acme_client_returns_replay_nonce_and_server_domain_for_response i http_resp current_state with
    |Success (replay_nonce, serv_dom) ->(
      let _ = _acme_client_get_nonce_save_state client replay_nonce serv_dom in
      let (|i, current_version_vec, current_state|) = get_last_state client in
      match acme_client_receives_response_for_asking_challenge i  http_resp current_state with
      |Success (authorization, order_sess_idx) ->
               _acme_client_receive_authorization_save_state client authorization  order_sess_idx
      | _ -> error "fail to receive authorization response"
     )
     |_ -> (
       match acme_client_receives_response_for_asking_challenge i  http_resp current_state with
      |Success (authorization, order_sess_idx) ->
               _acme_client_receive_authorization_save_state client authorization  order_sess_idx
      | _ -> error "fail to receive authorization response"
     )
      


let acme_client_receive_authorization_response_nw client msg_idx =
   let resp = receive_http_response client msg_idx in
   acme_client_receive_authorization_response_http client resp


let acme_client_triggers_challenge_i_http client idx_authz challenge_idx =
   let (req, server, replay_nonce) = _acme_client_triggers_challenge_i client idx_authz challenge_idx in
   let len_now = current_trace_len () in
   label_of_http_request_can_flow_to_public app_preds len_now req;
   (req, server, replay_nonce)


let acme_client_triggers_challenge_i_nw client idx_authz challenge_idx =
    let (req, server, replay_nonce) = acme_client_triggers_challenge_i_http client idx_authz challenge_idx in
    let len_now = current_trace_len () in
    assert(is_publishable_p app_preds len_now (serialize_http_request req));
    let out_msg = serialize_http_request req in
    assert(is_publishable_p app_preds len_now out_msg);
    let out_msg':msg_at len_now public = out_msg in
    let opt_send_idx = send client server out_msg' in
     //deactivate the nonce
    client_deactivates_replay_nonce client replay_nonce;
    opt_send_idx


(*acme.md #8*)
#push-options "--z3rlimit 100 --max_fuel 4 --max_ifuel 0"
let acme_client_challenge_response_http client http_req =
    let (|i, current_version_vec, current_state|) = get_last_state client in
    match acme_client_receives_challenge_request i client http_req  current_state with
    |Success (idx_acc, idx_authz, request_id) ->
         let resp =  _acme_client_challenge_response client idx_acc idx_authz request_id in
         let len_now = current_trace_len () in
         label_of_http_response_can_flow_to_public app_preds len_now resp;
         (resp, len_now)
    | _ -> error "Could not extract challenge information from client state"



let acme_client_challenge_response_nw client msg_idx =
    let  (req, server) = receive_http_request client msg_idx in
    let (resp, send_idx) = acme_client_challenge_response_http client req in
    let len_now = current_trace_len () in
       let out_msg = serialize_http_response resp in
       assert(is_publishable_p app_preds len_now out_msg);
       let out_msg':msg_at len_now public = out_msg in
       assert(authenticated_send_pred len_now client server out_msg');
       authenticated_send client server out_msg' //client need to response the challenge using authenticated channel




(*acme.md #9*)
//#push-options "--z3rlimit 500 --max_fuel 8 --max_ifuel 4"
let acme_client_sends_CSR_http  client idx_order  =
  let (idx_csr, cert_priv_key, order, acc_priv_key, acc_url, finalize_url, replay_nonce, payload) = _acme_client_add_valid_CSR_session client idx_order in
  let (req, server, replay_nonce) =  _acme_client_send_CSR_save_state client idx_csr cert_priv_key order acc_priv_key acc_url finalize_url replay_nonce payload in
  let len_now = current_trace_len () in
  label_of_http_request_can_flow_to_public app_preds len_now req;
  (req, server, replay_nonce)



//#pop-options


let acme_client_sends_CSR_nw client idx_order  =
    let (req, server, replay_nonce) = acme_client_sends_CSR_http  client idx_order in
    let len_now = current_trace_len () in
    assert(is_publishable_p app_preds len_now (serialize_http_request req));
    let out_msg = serialize_http_request req in
    assert(is_publishable_p app_preds len_now out_msg);
    let out_msg':msg_at len_now public = out_msg in
    let opt_send_idx = send client server out_msg' in
    //deactivate the nonce
    client_deactivates_replay_nonce client replay_nonce;
    opt_send_idx


(*acme.md #11*)
#push-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2"
let acme_client_retrieves_certificate_http client http_resp =
  let  (|i, current_version_vec, current_state|) =  get_last_state client in
  match acme_client_returns_replay_nonce_and_server_domain_for_response i http_resp current_state with
  | Success (replay_nonce, serv_dom) -> (
    let _ = _acme_client_get_nonce_save_state client replay_nonce serv_dom in
    let (|i, current_version_vec, current_state|) = get_last_state client in
    match acme_client_receives_finalize_order i  http_resp  current_state with
    | Success (csr_idx, account_sess_idx, opt_cert_url, opt_location_header_url) -> (
      match opt_cert_url with
      | None -> (
        (* The updated order has no certificate url. Send a request to the order endpoint for
        getting an updated order object. *)
        match opt_location_header_url with
        (* The client implementation requires the status of the updated order to be [Valid] or [Processing]. *)
        | None -> error "Response to finalize url has no certificate url and no location header"
        | Some location_header_url -> (
          let (req, server, replay_nonce) =  _acme_client_poll_order_endpoint_with_csr_idx client location_header_url csr_idx account_sess_idx in
          let len_now = current_trace_len () in
          label_of_http_request_can_flow_to_public app_preds len_now req;
          (req, server, replay_nonce, true)
        )
      )
      | Some cert_url -> (
        (* The updated order has a certificate url. Send a request to this url to receive the certificate. *)
        let (req, server, replay_nonce) =  _acme_client_retrieves_certificate_save_state client  cert_url csr_idx account_sess_idx in
        let len_now = current_trace_len () in
        label_of_http_request_can_flow_to_public app_preds len_now req;
        (req, server, replay_nonce, false)
      )
   )
   | Error e -> error ("failed to create request in [acme_client_retrieves_certificate_http]: " ^ e)
  )
  | _ -> (
    match acme_client_receives_finalize_order i  http_resp  current_state with
    |Success (csr_idx, account_sess_idx, opt_cert_url, opt_location_header_url) -> (
      match opt_cert_url with
      | None -> (
        (* The updated order has no certificate url. Send a request to the order endpoint for
        getting an updated order object. *)
        match opt_location_header_url with
        (* The client implementation requires the status of the updated order to be [Valid] or [Processing]. *)
        | None -> error "Response to finalize url has no certificate url and no location header"
        | Some location_header_url -> (
          let (req, server, replay_nonce) =  _acme_client_poll_order_endpoint_with_csr_idx client location_header_url csr_idx account_sess_idx in
          let len_now = current_trace_len () in
          label_of_http_request_can_flow_to_public app_preds len_now req;
          (req, server, replay_nonce, true)
        )
      )
      | Some cert_url -> (
        let (req, server, replay_nonce) =  _acme_client_retrieves_certificate_save_state client  cert_url csr_idx  account_sess_idx in
        let len_now = current_trace_len () in
        label_of_http_request_can_flow_to_public app_preds len_now req;
        (req, server, replay_nonce, false)
      )
    )
    | Error e -> error ("failed to create request in [acme_client_retrieves_certificate_http]: " ^ e)
  )
#pop-options


let acme_client_retrieves_certificate_nw client msg_idx =
   let resp = receive_http_response client msg_idx in
   let (req, server, replay_nonce, polling_flag) = acme_client_retrieves_certificate_http client resp in
   let len_now = current_trace_len () in
    assert(is_publishable_p app_preds len_now (serialize_http_request req));
    let out_msg = serialize_http_request req in
    assert(is_publishable_p app_preds len_now out_msg);
    let out_msg':msg_at len_now public = out_msg in
    let opt_send_idx = send client server out_msg' in
     //deactivate the nonce
    (opt_send_idx, polling_flag)




let acme_client_receives_and_saves_certificate client http_resp =
    let (|i, current_version_vec, current_state|) = get_last_state client in
    match acme_client_receives_certificate i http_resp current_state with
    | Success (certificate, retrieve_cert_sessionid) ->
        let opt_set_state_sess_idx = _acme_client_save_certificate client certificate retrieve_cert_sessionid in
        opt_set_state_sess_idx
    | _ -> error "fail to receive and save certificate"


let acme_client_receives_and_saves_certificate_nw client msg_idx =
   let resp = receive_http_response client msg_idx in
   let len_now = current_trace_len () in
    http_response_is_publishable_implies_certificate_of_http_response_is_publishable app_preds len_now resp;
    acme_client_receives_and_saves_certificate client resp



let acme_client_request_replay_nonce_nw client newNonce_url =
  let (server, req) = _acme_client_request_replay_nonce_save_state client newNonce_url in
  let out_msg = serialize_http_request req in
  let len_now = current_trace_len () in
  label_of_http_request_can_flow_to_public app_preds len_now req;
  assert(is_publishable_p app_preds len_now out_msg);
  let out_msg':msg_at len_now public = out_msg in
  let opt_send_idx = send client server out_msg' in
  opt_send_idx

#push-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"
let acme_client_receives_and_saves_replay_nonce_nw client msg_idx =
   let resp = receive_http_response client msg_idx in
   let (|i, current_version_vec, current_state|) = get_last_state client in
   match acme_client_returns_replay_nonce_and_server_domain_for_response i resp  current_state with
   | Success (replay_nonce, server_dom) ->  _acme_client_get_nonce_save_state client replay_nonce server_dom
   | Success _ -> error "fail to receive and save replay nonce (1)"
   | Error e -> error ("fail to receive and save replay nonce (2): " ^ e)
#pop-options


#push-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2"
let acme_client_poll_order_create_http_request  client order_sessionid =
  _acme_client_poll_order_endpoint client order_sessionid
#pop-options


#push-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2"
let acme_client_polling_response_is_ready client http_resp =
  let {resp_req_id; resp_status; resp_headers; resp_body} = http_resp in
  match parse_acme_order resp_body with
  | Success order -> (
    if(order.acme_order_status = Some Ready) then true
    else false
  )
  | _ -> error "cannot parse acme order from polling response"
#pop-options


let acme_client_poll_at_order_endpoint client http_resp =
  let {resp_req_id; resp_status; resp_headers; resp_body} = http_resp in
  match resp_status with
  | HTTP_STATUS_403_FORBIDDEN -> true
  | _ -> false
