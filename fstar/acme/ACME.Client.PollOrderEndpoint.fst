/// ACME.Client.PollOrderEndpoint (implementation)
/// =================================================

module ACME.Client.PollOrderEndpoint

open Helpers
open DY.Monad
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.Labels
open DY.Entry
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
open FStar.String
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open ACME.Client.HelperLemmas
open ACME.Client.HelperFunctions

#set-options "--max_fuel 4 --max_ifuel 4 --z3rlimit 150"

(**
  Helper function creating parts of the request for [acme_client_poll_order_endpoint].
*)
val _acme_client_poll_order_endpoint_helper:
  client:principal ->
  order_url:url->
  account_sess_idx:nat  ->
  DYL (
    request_nonce: bytes *
    request_body:bytes *
    authz_dom: domain *
    req_uri: request_uri *
    replay_nonce: bytes
  )
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_url order_url))
  (ensures fun h0 (request_nonce, request_body, authz_dom, req_uri, _) h1 ->
     later (trace_len h0) (trace_len h1) /\
     is_publishable_p app_preds (trace_len h1) request_nonce /\
     is_publishable_p app_preds (trace_len h1) request_body /\
     is_publishable_p app_preds (trace_len h1) (serialize_request_uri req_uri)
  )


let  _acme_client_poll_order_endpoint_helper client order_url idx_account =
  let (|idx, req_nonce|) = guid_gen () in
  let (|i, v, state|) = get_last_state client in
  if idx_account < Seq.length state then (
    let ss_acc_st = state.[idx_account] in
    match parse_acme_client_state ss_acc_st with
    | Success (Account acc_priv_key acc_url _) -> (
       let cert_dom = order_url.url_domain in
       match client_finds_valid_replay_nonce i client v state cert_dom with
       |Success replay_nonce -> (
          let payload = string_to_bytes app_preds i "" in
          assert(is_sign_key_p app_preds i acc_priv_key
            (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));
          generate_message_for_jws_signature_structure app_preds acc_url order_url replay_nonce payload;
          assert(
            match DY.Crypto.split (generate_message_for_jws_signature acc_url order_url replay_nonce payload) with
            | Success (nonce_bytes, snd_part) -> (
              match  DY.Crypto.split snd_part with
            | Success (keyID_bytes, snd_part) -> (
              match DY.Crypto.split snd_part with
              | Success (url_bytes, payload_bytes) -> (
                match parse_acme_csr payload_bytes with
                | Success csr ->  False
                | _ -> True) //other signing cases
              | _ -> False)
            | _ -> False)
            | _ -> False
          );
          assert(acme_sign_pred  (readers [any client]) app_preds i
            (generate_message_for_jws_signature acc_url order_url replay_nonce payload));
          let jws_req = generate_jws_acme_request app_preds i
            (acme_sig_key_usage (readers [any client]) app_preds)
            acc_url order_url replay_nonce payload acc_priv_key
            (readable_by (readers [any client])) in
          elements_of_jws_acme_request_are_publishable_implies_jws_request_is_publishable
            app_preds i acc_url order_url replay_nonce payload acc_priv_key (readers [any client]);
          let req_body = serialize_jws_acme_request jws_req in
          assert(is_publishable_p app_preds i req_body);
          assert(later idx i);
          assert(is_publishable_p app_preds i req_nonce);
          url_is_publishable_implies_request_uri_is_publishable app_preds i order_url;
          assert(is_publishable_p app_preds i (serialize_request_uri order_url.url_request_uri));
          (req_nonce, req_body, cert_dom,  order_url.url_request_uri, replay_nonce)
        )
       | _ -> error "there is no replay nonce to send request"
    )
    | _ -> error "failed to create polling request for order endpoint: cannot parse client state"
  ) else error "failed to create polling request for order endpoint: wrong account index"


let _acme_client_poll_order_endpoint_with_csr_idx client order_url idx_csr idx_account =
  let len_begin = current_trace_len () in
  let (req_nonce, request_body, order_dom,  order_url_uri, replay_nonce) =
    _acme_client_poll_order_endpoint_helper client order_url idx_account in
  let (|i, v, state|) = get_last_state client in

  if idx_csr < Seq.length state then (
    match parse_acme_client_state state.[idx_csr] with
    |Success (CSR _ _ _ _) -> (
      assert(later len_begin i);
      assert(is_publishable_p app_preds i (serialize_url order_url));
      let pen_req_ss = HTTPSPendingRequest req_nonce idx_csr order_dom in
      let v_req_ss = Seq.snoc v 0 in
      let st_pen_req = Seq.snoc state (serialize_acme_client_state pen_req_ss) in
      flows_to_public_can_flow (app_preds.model.corrupt_at i) (get_label req_nonce) (readable_by (readers [any client]));
      add_valid_client_session_state_preserves_state_inv i client v state pen_req_ss;
      set_state client v_req_ss st_pen_req;
      let len_now = current_trace_len () in
      assert(later i len_now);
      let order_uri:request_uri = order_url.url_request_uri in
      assert(can_label_of_bytes_flow_to app_preds i (serialize_url order_url) public);
      assert(can_label_of_bytes_flow_to app_preds len_now (serialize_url order_url) public);
      url_is_publishable_implies_request_uri_is_publishable app_preds len_now order_url;
      let req_header = generate_request_header_host_domain order_dom in
      request_header_host_domain_is_publishable len_now order_dom;
      let request:http_request = {
        req_id = req_nonce;
        req_method = HTTP_METHOD_POST;
        req_uri = order_uri;
        req_headers = req_header;
        req_body = request_body
      } in
      assert(can_label_of_bytes_flow_to app_preds i  req_nonce public);
      can_label_of_bytes_flow_later app_preds i len_now req_nonce public;
      assert(can_label_of_bytes_flow_to app_preds i req_nonce public);
      can_label_of_bytes_flow_later app_preds i len_now req_nonce public;
      assert(can_label_of_bytes_flow_to app_preds len_now req_nonce public);
      assert(can_label_of_bytes_flow_to app_preds i request.req_body public);
      can_label_of_bytes_flow_later app_preds i len_now request.req_body public;
      assert(can_label_of_bytes_flow_to app_preds len_now request.req_body public);
      assert(all_elements_of_http_request_are_publishable app_preds len_now request);
      let server = domain_principal_mapping order_dom in
      (request, server, replay_nonce)
    )
    | _ -> error "cannot parse client state at csr index"
  ) else  error "invalid csr index"


let _acme_client_poll_order_endpoint client order_sessionid =
  let (|i, v, state|) = get_last_state client in
  if order_sessionid < Seq.length state then (
    match parse_acme_client_state state.[order_sessionid] with
    | Success (ACMEOrder _ acc_sid opt_order_url) -> (
      match opt_order_url with
      | Some order_url -> (
      if acc_sid < Seq.length state then (
          match parse_acme_client_state state.[acc_sid] with
          | Success (Account private_acc_key _ _) -> (
            let (req_nonce, request_body, order_dom,  order_url_uri, replay_nonce) =
              _acme_client_poll_order_endpoint_helper client order_url acc_sid in
             let len_now1 = current_trace_len () in
             assert(can_label_of_bytes_flow_to app_preds len_now1  req_nonce public);
             let order_uri:request_uri = order_url.url_request_uri in
             let len_now = current_trace_len () in
             assert(can_label_of_bytes_flow_to app_preds i (serialize_url order_url) public);
             assert(can_label_of_bytes_flow_to app_preds len_now (serialize_url order_url) public);
             url_is_publishable_implies_request_uri_is_publishable app_preds len_now order_url;
             let req_header = generate_request_header_host_domain order_dom in
             request_header_host_domain_is_publishable len_now order_dom;
             let request:http_request = {
               req_id = req_nonce;
               req_method = HTTP_METHOD_POST;
               req_uri = order_uri;
               req_headers = req_header;
               req_body = request_body
             } in
             assert(later len_now len_now1);
             flows_to_public_can_flow (app_preds.model.corrupt_at i) (get_label req_nonce) (readable_by (readers [any client]));
             assert(can_label_of_bytes_flow_to app_preds len_now  req_nonce public);
             can_label_of_bytes_flow_later app_preds len_now len_now req_nonce public;
             assert(can_label_of_bytes_flow_to app_preds len_now req_nonce public);
             can_label_of_bytes_flow_later app_preds i len_now req_nonce public;
             assert(can_label_of_bytes_flow_to app_preds len_now req_nonce public);
             can_label_of_bytes_flow_later app_preds i len_now request.req_body public;
             assert(can_label_of_bytes_flow_to app_preds len_now request.req_body public);
             assert(all_elements_of_http_request_are_publishable app_preds len_now request);
             let server = domain_principal_mapping order_dom in
             (request, server, replay_nonce)
          )
         | _ -> error "Client state is not an Account session."
      ) else  error "Account index retrieved from ACMEOrder session is not valid."
      )
      | None -> error "Cannot create polling request due to missing order url in client state."
    )
    | _ -> error "Client state is not an ACMEOrder session."
  ) else  error "Session index of order is not valid."
