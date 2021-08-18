/// ACME.Client.RequestNonce (implementation)
/// =============================================

module ACME.Client.RequestNonce

open Application.Predicates.Helpers
friend Application.Predicates
open Application.Predicates.Lemmas
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Client.HelperLemmas
open ACME.Data.SerializationLemmas



#push-options "--z3rlimit 50 --max_fuel 4 --max_ifuel 2"
let _acme_client_request_replay_nonce_save_state client newNonce_url =
  let (|idx, req_nonce|) = guid_gen () in
  let (|i, v, state|) = get_last_state client in
  let serv_dom = newNonce_url.url_domain in
  let server = domain_principal_mapping serv_dom in
    
  let pen_req_ss = HTTPSPendingRequest req_nonce (Seq.length v) serv_dom in //the reference points to the session ReplayNonceRequest
  let v_req_ss = Seq.snoc v 0 in 
  let st_pen_req = Seq.snoc state (serialize_acme_client_state pen_req_ss) in
  add_valid_client_session_state_preserves_state_inv i client v state pen_req_ss;
  set_state client v_req_ss st_pen_req;
  let request:http_request ={
     req_id = req_nonce;
     req_method = HTTP_METHOD_HEAD;
     req_uri = newNonce_url.url_request_uri;
     req_headers = Seq.empty;
     req_body = string_to_bytes ""
  } in
  let len_now = current_trace_len () in  
  url_is_publishable_implies_request_uri_is_publishable app_preds len_now newNonce_url;
  (server, request)
