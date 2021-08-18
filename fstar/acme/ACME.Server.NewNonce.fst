/// ACME.Server.NewNonce (implementation)
/// ======================================
module ACME.Server.NewNonce


open Helpers
open DY.Monad
open DY.Labels
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
open Application.Predicates.Helpers
open FStar.Seq

#push-options "--z3rlimit 100 --max_fuel 4 --max_ifuel 1"
let _acme_server_new_nonce acme_server_principal request =
  let (|i, fresh_nonce|) = guid_gen () in
  let len1 = current_trace_len () in
  let (|len_now, version_vec, last_state |) = get_last_state acme_server_principal in
    assert(state_inv len_now acme_server_principal version_vec last_state);
    let version_vec' = Seq.snoc version_vec 0 in
    let new_acme_server_state_element = IssuedValidNonce fresh_nonce in
    assert(later len1 len_now);
    //is_publishable_p_later_lemma app_preds len1 fresh_nonce;
    assert(valid_acme_server_st app_preds len_now acme_server_principal new_acme_server_state_element);
    let serialized_state_element = serialize_acme_server_state new_acme_server_state_element in
    let new_state = Seq.snoc last_state serialized_state_element in
    add_valid_server_session_state_preserves_state_inv len_now  acme_server_principal version_vec last_state new_acme_server_state_element;
    set_state acme_server_principal version_vec' new_state; 
    let label_bytes = string_to_bytes "Replay-Nonce" in
    let header = (label_bytes, fresh_nonce) in
    let resp:http_response = {resp_req_id = request.req_id; resp_status = HTTP_STATUS_200_OK; resp_headers = Seq.create 1 header; resp_body = string_to_bytes ""} in
    let len_now = current_trace_len () in
    http_request_is_publishable_implies_request_id_is_publishable app_preds len1 request;
    is_publishable_p_later_lemma app_preds len1 request.req_id;
    assert(later len1 len_now);
    assert(is_publishable_p app_preds len_now resp.resp_req_id);
    assert(is_publishable_p app_preds len_now resp.resp_body);
    is_publishable_p_later_lemma app_preds i fresh_nonce;
    assert(is_publishable_p app_preds len_now fresh_nonce);
    Seq.Properties.lemma_contains_singleton header;
    concatenation_of_publishable_bytes_is_publishable_forall app_preds;
    assert(forall x. Seq.contains resp.resp_headers x ==> x == header);
    assert(forall x. Seq.contains resp.resp_headers x ==> x == (label_bytes, fresh_nonce) );
  assert(forall x.Seq.contains resp.resp_headers x ==> is_publishable_p app_preds len_now (dy_concat (fst x) (snd x)));
    serialized_sequence_of_bytes_tuples_publishable_if_all_elements_publishable app_preds len_now resp.resp_headers;
     
    assert(is_publishable_p app_preds len_now (serialize_sequence_of_bytes_tuples resp.resp_headers));
    assert(all_elements_of_http_response_are_publishable app_preds len_now resp);
    label_of_http_response_can_flow_to_public app_preds len_now resp;
    assert(is_publishable_p app_preds len_now (serialize_http_response resp));
    resp
#pop-options
