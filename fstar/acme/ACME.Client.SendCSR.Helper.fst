/// ACME.Client.SendCSR.Helper (implementation)
/// =====================================================

module ACME.Client.SendCSR.Helper
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
open SerializationLemmas

#set-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 500"

let gen_jws_req_helper client tr_idx acc_priv_key acc_url finalize_url replay_nonce payload =
  let sig_msg = generate_message_for_jws_signature acc_url finalize_url replay_nonce payload in
  assert(acme_sign_pred  (readers [any client]) app_preds tr_idx sig_msg);
  assert(exists j. j<= tr_idx /\ acme_sign_pred  (readers [any client]) app_preds j sig_msg) ;
  sig_key_usage_pred_lemma tr_idx (acme_sign_pred  (readers [any client]) app_preds)  sig_msg;
  let up:DY.Crypto.usage_pred DY.Crypto.sig_key_usage = acme_sig_key_usage (readers [any client]) app_preds in
  assert(DY.Crypto.sign_pred up tr_idx sig_msg);
  assert(is_sign_key_p app_preds tr_idx acc_priv_key (readable_by (readers [any client])) up);
  let jws_req = generate_jws_acme_request app_preds tr_idx up acc_url finalize_url replay_nonce payload acc_priv_key (readable_by (readers [any client])) in  elements_of_jws_acme_request_are_publishable_implies_jws_request_is_publishable app_preds tr_idx acc_url finalize_url replay_nonce payload acc_priv_key (readers [any client]);
  jws_req



#push-options "--max_fuel 2 --max_ifuel 1 --z3rlimit 100"
let gen_pen_request_session_helper client tr_idx request_nonce idx_csr serv_dom state v =
  flows_to_public_can_flow (app_preds.model.corrupt_at tr_idx) (get_label request_nonce)  (readable_by (readers [any client]));
  let pen_req_ss = HTTPSPendingRequest request_nonce idx_csr serv_dom  in
  assert(valid_acme_client_st state tr_idx app_preds client pen_req_ss);
  let v_req_ss = Seq.snoc v 0 in
  let st_pen_req = Seq.snoc state (serialize_acme_client_state pen_req_ss) in
  assert(state_inv tr_idx client v state);
  add_valid_client_session_state_preserves_state_inv tr_idx client v state pen_req_ss;
  assert(is_principal_state_readable tr_idx client v_req_ss st_pen_req);
  assert(state_inv tr_idx client v_req_ss st_pen_req);
  (v_req_ss, st_pen_req)

#pop-options



let gen_http_request_helper client jws_req request_nonce order len_begin i len_now =
      assert(later len_begin len_now);
      is_publishable_p_later_lemma app_preds i request_nonce;
      assert(is_publishable_p app_preds len_now request_nonce);
      later_is_transitive len_begin i len_now;
      assert(later len_begin len_now);

      let serialized_order = serialize_acme_order order in
      assert(is_publishable_p app_preds len_begin serialized_order);
      is_publishable_p_later_lemma app_preds len_begin serialized_order;
      assert(is_publishable_p app_preds len_now serialized_order);

      acme_order_is_publishable_implies_finalize_url_is_publishable len_now order;
      let finalize_url = Some?.v order.acme_order_finalize in
      let finalize_dom = finalize_url.url_domain in
      let server = domain_principal_mapping finalize_dom in

      let req_header = generate_request_header_host_domain finalize_dom in
      request_header_host_domain_is_publishable len_now finalize_dom;
      assert(is_publishable_p app_preds len_now  (serialize_url finalize_url));
      url_is_publishable_implies_request_uri_is_publishable app_preds len_now finalize_url;
      let http_req:http_request = {
               req_id = request_nonce;
               req_method = HTTP_METHOD_POST;
               req_uri = finalize_url.url_request_uri;
               req_headers = req_header;
               req_body = serialize_jws_acme_request jws_req
         } in
       assert(all_elements_of_http_request_are_publishable app_preds len_now http_req);
       (http_req, server)
