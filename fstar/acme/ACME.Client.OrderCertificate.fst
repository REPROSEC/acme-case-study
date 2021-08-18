/// ACME.Client.OrderCertificate (implementation)
/// ==============================================
module ACME.Client.OrderCertificate


open Helpers
open DY.Monad
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
open FStar.String
open ACME.Data.Predicates
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open ACME.Client.HelperLemmas
open ACME.Client.HelperFunctions
open SerializationLemmas

#set-options "--max_fuel 2 --max_ifuel 0  --z3rlimit 250"
let _acme_client_orders_certificate_save_state client doms idx_acc  =
    let (|idx, request_nonce|) = guid_gen () in
    let (|i, v, state|) = get_last_state client in
    if idx_acc < Seq.length state  then (
      let ss_acc_st = state.[idx_acc] in
      match parse_acme_client_state ss_acc_st with
      | Success (Account acc_priv_key acc_url order_url) -> (
        //construct acme jws request
        let order_dom = order_url.url_domain in
        match client_finds_valid_replay_nonce i client v state order_dom with
        |Success replay_nonce -> (
        let order:acme_order = {
          acme_order_status = None;
          acme_order_identifiers = doms;
          acme_order_authorizations = None;
          acme_order_finalize = None;
          acme_order_certificate = None
        } in
        (*  save the new state session ACMEOrder    *)
        let acme_order_ss = ACMEOrder order idx_acc None in
        let v_order = Seq.snoc v 0 in
        let ss_order = (serialize_acme_client_state acme_order_ss) in
        let st_order = Seq.snoc state ss_order in
        acme_order_containing_only_domain_is_publishable i order;
        add_valid_client_session_state_preserves_state_inv i client v state acme_order_ss; //admit();
        //assert(state_inv len_now client v_order st_order);
        let st_order': app_state i client v_order = st_order in
        (*       save the new state session HTTPSPendingRequest   *)
        let server = domain_principal_mapping order_dom in
        let payload =  serialize_acme_order order in
        assert(is_sign_key_p app_preds i acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));//admit();
        generate_message_for_jws_signature_structure app_preds acc_url order_url replay_nonce payload; //admit();
        parse_acme_csr_error_if_acme_order order;
        assert(acme_sign_pred  (readers [any client]) app_preds i (generate_message_for_jws_signature acc_url order_url replay_nonce payload)); //admit();
        let jws_req = generate_jws_acme_request app_preds i (acme_sig_key_usage (readers [any client]) app_preds) acc_url order_url replay_nonce payload acc_priv_key (readable_by (readers [any client])) in //admit();
        elements_of_jws_acme_request_are_publishable_implies_jws_request_is_publishable app_preds i acc_url order_url replay_nonce payload acc_priv_key (readers [any client]); 
        assert(later idx i); //admit();
        let req_header = (string_to_bytes app_preds i "Host", serialize_domain order_dom) in
        let pen_req_ss = HTTPSPendingRequest request_nonce (Seq.length v) order_dom in //the reference points to the session ACMEOrder added above
        let v_req_ss = Seq.snoc v_order 0 in
        let ss_req = serialize_acme_client_state pen_req_ss in
        let st_pen_req = Seq.snoc st_order' ss_req in
        flows_to_public_can_flow (app_preds.model.corrupt_at i) (get_label request_nonce) (readable_by (readers [any client]));
        //assert(can_label_of_bytes_flow_to app_preds request_nonce (readable_by (readers [any client])));
        //assert(can_label_of_bytes_flow_to app_preds sym_key (readable_by (readers [any client])));
        add_valid_client_session_state_preserves_state_inv i client v_order st_order pen_req_ss;
        let st':app_state i client v_req_ss = st_pen_req in
        set_state client v_req_ss st';
        //set_state client v_req_ss st_pen_req;
        let request_body = serialize_jws_acme_request jws_req in
        let len_now = current_trace_len () in
        assert(later i len_now);
        assert(is_publishable_p app_preds len_now request_nonce);
        assert(is_publishable_p app_preds len_now (serialize_url order_url ));
        url_is_publishable_implies_request_uri_is_publishable app_preds len_now order_url;
        assert(is_publishable_p app_preds len_now (serialize_request_uri order_url.url_request_uri));
        assert(is_publishable_p app_preds len_now request_body);
        let http_req = gen_http_request_with_server_domain_in_header len_now server request_nonce order_dom order_url.url_request_uri request_body in
        assert(Success? (parse_jws_acme_request http_req.req_body));
        assert(Success? (parse_acme_order (Success?.v (parse_jws_acme_request http_req.req_body)).payload));
        assert(all_elements_of_http_request_are_publishable app_preds len_now http_req);
        (|server, http_req, replay_nonce|) 
        )
        | _ -> error "there is no replay nonce to send request"
      )
     | _ -> error "fail to save new Order state"
    ) else error "fail to save new Order state"
#reset-options

