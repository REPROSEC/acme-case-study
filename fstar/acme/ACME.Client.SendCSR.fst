/// ACME.Client.SendCSR
/// =============================
module ACME.Client.SendCSR


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
open ACME.Client.SendCSR.Helper



#set-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 500"


//#push-options "--max_fuel 16 --max_ifuel 16 --z3rlimit 500"
let _acme_client_add_valid_CSR_session client idx_order =
    let (|idx, cert_priv_key|) = secret_gen (readable_by (readers [any client])) pke_key_usage (acme_pke_key_usage (readers [any client])) in
    let (|i, v, state|) = get_last_state client in
    if idx_order < Seq.length state then (
      match parse_acme_client_state (state.[idx_order]) with
      | Success (ACMEOrder order idx_acc _) -> (
        assert(exists i'. i'< i /\ is_set_state_at i' client v state);
        assert(exists i'. i'< i /\ client_sent_newOrder_request client order.acme_order_identifiers v state i' idx_order);
        if idx_acc < Seq.length state && is_updated_order order then (
          match parse_acme_client_state (state.[idx_acc]) with
          | Success (Account acc_priv_key acc_url _) -> (
              assert(is_labeled_p app_preds idx  cert_priv_key (readable_by (readers [any client])));
              is_private_dec_key_p_later_lemma app_preds idx cert_priv_key (readable_by (readers [any client])) (acme_pke_key_usage (readers [any client]));
              assert(is_private_dec_key_p app_preds idx cert_priv_key (readable_by (readers [any client])) (acme_pke_key_usage (readers [any client])));
              assert(later idx i);
               assert(is_private_dec_key_p app_preds i cert_priv_key (readable_by (readers [any client])) (acme_pke_key_usage (readers [any client]) ));
              assert(is_labeled_p app_preds i cert_priv_key (readable_by (readers [any client])));
              let csr_ss = CSR cert_priv_key order.acme_order_identifiers idx_order i in
              let ss_csr = serialize_acme_client_state csr_ss in
              let st_csr = Seq.snoc state ss_csr in
              let v_csr = Seq.snoc v 0 in
              assert(valid_acme_client_st state i app_preds client csr_ss);
              add_valid_client_session_state_preserves_state_inv i client v state csr_ss;
              set_state client v_csr st_csr;
              let len_now = current_trace_len () in
              assert(is_publishable_p app_preds i (serialize_acme_order order));
              assert(later i len_now);
              assert(is_publishable_p app_preds len_now (serialize_acme_order order));
              acme_order_is_publishable_implies_finalize_url_is_publishable len_now order;
              let finalize_url = Some?.v order.acme_order_finalize in
              let finalize_dom = finalize_url.url_domain in
              match client_finds_valid_replay_nonce len_now client v state finalize_dom with
              |Success replay_nonce -> (
                assert(is_secret_p app_preds idx cert_priv_key (readable_by (readers [any client])) pke_key_usage (acme_pke_key_usage (readers [any client]) ));
                assert(is_secret_p app_preds i cert_priv_key (readable_by (readers [any client])) pke_key_usage (acme_pke_key_usage (readers [any client])));
                assert(is_secret_p app_preds len_now cert_priv_key (readable_by (readers [any client])) pke_key_usage (acme_pke_key_usage (readers [any client])));
                let cert_public_key = pk #app_preds #len_now #(readable_by (readers [any client])) #(acme_pke_key_usage (readers [any client]) ) cert_priv_key in
                let ordered_domains = order.acme_order_identifiers in
                let csr:acme_csr = {
                  acme_csr_identifiers = ordered_domains;
                  acme_csr_pub_key = cert_public_key
                } in
                let payload = serialize_acme_csr csr in
                csr_is_publishable_with_publishable_public_key len_now csr;
                assert(is_sign_key_p app_preds i acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));
                assert(is_sign_key_p app_preds len_now acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));

                generate_message_for_jws_signature_structure app_preds acc_url finalize_url replay_nonce payload;

                assert(match parse_acme_csr payload with
                  | Success temp_csr -> (temp_csr == csr)
                  | _ -> True //other signing cases
                );

                assert(exists (set_csr_st_idx:nat). set_csr_st_idx < len_now /\ client_stored_CSR client set_csr_st_idx csr.acme_csr_identifiers csr.acme_csr_pub_key);
                let sig_msg = generate_message_for_jws_signature acc_url finalize_url payload in
                assert(acme_sign_pred  (readers [any client]) app_preds len_now (generate_message_for_jws_signature acc_url finalize_url replay_nonce payload));
                assert(is_publishable_p app_preds len_now (serialize_url acc_url));
                assert(is_publishable_p app_preds len_now (serialize_url finalize_url));
                assert(is_publishable_p app_preds len_now payload);

                let up:DY.Crypto.usage_pred DY.Crypto.sig_key_usage = acme_sig_key_usage (readers [any client]) app_preds in
                assert(is_sign_key_p app_preds len_now acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));

                is_private_dec_key_p_later_lemma app_preds i cert_priv_key (readable_by (readers [any client])) (acme_pke_key_usage (readers [any client]) );
                assert(is_private_dec_key_p app_preds len_now cert_priv_key (readable_by (readers [any client])) (acme_pke_key_usage (readers [any client])));

                (Seq.length v, cert_priv_key, order, acc_priv_key, acc_url, finalize_url, replay_nonce, payload)
              )
              | _ -> error "there is no replay nonce to send request"
            )
          | _ -> error "fail to save CSR session state"
        )else error "fail to save CSR session state"
       )
      | _ -> error "fail to save CSR session state"
    ) else error "fail to save CSR session state"
//#pop-options




#push-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 500"
let _acme_client_send_CSR_save_state client idx_csr cert_priv_key order acc_priv_key acc_url finalize_url replay_nonce payload  =
      let len_begin = current_trace_len () in
      let jws_req = gen_jws_req_helper client len_begin acc_priv_key acc_url finalize_url replay_nonce payload  in
      assert(is_publishable_p app_preds len_begin (serialize_jws_acme_request jws_req));
      let (|idx, request_nonce|) = guid_gen () in
      let (|i, v, state|) = get_last_state client in
      assert(later len_begin idx);
      assert(later idx i);
      assert(later len_begin i);
      is_publishable_p_later_lemma app_preds len_begin request_nonce;
      assert(is_publishable_p app_preds i request_nonce);

      let (v_req_ss, st_pen_req  ) = gen_pen_request_session_helper client i request_nonce idx_csr finalize_url.url_domain state v in
      set_state client v_req_ss st_pen_req;
      let len_now = current_trace_len () in
      assert(later i len_now);
      let (http_req, server) = gen_http_request_helper client jws_req request_nonce order len_begin i len_now in
      (http_req, server, replay_nonce)

