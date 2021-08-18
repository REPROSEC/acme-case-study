/// ACME.Client.SendCSR
/// =============================
module ACME.Client.SendCSR


open Helpers
open DY.Monad
open Web.Messages
open DY.Labels
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open ACME.Data
open Application.Predicates.Helpers
open Application.Predicates
open ACME.Data.Predicates
open SerializationHelpers
open SerializationLemmas
open ACME.Client.HelperFunctions
open ACME.Data.SerializationHelpers


val _acme_client_add_valid_CSR_session:
  client: principal ->
  idx_order: nat ->
  DYL (
      idx_csr:nat *
      cert_priv_key: bytes *
      order:acme_order *
      acc_priv_key:bytes *
      acc_url:url *
      finalize_url: url *
      replay_nonce:bytes *
      payload:bytes
      //jws_req:jws_acme_request
      )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
     ( let (idx_csr, cert_priv_key, order, acc_priv_key, acc_url, finalize_url, replay_nonce, payload) = r in
       is_private_dec_key_p app_preds (trace_len h1) cert_priv_key (readable_by (readers [any client])) (acme_pke_key_usage (readers [any client])) /\
       is_updated_order order /\
       can_label_of_bytes_flow_to app_preds (trace_len h1) (serialize_acme_order order ) public /\
       is_sign_key_p app_preds (trace_len h1) acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds) /\
       can_label_of_bytes_flow_to app_preds (trace_len h1) (serialize_url acc_url ) public /\
       can_label_of_bytes_flow_to app_preds (trace_len h1) (serialize_url finalize_url ) public /\
       //is_publishable_p app_preds (trace_len h1) (serialize_jws_acme_request jws_req) /\
       is_publishable_p app_preds (trace_len h1) payload /\
       is_publishable_p app_preds (trace_len h1) replay_nonce /\
       acme_sign_pred  (readers [any client]) app_preds (trace_len h1) (generate_message_for_jws_signature acc_url finalize_url replay_nonce payload)
       //Success? (parse_acme_csr jws_req.payload)
     )
  )


val _acme_client_send_CSR_save_state:
  client: principal ->
  idx_csr:nat ->
  cert_priv_key: bytes ->
  order:acme_order ->
  acc_priv_key:bytes ->
  acc_url:url ->
  finalize_url: url ->
  replay_nonce:bytes -> 
  payload:bytes ->
  //jws_req:jws_acme_request ->
  DYL (
      req:http_request *
      server:principal *
      replay_nonce:bytes
    )
  (requires fun h0 ->
    is_private_dec_key_p app_preds (trace_len h0) cert_priv_key (readable_by (readers [any client])) (acme_pke_key_usage (readers [any client])) /\
    is_updated_order order /\
    can_label_of_bytes_flow_to app_preds (trace_len h0) (serialize_acme_order order ) public /\
    is_sign_key_p app_preds (trace_len h0) acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds) /\
    can_label_of_bytes_flow_to app_preds (trace_len h0) (serialize_url acc_url ) public /\
    //is_publishable_p app_preds (trace_len h0) (serialize_jws_acme_request jws_req) /\
    can_label_of_bytes_flow_to app_preds (trace_len h0) (serialize_url finalize_url ) public /\
    acme_sign_pred  (readers [any client]) app_preds (trace_len h0) (generate_message_for_jws_signature acc_url finalize_url replay_nonce payload) /\
       //is_publishable_p app_preds (trace_len h1) (serialize_jws_acme_request jws_req) /\
    is_publishable_p app_preds (trace_len h0) replay_nonce /\
    is_publishable_p app_preds (trace_len h0) payload
    //Success? (parse_acme_csr jws_req.payload)
  )
  (ensures fun h0 r h1 ->
    ( let (req, _, _) = r in
      all_elements_of_http_request_are_publishable app_preds (trace_len h1) req
    )
  )

