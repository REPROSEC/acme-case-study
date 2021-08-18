/// ACME.Client.SendCSR.Helper
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
open FStar.Seq.Base

open SerializationHelpers
open FStar.String
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open ACME.Client.HelperLemmas
open ACME.Client.HelperFunctions
open ACME.Data.Predicates
open SerializationLemmas


val gen_jws_req_helper:
  client:principal ->
  tr_idx:nat ->
  acc_priv_key:bytes{is_sign_key_p app_preds tr_idx acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds)} ->
  acc_url:url{is_publishable_p app_preds tr_idx (serialize_url acc_url)} ->
  finalize_url:url{is_publishable_p app_preds tr_idx (serialize_url finalize_url)} ->
  replay_nonce:bytes{is_publishable_p app_preds tr_idx replay_nonce} ->
  payload:bytes{is_publishable_p app_preds tr_idx payload} ->
  Pure (jws_req: jws_acme_request{is_publishable_p app_preds tr_idx (serialize_jws_acme_request jws_req)})
  (requires
     acme_sign_pred  (readers [any client]) app_preds tr_idx (generate_message_for_jws_signature acc_url finalize_url replay_nonce payload)
  )
  ( ensures fun _ -> True)


val gen_pen_request_session_helper:
  client:principal ->
  tr_idx:nat ->
  req_nonce:bytes ->
  idx_csr:nat ->
  serv_dom: domain ->
  state: principal_state ->
  v: version_vec ->
  Pure (version_vec * principal_state)
  (requires
    is_publishable_p app_preds tr_idx req_nonce /\
    is_principal_state_readable tr_idx client v state /\
    state_inv tr_idx client v state
  )
  (ensures fun (new_v, new_state) ->
    is_principal_state_readable tr_idx client new_v new_state /\
     state_inv tr_idx client new_v new_state
  )

val gen_http_request_helper:
  client:principal ->
  jws_req:jws_acme_request ->
  request_nonce:bytes ->
  order:acme_order{is_updated_order order} ->
  len_begin: nat ->
  i:nat ->
  len_now:nat ->
  Pure (http_request * principal)
  (requires
     later i len_now /\
     later len_begin i /\
     is_publishable_p app_preds len_begin (serialize_jws_acme_request jws_req) /\
     is_publishable_p app_preds i request_nonce /\
     is_publishable_p app_preds len_begin (serialize_acme_order order)
  )
  (ensures
     fun (req, _) -> all_elements_of_http_request_are_publishable app_preds len_now req
  )

