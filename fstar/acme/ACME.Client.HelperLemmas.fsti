/// ACME.Client.HelperLemmas
/// ==========================================
module ACME.Client.HelperLemmas

open Helpers
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
open ACME.Data.Predicates
open Application.Predicates.Helpers
open Application.Predicates.Lemmas



val add_valid_client_session_state_preserves_state_inv:
  tr_idx:nat ->
  client:principal ->
  current_version_vec: version_vec ->
  current_state:app_state tr_idx client current_version_vec ->
  new_ss:acme_client_state{valid_acme_client_st current_state tr_idx app_preds client new_ss} ->
  Lemma
  (requires state_inv tr_idx client current_version_vec current_state)
  (ensures (
    let new_state = Seq.snoc current_state (serialize_acme_client_state new_ss) in
    let new_version_vec = Seq.snoc current_version_vec 0 in
    state_inv tr_idx client new_version_vec new_state /\
    is_principal_state_readable tr_idx client new_version_vec new_state
  ))

val update_valid_ReplayNonce_session_state_preserves_state_inv:
  tr_idx: nat ->
  client:principal ->
  current_version_vec: version_vec ->
  current_state:app_state tr_idx client current_version_vec ->
  sess_idx:nat {sess_idx < Seq.length current_state /\ is_ReplayNonce_session current_state.[sess_idx]} ->
  acme_order_ss:acme_client_state{ReplayNonce? acme_order_ss /\ valid_acme_client_st current_state tr_idx app_preds client acme_order_ss} ->
  Lemma
  (requires state_inv tr_idx client current_version_vec current_state)
  (ensures (
    let updated_state = current_state.[sess_idx] <- (serialize_acme_client_state acme_order_ss) in
    state_inv tr_idx client current_version_vec updated_state /\
    is_principal_state_readable tr_idx client current_version_vec updated_state
  ))

