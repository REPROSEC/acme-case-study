/// ACME.Client.HelperLemmas (implementation)
/// ==========================================
module ACME.Client.HelperLemmas

open Helpers
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
open FStar.Seq.Base

open SerializationHelpers
open FStar.String
open ACME.Data.Predicates
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
friend Application.Predicates


#set-options "--z3refresh --max_fuel 8 --max_ifuel 8 --z3rlimit 500"
let add_valid_client_session_state_preserves_state_inv tr_idx client v state new_ss =
  let new_state = Seq.snoc state (serialize_acme_client_state new_ss) in
  let new_v = Seq.snoc v 0 in
  valid_serialize_acme_client_st_lemma state tr_idx client (Seq.length v) new_ss;
  parse_acme_client_state_lemma new_ss;
  parse_acme_server_st_of_client_st_returns_none new_ss;
  assert(state_inv tr_idx client new_v new_state);
  state_inv_implies_principal_state_readable tr_idx client new_v new_state


let update_valid_ReplayNonce_session_state_preserves_state_inv tr_idx client v state idx_order acme_order_ss =
  let updated_state = state.[idx_order] <- (serialize_acme_client_state acme_order_ss) in
  valid_serialize_acme_client_st_lemma state tr_idx client idx_order acme_order_ss;
  parse_acme_client_state_lemma acme_order_ss;
  parse_acme_server_st_of_client_st_returns_none acme_order_ss;
  assert(state_inv tr_idx client v updated_state);
  state_inv_implies_principal_state_readable tr_idx client v updated_state
