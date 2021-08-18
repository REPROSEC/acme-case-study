/// ACME.Client.GetNonce (implementation)
/// ==========================================

module ACME.Client.GetNonce

open DY.Principals
open DY.Monad
open DY.Trace
open DY.Crypto
open Labeled.Crypto
open Labeled.ApplicationAPI
open Web.Messages
open Application.Predicates
friend Application.Predicates
open SerializationLemmas
open SerializationHelpers
open ACME.Data
open ACME.Data.SerializationHelpers
open Application.Predicates.Lemmas
open ACME.Data.SerializationLemmas
open ACME.Client.HelperLemmas

#set-options "--max_fuel 16 --max_ifuel 8 --z3rlimit 800"
let _acme_client_get_nonce_save_state client nonce serv_dom =
  let (|i, v, state|) = get_last_state client in
  let nonce_ss = ReplayNonce nonce true serv_dom in
  let ss_nonce = serialize_acme_client_state nonce_ss in
  let st_nonce = Seq.snoc state ss_nonce in
  let v_nonce = Seq.snoc v 0 in
  add_valid_client_session_state_preserves_state_inv i client v state nonce_ss;
  set_state client v_nonce st_nonce;
  (Seq.length v)
