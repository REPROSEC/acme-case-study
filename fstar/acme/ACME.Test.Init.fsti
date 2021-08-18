/// AMCE.Test.Init
/// ==============================
module ACME.Test.Init

open DY.Entry
open DY.Monad
open DY.Labels
open DY.Principals
open DY.Crypto
open DY.Trace
open Labeled.Crypto
open Labeled.ApplicationAPI
open Web.Messages
open SerializationHelpers
open ACME.Data
open ACME.Data.SerializationHelpers
open Application.Predicates
open HelperFunctions

(** generate an account and stored account information in client (private key, account url) and server's states (public key, account url)*)
val gen_account:
  client:principal ->
  server:principal ->
  account_url:url ->
  order_url:url ->
  DYL (si_client:nat * si_server:nat)
  (requires fun t0 ->
    is_publishable_p app_preds (trace_len t0) (serialize_url account_url) /\
    is_publishable_p app_preds (trace_len t0) (serialize_url order_url)
  )
  (ensures fun _ _ _ -> True)


val gen_private_ca_key: server:principal -> DYL (si:nat)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

val gen_publishable_url: trace_index:nat -> dom:domain -> path_strings:list string -> u:url{is_publishable_p app_preds trace_index (serialize_url u)}

val gen_new_replay_nonce_url: 
  trace_idx:nat -> 
  serv_dom:domain -> 
  u:url{
    is_publishable_p app_preds trace_idx (serialize_url u) /\
    eq_path u.url_request_uri.uri_path (init_seq_bytes_with_list [string_to_bytes "acme"; string_to_bytes "new-nonce"])
  }
