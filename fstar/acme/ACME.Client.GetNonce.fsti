/// ACME.Client.GetNonce
/// =======================

module ACME.Client.GetNonce

open DY.Principals
open DY.Monad
open DY.Trace
open DY.Crypto
open Labeled.Crypto
open Labeled.ApplicationAPI
open Web.Messages
open Application.Predicates
open SerializationLemmas
open SerializationHelpers

val _acme_client_get_nonce_save_state: client:principal -> nonce:bytes -> serv_dom:domain->
  DYL nat
  (requires fun t0 -> 
    is_publishable_p app_preds (trace_len t0) nonce
  )
  (ensures fun t0 _ t1 -> later (trace_len t0) (trace_len t1) )
