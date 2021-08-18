/// ACME.Client.RequestNonce
/// ============================

module ACME.Client.RequestNonce
open DY.Principals
open DY.Monad
open DY.Trace
open Labeled.Crypto
open Labeled.ApplicationAPI
open Web.Messages
open Application.Predicates
open SerializationLemmas
open SerializationHelpers

val _acme_client_request_replay_nonce_save_state: client:principal -> newNonce_url:url ->
  DYL( server:principal* req:http_request)
  (requires fun t0 -> 
    is_publishable_p app_preds (trace_len t0) (serialize_url newNonce_url)
  )
  (ensures fun t0 (server, req) t1 -> 
     //later (trace_len t0) (trace_len t1) /\
     all_elements_of_http_request_are_publishable app_preds (trace_len t1) req
  )

