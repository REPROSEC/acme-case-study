/// ACME.Client.TriggerChallenge
/// ============================
module ACME.Client.TriggerChallenge

open DY.Monad
open DY.Trace
open DY.Labels
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open ACME.Data
open Application.Predicates
open ACME.Data.Predicates
open SerializationLemmas

val _acme_client_receive_authorization_save_state:
  client: principal ->
  authorization:acme_authorization ->
  order_sess_idx:nat ->
  DYL (authz_sessionid: nat * number_of_challenges: nat)
  (requires fun h0 -> acme_authorization_is_publishable app_preds (trace_len h0) authorization)
  (ensures fun h0 r h1 -> True)

val _acme_client_triggers_challenge_i:
  client: principal ->
  authz_sessionid: nat ->
  challenge_idx: nat ->
  DYL (http_request * principal * bytes)
  (requires fun h0 -> True)
  (ensures fun h0 (req, _, _) h1 ->
      all_elements_of_http_request_are_publishable app_preds (trace_len h1) req
  )

