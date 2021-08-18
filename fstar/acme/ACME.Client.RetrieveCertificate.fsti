/// ACME.Client.RetrieveCertificate
/// ==========================================


module ACME.Client.RetrieveCertificate
open Helpers
open DY.Monad
open DY.Labels
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open Application.Predicates
open ACME.Data
open SerializationLemmas
open SerializationHelpers


val _acme_client_retrieves_certificate_save_state:
  client:principal ->
  certificate_url:url->
  csr_sess_idx:nat ->
  account_sess_idx:nat  ->
  DYL ( req:http_request * server:principal * replay_nonce:bytes)
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_url certificate_url))
  (ensures fun h0 (req, server, _) h1 -> all_elements_of_http_request_are_publishable app_preds (trace_len h1) req)
