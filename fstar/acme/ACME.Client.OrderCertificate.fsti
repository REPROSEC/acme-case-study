/// ACME.Client.OrderCertificate
/// =============================
module ACME.Client.OrderCertificate

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
open SerializationHelpers
open ACME.Data.Predicates
open SerializationLemmas


val _acme_client_orders_certificate_save_state: client: principal -> doms:Seq.seq domain{Seq.length doms > 0} -> idx_account:nat ->
DYL (
     server:principal &
     req:http_request{
      http_request_header_contains_domain_of_server req server
     }&
     replay_nonce:bytes
   )
(requires fun h0 -> True)
(ensures fun h0 r h1 ->
  ( let (|server, req, _|) = r in
    all_elements_of_http_request_are_publishable app_preds (trace_len h1) req
  )
)
