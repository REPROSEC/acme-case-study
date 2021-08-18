/// ACME.Client.PollOrderEndpoint
/// ==========================================


module ACME.Client.PollOrderEndpoint
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


(**
    Send an empty request (Post-as-Get) to the [location_header_url].

    This function creates the http request that is used for polling at the order endpoint after the
    ACME server returns an updated acme order with the status [Processing] at the finalize endpoint.

    The [location_header_url] is the url contained in the Location header of the finalize response.
*)
val _acme_client_poll_order_endpoint_with_csr_idx:
  client:principal ->
  location_header_url:url->
  csr_sess_idx:nat ->
  account_sess_idx:nat  ->
  DYL ( req:http_request * server:principal * replay_nonce:bytes)
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_url location_header_url))
  (ensures fun h0 (req, server, _) h1 -> all_elements_of_http_request_are_publishable app_preds (trace_len h1) req)


(**
    Create an empty request (Post-as-Get) to the current order endpoint that is stored in the ACMEOrder client
    session.
*)
val _acme_client_poll_order_endpoint:
  client:principal ->
  acme_order_sessionid: nat ->
  DYL (req:http_request * server:principal * replay_nonce:bytes)
  (requires fun h0 -> True)
  (ensures fun h0 (req, server, _) h1 -> all_elements_of_http_request_are_publishable app_preds (trace_len h1) req)
