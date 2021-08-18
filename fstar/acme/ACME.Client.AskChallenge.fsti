/// ACME.Client.AskChallenge
/// =========================
module ACME.Client.AskChallenge

open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open DY.Monad
open Labeled.ApplicationAPI
open Application.Predicates
open Labeled.Crypto
open ACME.Data
open ACME.Data.Predicates
open SerializationLemmas
open SerializationHelpers
open ACME.Client.HelperFunctions

val _acme_client_receive_order_response_save_state:
  client: principal ->
  updated_order:acme_order{
                    is_updated_order updated_order } ->
  order_sessionid:nat ->
  opt_current_order_url: option url ->
  DYL (order_sessionid:nat * number_of_authorization_urls:nat)
  (requires fun h0 -> acme_order_is_publishable app_preds (trace_len h0) updated_order /\
    (can_label_of_bytes_flow_to app_preds (trace_len h0) (serialize_opt_url opt_current_order_url ) public)
  )
  (ensures fun h0 r h1 -> True )

val _acme_client_asks_for_authorization_save_state:
  client: principal ->
  order_sessionid:nat ->
  authz_url_idx:nat ->
  DYL (
          req:http_request *
          server:principal *
          replay_nonce:bytes
      )
  (requires fun h0 -> True)
  (ensures fun h0 (req, _, _) h1 ->  all_elements_of_http_request_are_publishable app_preds (trace_len h1) req )

