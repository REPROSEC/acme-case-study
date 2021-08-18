/// ACME.Client.ReceiveMessage
/// ==============================
module ACME.Client.ReceiveMessage

open Helpers
open Web.Messages
open DY.Entry
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Labeled.ApplicationAPI
open Application.Predicates
open Labeled.Crypto
open ACME.Data
open ACME.Client.HelperFunctions
open ACME.Data.Predicates
open SerializationHelpers
(**
acme.md #3
*)
val acme_client_receives_response_for_new_order:
  tr_idx:nat ->
  http_resp: http_response {is_publishable_p app_preds tr_idx (serialize_http_response http_resp)} ->
  current_state:principal_state ->
  result (
           order:acme_order{acme_order_is_publishable app_preds tr_idx order /\
                            is_updated_order order } *
           init_order_sess_idx:nat
         )


(**
acme.md #5
*)
val acme_client_receives_response_for_asking_challenge:
  tr_idx:nat ->
  http_resp: http_response {is_publishable_p app_preds tr_idx (serialize_http_response http_resp)} ->
  current_state: principal_state ->
  result ( authorization:acme_authorization{acme_authorization_is_publishable app_preds tr_idx authorization}  *
           order_sess_idx:nat
         )



(**
acme.md #8
*)
val acme_client_receives_challenge_request:
  tr_idx:nat ->
  client:principal ->
  http_req: http_request{is_publishable_p app_preds tr_idx (serialize_http_request http_req)}  ->
  current_state:principal_state->
  result (
           account_sessionid: nat *
           authorization_sessionid: nat *
           request_id:bytes {is_publishable_p app_preds tr_idx request_id}
         )


(**
  The ACME client receives the response from the finalize endpoint (to which the CSR was sent). If
  this response contains an acme order with the status [Valid], the client can immediately send the
  request to the certificate endpoint.

  If the status of the order is [Valid], this function returns the certificate url and no location
  header url.

  If the status of the order is [Processing], this function returns the url contained in the
  Locations header of the response. The client needs to send requests to this endpoint to get an
  updated order object with the status being [Valid].
*)
val acme_client_receives_finalize_order:
 tr_idx:nat ->
  http_resp: http_response{is_publishable_p app_preds tr_idx (serialize_http_response http_resp)}  ->
  current_state:principal_state->
  result (
           csr_sess_idx: nat *
           account_sess_idx: nat *
           opt_certificate_url:option (certificate_url:url{is_publishable_p app_preds tr_idx (serialize_url certificate_url)}) *
           opt_location_header_url:option (location_header_url:url{is_publishable_p app_preds tr_idx (serialize_url location_header_url)})
         )

val acme_client_receives_certificate:
  tr_idx:nat ->
  http_resp: http_response{is_publishable_p app_preds tr_idx (serialize_http_response http_resp)}  ->
  current_state:principal_state ->
  result (
          certificate:acme_certificate{certificate_is_publishable app_preds tr_idx certificate} *
          retrieve_cert_sessionid:nat
         )


val extract_replay_nonce_from_response:
  tr_idx:nat ->
  http_resp: http_response {is_publishable_p app_preds tr_idx (serialize_http_response http_resp)} ->
  result (replay_nonce: bytes{is_publishable_p app_preds tr_idx replay_nonce})

(**
acme.md: client returns replay nonce and server domain from incomming http response and its internal state
*)
val acme_client_returns_replay_nonce_and_server_domain_for_response:
  tr_idx:nat ->
  http_resp: http_response {is_publishable_p app_preds tr_idx (serialize_http_response http_resp)} ->
  current_state: principal_state ->
  result (replay_nonce: bytes{is_publishable_p app_preds tr_idx replay_nonce} *
          server_dom: domain
         )
