/// ACME.Server.KeyRollover
/// =======================
module ACME.Server.KeyRollover

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
open HelperFunctions
open ACME.Data.Predicates
open SerializationHelpers
open ACME.Data

val _acme_server_update_account_key:
    acme_server_principal:principal ->
    request:http_request ->
  DYL (http_response)
    (requires (fun h0 ->
      http_request_header_contains_domain_of_server request acme_server_principal /\
      is_publishable_p app_preds (trace_len h0) (serialize_http_request request)
    ))
    (ensures (fun h0 response h1 ->
      response.resp_status == HTTP_STATUS_200_OK /\
      is_publishable_p app_preds (trace_len h1) (serialize_http_response response)
    ))
