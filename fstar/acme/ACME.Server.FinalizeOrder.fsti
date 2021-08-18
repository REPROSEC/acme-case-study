/// ACME.Server.FinalizeOrder
/// ==============================
module ACME.Server.FinalizeOrder

open DY.Monad
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open Application.Predicates
open HelperFunctions
open ACME.Data.Predicates
open Application.Predicates
open SerializationHelpers

// Step 9/10 of the protocol description in acme.md
val _acme_server_finalize_order:
      acme_server_principal:principal ->
      request:http_request ->
      DYL http_response
         (requires (fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_request request)))
         (ensures (fun h0 response h1 -> is_publishable_p app_preds (trace_len h1) (serialize_http_response response)))
