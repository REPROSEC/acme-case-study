/// ACME.Server.NewOrder
/// =====================
module ACME.Server.NewOrder


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

// 
(**
    RFC8555 7.4 Applying for Certificate Issuance
    The issuance process starts here. The client sends a POST request containing an ACME order.
    Upon receiving this request, the server sends an ACME order containing an updated status, the same identifiers,
    and URLs for the authorization and finalize endpoints.
*)
val _acme_server_new_order:
  acme_server_principal:principal ->
  request:http_request ->
  DYL (response:http_response)
     (requires (fun h0 -> 
        http_request_header_contains_domain_of_server request acme_server_principal /\
        is_publishable_p app_preds (trace_len h0) (serialize_http_request request)
     ))
     (ensures (fun h0 response h1 -> 
        response.resp_status == HTTP_STATUS_201_CREATED /\
        acme_order_in_http_response_is_publishable app_preds (trace_len h1) response /\
        is_publishable_p app_preds (trace_len h1) (serialize_http_response response)
     ))
