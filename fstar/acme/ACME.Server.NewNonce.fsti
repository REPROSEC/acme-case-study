/// ACME.Server.NewNonce
/// =====================
module ACME.Server.NewNonce

open Helpers
open DY.Monad
open DY.Labels
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open HelperFunctions
open SerializationHelpers
open Application.Predicates

// RFC8555 7.2 Getting a Nonce
val _acme_server_new_nonce:
      acme_server_principal:principal ->
      request:http_request{
        request.req_method == HTTP_METHOD_HEAD /\
        eq_path
          request.req_uri.uri_path
          (init_seq_bytes_with_list [string_to_bytes "acme"; string_to_bytes "new-nonce"])} ->
      DYL (response:http_response{response.resp_status == HTTP_STATUS_200_OK}
          )
         (requires (fun t0 -> is_publishable_p app_preds (trace_len t0) (serialize_http_request request)))
         (ensures (fun t0 resp t1 -> is_publishable_p app_preds (trace_len t1) (serialize_http_response resp)))
