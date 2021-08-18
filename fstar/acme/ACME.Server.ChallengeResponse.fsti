/// ACME.Server.ChallengeResponse
/// ==============================
module ACME.Server.ChallengeResponse

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
open SerializationHelpers

// RFC8555 7.5.1 Responding to Challenges (trigger challenge validation)
// Step 5/6 of the protocol description in acme.md
val _acme_server_challenge_response:
      acme_server_principal:principal ->
      request:http_request ->
      DYL http_response
         (requires (fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_request request)))
         (ensures (fun h0 response h1 -> is_publishable_p app_preds (trace_len h1) (serialize_http_response response)))
