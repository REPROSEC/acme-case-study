/// ACME.Server.TriggerChallengeVerification
/// =========================================
module ACME.Server.TriggerChallengeVerification

open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Monad
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open Application.Predicates
open HelperFunctions
open SerializationHelpers

// Step 7 of the protocol description in acme.md
val _acme_server_trigger_challenge_verification:
      server:principal ->
      DYL http_request
      (requires (fun t0 -> True))
      (ensures (fun t0 request t1 -> is_publishable_p app_preds (trace_len t1) (serialize_http_request request)))
