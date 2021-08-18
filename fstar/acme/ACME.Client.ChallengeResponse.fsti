/// ACME.Client.ChallengeResponse
/// =============================
module ACME.Client.ChallengeResponse

open DY.Monad
open Helpers
open Web.Messages
open DY.Labels
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open ACME.Data
open Application.Predicates
open SerializationHelpers
open SerializationLemmas
open Application.Predicates.Helpers

val _acme_client_challenge_response:
   client: principal ->
   account_sessionid: nat ->
   authorization_sessionid: nat ->
   request_id: bytes ->
   DYL (resp:http_response)
   (requires fun t0 -> is_publishable_p app_preds (trace_len t0) request_id)
  (ensures fun t0 resp t1 ->
        all_elements_of_http_response_are_publishable app_preds (trace_len t1) resp /\
        (match DY.Crypto.split resp.resp_body with
         | Success (token, account_pubkey) ->(
            client_has_account_public_key client account_pubkey (trace_len t1)
           )
         | _ -> False
        )
   )


