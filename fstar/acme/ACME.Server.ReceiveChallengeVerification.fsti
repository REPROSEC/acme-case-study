/// ACME.Server.ReceiveChallengeVerification
/// =========================================
module ACME.Server.ReceiveChallengeVerification

open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Monad
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open HelperFunctions
open Application.Predicates
open SerializationHelpers

// Step 8 of the protocol description in acme.md
val _acme_server_receive_challenge_verification:
      server:principal ->
      response:http_response ->
      sender_of_response:principal ->
      index_of_send_event:nat{
        authenticated_send_pred index_of_send_event sender_of_response server (serialize_http_response response) \/ //honest sender: predicate must hold true
        is_principal_corrupted_before index_of_send_event sender_of_response
      } ->
      DYL unit
         (requires (fun t0 ->
           index_of_send_event < trace_len t0 /\
           is_publishable_p app_preds (trace_len t0) (serialize_http_response response) /\
           is_publishable_p app_preds index_of_send_event (serialize_http_response response)
         ))
         (ensures (fun _ _ _ -> True))

(**
Faulty version of  _acme_server_receive_challenge_verification:
 servers checks if there is ONE authorization has been verified successfully (the status is Valid),
 if yes, then it sets the status of order to be Ready
*)
val _acme_server_receive_challenge_verification_faulty:
      server:principal ->
      response:http_response ->
      sender_of_response:principal ->
      index_of_send_event:nat{
        authenticated_send_pred index_of_send_event sender_of_response server (serialize_http_response response) \/ //honest sender: predicate must hold true
        is_principal_corrupted_before index_of_send_event sender_of_response
      } ->
      DYL unit
         (requires (fun t0 ->
           index_of_send_event < trace_len t0 /\
           is_publishable_p app_preds (trace_len t0) (serialize_http_response response) /\
           is_publishable_p app_preds index_of_send_event (serialize_http_response response)
         ))
         (ensures (fun _ _ _ -> True))
