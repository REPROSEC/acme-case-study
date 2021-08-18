/// ACME.Server.ChallengeResponse (implementation)
/// ===============================================
module ACME.Server.ChallengeResponse

open Helpers
open DY.Monad
open Labeled.Crypto
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Labeled.ApplicationAPI
open Application.Predicates.Helpers
open Application.Predicates
friend Application.Predicates
open Application.Predicates.Lemmas
open ACME.Data
open ACME.Data.SerializationHelpers


open SerializationHelpers
open SerializationLemmas

open ACME.Server.HelperFunctions

open ACME.Data.SerializationLemmas

open FStar.Seq

#set-options "--initial_fuel 0 --initial_ifuel 0"

(**
  Helper function creating the response for [_acme_server_challenge_response].
*)
let _acme_server_challenge_response_create_response
  (tr_idx: nat)
  (req_id:bytes{is_publishable_p app_preds tr_idx req_id})
  (body:bytes{is_publishable_p app_preds tr_idx body})
: Tot (response:http_response{
        is_publishable_p app_preds tr_idx (serialize_http_response response)
      })
  =
    let response = {
      resp_req_id = req_id;
      resp_status = HTTP_STATUS_200_OK;
      resp_headers = Seq.empty; 
      resp_body = body
    } in
    assert(all_elements_of_http_response_are_publishable app_preds tr_idx response);
    label_of_http_response_can_flow_to_public app_preds tr_idx response;
    response


#push-options "--z3rlimit 150 --max_ifuel 0 --initial_ifuel 0 --max_fuel 1 --initial_fuel 1"

(*
Happy path according to p. 53 of RFC8555:
1) We expect an empty (since we only look at HTTP01 and DNS01 challenges) payload of the jws
2) Find a pending authz object which contains a challenge with the target URL (as challenge URL)
3) Update that object (the challenge inside the authz object) with the payload of the jws
   => for HTTP01 and DNS01 challenges, nothing is updated, so the server only changes the status of the
      challenge to "processing" (sec. 7.1.6).
4) Store that updated authz object (overwriting the old one).
5) Answer with HTTP 200 and the updated challenge object
*)
let _acme_server_challenge_response acme_server_principal request =
  match parse_jws_acme_request request.req_body with
  | Error _  -> error "server fails to generate challenge response"
  | Success jws_acme_request_object -> (
      let len_now1 = current_trace_len () in
      concatenation_publishable_implies_components_publishable_forall app_preds;
      assert(is_publishable_p app_preds len_now1 request.req_body);
      serialize_parse_jws_acme_request_publishability_lemma app_preds len_now1 request.req_body;
      assert(is_publishable_p app_preds len_now1 (serialize_jws_acme_request jws_acme_request_object));
      if (dfst (verify_jws_acme_request len_now1 request acme_server_principal jws_acme_request_object)) then (
         let challenge_url = jws_acme_request_object.url in
         let (|i, v, current_state|)= get_last_state acme_server_principal in
         // Find the challenge/authz_object corresponding to challenge_url in state
         assert(later len_now1 i);
         match retrieve_authz_by_challenge_url_from_server_st i acme_server_principal challenge_url 0 v current_state with
         | None -> error "404: server fails to generate challenge response"  
         | Some (authz_object, authz_session_idx, challenge_index) -> (
            // Status should be pending
             //      (spec on p. 53 is unclear about the exact code to use)
             if authz_object.acme_authorization_status <> Pending then
                error "server fails to generate challenge response"
             else (
                let Success (Authorization authorization_url azo order_sess_idx) = parse_acme_server_state current_state.[authz_session_idx] in
                // Update the challenge inside the authz object
                let old_challenge = authz_object.acme_authorization_challenges.[challenge_index] in
                let new_challenge = {old_challenge with acme_challenge_status = Processing} in
                let new_authz_object = {
                  authz_object with
                  acme_authorization_challenges = authz_object.acme_authorization_challenges.[challenge_index] <- new_challenge
                } in
                // Store the modified authz object
                let updated_authz_st = Authorization authorization_url new_authz_object order_sess_idx in
                let updated_authz_session = serialize_acme_server_state updated_authz_st in
                let new_state = current_state.[authz_session_idx] <- updated_authz_session in
                // We only changed the status of one challenge, nothing else ...
                assert(can_label_of_bytes_flow_to app_preds i (serialize_acme_authorization authz_object) public);
                serialized_updated_acme_authorization_flows_to_public i authz_object challenge_index;
                assert(can_label_of_bytes_flow_to app_preds i (serialize_acme_authorization new_authz_object) public);
                assert(valid_acme_server_st app_preds i acme_server_principal (Success?.v (parse_acme_server_state updated_authz_session)));
                state_with_updated_valid_session_is_still_readable_by_server i acme_server_principal v current_state updated_authz_session authz_session_idx;
                assert(is_session_state_readable i acme_server_principal authz_session_idx v.[authz_session_idx] updated_authz_session);
                //let len_now = current_trace_len() in
                assert((Success? (parse_acme_server_state updated_authz_session)));
                assert(valid_acme_server_st app_preds i acme_server_principal (Success?.v (parse_acme_server_state updated_authz_session)));
                state_invariant_remains_true_if_true_for_updated_server_state i current_state updated_authz_session acme_server_principal v authz_session_idx;
                assert(state_inv i acme_server_principal v new_state);
                state_inv_implies_principal_state_readable i acme_server_principal v new_state;
                ///important place: here the trace is changed
                set_state acme_server_principal v new_state;
                // Respond with the updated challenge object
                let len_now = current_trace_len() in
                assert(later i len_now);
                later_is_transitive len_now1 i len_now;
                is_publishable_p_later_lemma app_preds len_now1 (serialize_http_request request);
                http_request_is_publishable_implies_request_id_is_publishable app_preds len_now request;
                assert(is_publishable_p app_preds len_now request.req_id);
                is_publishable_p_later_lemma app_preds i (serialize_acme_authorization authz_object);
                serialized_acme_authorization_flows_to_public_implies_components_flow_to_public len_now authz_object;
                sequence_of_challenges_publishable_implies_single_challenge_publishable
                  len_now
                  authz_object.acme_authorization_challenges
                  challenge_index;
                assert(is_publishable_p app_preds len_now (serialize_acme_challenge old_challenge));
                serialized_updated_acme_challenge_flow_to_public len_now old_challenge;
                assert(is_publishable_p app_preds len_now (serialize_acme_challenge new_challenge));
                let response = _acme_server_challenge_response_create_response len_now request.req_id (serialize_acme_challenge new_challenge) in
                response
             )
          )
      ) else error "server fails to generate challenge response"
    )
#pop-options
