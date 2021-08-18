/// ACME.Client.ChallengeResponse (implementation)
/// ==============================================
module ACME.Client.ChallengeResponse

open Helpers
open DY.Monad
open Web.Messages
open DY.Labels
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open ACME.Data
open Application.Predicates
friend Application.Predicates
open SerializationHelpers
open SerializationLemmas

open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open ACME.Client.HelperFunctions

#set-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let _acme_client_challenge_response client idx_acc idx_authz request_id =
  let (|i, v, state|) = get_last_state client in
     if idx_acc < Seq.length state && idx_authz < Seq.length state then(
       let ss_acc_st = state.[idx_acc] in
       let ss_authz_st = state.[idx_authz] in
       match parse_acme_client_state ss_acc_st,
             parse_acme_client_state ss_authz_st  with
       | Success (Account acc_priv_key acc_url order_url),
         Success (ACMEAuthorziation authorization idx_order) -> (
           if Seq.length authorization.acme_authorization_challenges > 0 then(
             //use the first challenge in the list
             let challenge = get_challenge_i_from_authorization authorization 0 in
             let token = challenge.acme_challenge_token in
             assert(is_publishable_p app_preds i (serialize_acme_authorization authorization));
             challenge_of_publishable_acme_authorization_is_publishable i authorization challenge;
             token_of_publishable_challenge_is_publishable i challenge;
             assert(is_publishable_p app_preds i token);
             //assert(valid_acme_client_st state i app_preds client (Account acc_priv_key acc_url order_url));
             assert(is_sign_key_p app_preds i acc_priv_key (readable_by (readers [any client]))  (acme_sig_key_usage (readers [any client]) app_preds));
             let account_pubkey = vk #i  #(readable_by (readers [any client])) #(acme_sig_key_usage (readers [any client]) app_preds) acc_priv_key in
             assert(is_publishable_p app_preds i account_pubkey);
             let token':msg_at i public = token in
             let account_pubkey':msg_at i public = account_pubkey in
             let key_authz = concat #i  #public token' account_pubkey' in
             let http_resp:http_response ={
               resp_req_id = request_id;
               resp_status = HTTP_STATUS_200_OK;
               resp_headers = Seq.empty #http_header;
               resp_body = key_authz
             } in
             assert(Seq.length http_resp.resp_headers = 0);
             serialization_empty_sequence_http_header_is_publishable app_preds i http_resp.resp_headers;
             assert(Success? (DY.Crypto.split key_authz));

             assert( client_has_account_public_key client account_pubkey i);
             get_challenge_i_from_authorization_lemma authorization 0;
             assert(match DY.Crypto.split http_resp.resp_body with
               | Success (token, account_pubkey) ->(
                      client_has_account_public_key client account_pubkey i
                      )
               | _ -> False
              );
             http_resp
           )else error "No pending challenges in authorization"
         )
       | _ -> error "Authz index does not point to a valid ACMEAuthorziation session"
     )else error "Invalid Authz or Account session index"



