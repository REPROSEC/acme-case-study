/// ACME.Client.TriggerChallenge (implementation)
/// =============================================
module ACME.Client.TriggerChallenge

open Helpers
open DY.Monad
open DY.Entry
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.Labels
open Labeled.ApplicationAPI
open Labeled.Crypto
open Web.Messages
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open Application.Predicates
friend Application.Predicates
open FStar.Seq.Base

open SerializationHelpers
open FStar.String
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open ACME.Client.HelperLemmas
open ACME.Client.HelperFunctions

#push-options "--z3rlimit 10"
let _acme_client_receive_authorization_save_state client authorization idx_order =
    let  (|i, v, state|) = get_last_state client in
    if idx_order < Seq.length state &&
       Seq.length authorization.acme_authorization_challenges > 0
    then (
      let ss_order_st = state.[idx_order] in
      match parse_acme_client_state ss_order_st with
      | Success (ACMEOrder order acc_idx _) -> (
         if is_updated_order order &&
            Seq.mem authorization.acme_authorization_identifier order.acme_order_identifiers
         then(
            (*  save the new state session ACMEAuthorziation    *)
            let acme_authz_ss = ACMEAuthorziation authorization idx_order in
            let ss_authz = (serialize_acme_client_state acme_authz_ss) in
            let v_authz = Seq.snoc v 0 in
            let st_authz = Seq.snoc state ss_authz in
            let len_now = current_trace_len () in
            add_valid_client_session_state_preserves_state_inv len_now client v state acme_authz_ss;
            //let st_authz':app_state len_now client v_authz = st_authz in
            set_state client v_authz st_authz;
            let num_of_challenges = Seq.length authorization.acme_authorization_challenges in
            (Seq.length v, num_of_challenges)
          )else error "fail to save ACMEAuthorziation session"
        )
      | _ -> error "fail to save ACMEAuthorziation session"
    )else error "fail to save ACMEAuthorziation session"
#pop-options

private val gen_jws_req_helper:
  client:principal ->
  tr_idx:nat ->
  acc_priv_key:bytes{is_sign_key_p app_preds tr_idx acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds)} ->
  acc_url:url{is_publishable_p app_preds tr_idx (serialize_url acc_url)} ->
  challenge_url:url{is_publishable_p app_preds tr_idx (serialize_url challenge_url)} ->
  replay_nonce:bytes{is_publishable_p app_preds tr_idx replay_nonce} ->
  jws_req: jws_acme_request{is_publishable_p app_preds tr_idx (serialize_jws_acme_request jws_req)}

#push-options "--max_fuel 4 --max_ifuel 2 --z3rlimit 100"
let gen_jws_req_helper client tr_idx acc_priv_key acc_url challenge_url replay_nonce =
  let payload =  string_to_bytes app_preds tr_idx "{}" in
  generate_message_for_jws_signature_structure app_preds acc_url challenge_url replay_nonce payload;
   assert(
           match DY.Crypto.split (generate_message_for_jws_signature acc_url challenge_url replay_nonce payload) with
             | Success (nonce_bytes, snd_part) -> (
                match  DY.Crypto.split snd_part with
                  | Success (keyID_bytes, snd_part) -> (
                    match DY.Crypto.split snd_part with
                    | Success (url_bytes, payload_bytes) -> (
                      match parse_acme_csr payload_bytes with
                      | Success csr ->  False
                      | _ -> True //other signing cases
                      )
                    | _ -> False
                    )
                  | _ -> False
                )
               | _ -> False
             ); 
  assert(acme_sign_pred  (readers [any client]) app_preds tr_idx (generate_message_for_jws_signature acc_url challenge_url replay_nonce payload));
  let jws_req = generate_jws_acme_request app_preds tr_idx (acme_sig_key_usage (readers [any client]) app_preds) acc_url challenge_url replay_nonce payload acc_priv_key (readable_by (readers [any client])) in 
  elements_of_jws_acme_request_are_publishable_implies_jws_request_is_publishable app_preds tr_idx acc_url challenge_url replay_nonce payload acc_priv_key (readers [any client]);
  jws_req
#pop-options 

private val gen_http_request_helper:
  client:principal ->
  acc_priv_key:bytes ->
  request_nonce:bytes ->
  authorization: acme_authorization ->
  acc_url:url ->
  replay_nonce:bytes->
  challenge_idx:nat ->
  i:nat ->
  len_now:nat ->
  Pure (http_request * principal)
  (requires
     later i len_now /\
     challenge_idx < Seq.length (authorization.acme_authorization_challenges) /\
     is_publishable_p app_preds i (serialize_acme_authorization authorization) /\
     is_publishable_p app_preds i request_nonce /\
     is_publishable_p app_preds i replay_nonce /\
     is_publishable_p app_preds i (serialize_url acc_url) /\
     is_sign_key_p app_preds i acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds)
  )
  (ensures
     fun (req, _) -> all_elements_of_http_request_are_publishable app_preds len_now req
  )

#push-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 500"
let gen_http_request_helper client acc_priv_key request_nonce authorization acc_url replay_nonce challenge_idx i len_now =
  let challenge = get_challenge_i_from_authorization authorization challenge_idx in
  challenge_of_publishable_acme_authorization_is_publishable i authorization challenge;
  url_and_token_of_publishable_challenge_are_publishable i challenge;
  let challenge_url = challenge.acme_challenge_url in
  let challenge_dom = challenge_url.url_domain in
  let server = domain_principal_mapping challenge_dom in
  let jws_req = gen_jws_req_helper client i acc_priv_key acc_url challenge_url replay_nonce in
  let req_header = generate_request_header_host_domain challenge_dom in
  request_header_host_domain_is_publishable i challenge_dom;
  url_is_publishable_implies_request_uri_is_publishable app_preds i challenge_url;
  let http_req:http_request = {
      req_id = request_nonce;
      req_method = HTTP_METHOD_POST;
      req_uri = challenge_url.url_request_uri;
      req_headers = req_header;
      req_body = serialize_jws_acme_request jws_req
  }in
  assert(all_elements_of_http_request_are_publishable app_preds i http_req);
  all_elements_of_http_request_are_publishable_later_lemma app_preds i http_req;
  (http_req, server)
#pop-options

#push-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 500"
let _acme_client_triggers_challenge_i client idx_authz challenge_idx =
      let (|idx, request_nonce|) = guid_gen () in
      assert(is_publishable_p app_preds idx request_nonce);
      let (|i, v, state|) = get_last_state client in
      if idx_authz < Seq.length state then (
        match parse_acme_client_state state.[idx_authz] with
        | Success (ACMEAuthorziation authorization idx_order) -> (
            if idx_order < Seq.length state &&
               challenge_idx < Seq.length (authorization.acme_authorization_challenges)
            then(
              match parse_acme_client_state state.[idx_order] with
              | Success (ACMEOrder order idx_acc _) -> (
                  if is_updated_order order && idx_acc < Seq.length state then(
                    match parse_acme_client_state state.[idx_acc] with
                    | Success (Account acc_priv_key acc_url order_url) -> (
                        let challenge = get_challenge_i_from_authorization authorization challenge_idx in  
                        let challenge_url = challenge.acme_challenge_url in
                        let challenge_dom = challenge_url.url_domain in
                        match client_finds_valid_replay_nonce i client v state challenge_dom with
                        |Success replay_nonce -> (
                          assert(is_sign_key_p app_preds i acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));
                          assert(later idx i);
                          is_publishable_p_later_lemma app_preds idx request_nonce;
                          assert(is_publishable_p app_preds i request_nonce);
                          flows_to_public_can_flow (app_preds.model.corrupt_at i) (get_label request_nonce)  (readable_by (readers [any client]));
                          let pen_req_ss = HTTPSPendingRequest request_nonce idx_authz challenge_dom in //the reference points to the session ACMEAuthorization added above
                          let v_req_ss = Seq.snoc v 0 in
                          let st_pen_req = Seq.snoc state (serialize_acme_client_state pen_req_ss) in
                          add_valid_client_session_state_preserves_state_inv i client v state pen_req_ss;
                          //assert(is_principal_state_readable client v_req_ss st_pen_req);
                          //let st':app_state i client v_req_ss = st_pen_req in
                          set_state client v_req_ss st_pen_req;
                          let len_now = current_trace_len () in
                          assert(later i len_now);
                          assert(is_publishable_p app_preds i (serialize_acme_authorization authorization));
                          assert(is_publishable_p app_preds i (serialize_url acc_url));

                          let (http_req, server) = gen_http_request_helper client acc_priv_key request_nonce authorization acc_url replay_nonce challenge_idx i len_now in
                          (http_req, server, replay_nonce)
                        )
                        | _ -> error "there is no replay nonce to send request"
                      )
                    | _ -> error "fail to send http request triggering challenge"
                  )else error "fail to send http request triggering challenge"
                )
              | _ -> error "fail to send http request triggering challenge"
            )else error "fail to send http request triggering challenge"
          )
        | _ -> error "fail to send http request triggering challenge"
      )else error "fail to send http request triggering challenge"

#pop-options
