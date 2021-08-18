/// ACME.Server.ReceiveChallengeVerification (implementation)
/// ==========================================================
module ACME.Server.ReceiveChallengeVerification

open FStar.Tactics

open Labeled.Crypto
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open DY.Entry
open DY.Monad
open Labeled.ApplicationAPI
open Application.Predicates.Helpers
open Application.Predicates.Helpers
open Application.Predicates
friend Application.Predicates
open Application.Predicates.Lemmas
open ACME.Data
open ACME.Data.SerializationHelpers
open Helpers

open SerializationHelpers
open SerializationLemmas
open ACME.Server.HelperFunctions

open ACME.Data.SerializationLemmas
open ACME.Data.Predicates
open FStar.Seq

val lookup_processing_challenge_by_http_request_id:
  #server:principal ->
  http_request_id:bytes ->
  state_trace_idx:nat ->
  current_session_id:nat ->
  current_version_vec:version_vec ->
  current_app_state:app_state state_trace_idx server current_version_vec{state_inv state_trace_idx server current_version_vec current_app_state} ->
  Tot (option ( processing_challenge_session_id:nat{processing_challenge_session_id < Seq.length current_version_vec} &
                authorization_sessionid:nat{authorization_sessionid < Seq.length current_version_vec} &
                challenge_idx:nat))
  (decreases ((Seq.length current_version_vec) - current_session_id))

let rec lookup_processing_challenge_by_http_request_id #server http_request_id state_trace_idx current_session_id current_version_vec current_app_state =
  if Seq.length current_version_vec <= current_session_id then
    None
  else (
    match parse_acme_server_state (current_app_state.[current_session_id]),
          parse_acme_client_state (current_app_state.[current_session_id]) with
    | Success st, Error _ -> (
      match st with
      | ProcessingChallenge authorization_sessionid challenge_idx http_request_id' -> (
        if eq_bytes http_request_id http_request_id' &&
          authorization_sessionid < Seq.length current_version_vec then
          Some (|current_session_id, authorization_sessionid, challenge_idx|)
        else
          lookup_processing_challenge_by_http_request_id http_request_id state_trace_idx (current_session_id + 1) current_version_vec current_app_state
        )
        | _ -> lookup_processing_challenge_by_http_request_id http_request_id state_trace_idx (current_session_id + 1) current_version_vec current_app_state
      )
    | Error _, Success st -> lookup_processing_challenge_by_http_request_id http_request_id state_trace_idx (current_session_id + 1) current_version_vec current_app_state
    |_ ->  lookup_processing_challenge_by_http_request_id http_request_id state_trace_idx (current_session_id + 1) current_version_vec current_app_state
  )


val client_has_account_public_key_implies_owner_of_account_pub_key:
  authz_msg_send_idx: nat ->
  client:principal ->
  pubkey:bytes{is_publishable_p app_preds authz_msg_send_idx pubkey} ->
  DYL unit
  (requires fun h -> authz_msg_send_idx < trace_len h)
  (ensures fun h0 _ h1 ->
    h0 == h1 /\
    (client_has_account_public_key client pubkey authz_msg_send_idx ==>
      is_verify_key_p app_preds authz_msg_send_idx pubkey (readable_by_any1 client) (acme_sig_key_usage (readers [any client]) app_preds)
    ))


let client_has_account_public_key_implies_owner_of_account_pub_key tr_idx client pubkey =
  assert(client_has_account_public_key client pubkey tr_idx ==>
   ( exists (v_acc:version_vec) (st_acc:principal_state) (set_acc_idx:nat) (acc_sessionid:nat).
       is_set_state_at set_acc_idx client v_acc st_acc /\
       set_acc_idx < tr_idx /\
       acc_sessionid < Seq.length st_acc /\
       ( match parse_acme_client_state st_acc.[acc_sessionid] with
         | Success (Account acc_priv_key acc_url order_url) ->(
                DY.Crypto.pk acc_priv_key == pubkey
           )
         | _ -> False
       )
   )
  );

  assert(client_has_account_public_key client pubkey tr_idx ==>
   ( exists (v_acc:version_vec) (st_acc:principal_state) (set_account_idx:nat) (acc_sessionid:nat).
       state_inv set_account_idx client v_acc st_acc /\
       acc_sessionid < Seq.length st_acc /\
       ( match parse_acme_client_state st_acc.[acc_sessionid] with
         | Success (Account acc_priv_key acc_url order_url) ->(
                DY.Crypto.pk acc_priv_key == pubkey
           )
         | _ -> False
       )
   )
  );
  assert(client_has_account_public_key client pubkey tr_idx ==>
   ( exists (v_acc:version_vec) (st_acc:principal_state) (set_account_idx:nat) (acc_sessionid:nat).
       state_inv set_account_idx client v_acc st_acc /\
       acc_sessionid < Seq.length st_acc /\
       ( match parse_acme_client_state st_acc.[acc_sessionid] with
         | Success (Account acc_priv_key acc_url order_url) ->(
                DY.Crypto.pk acc_priv_key == pubkey /\
                is_sign_key_p app_preds tr_idx acc_priv_key (readable_by_any1 client) (acme_sig_key_usage (reader_any1 client) app_preds)
           )
         | _ -> False
       )
   )
  );
  assert(client_has_account_public_key client pubkey tr_idx ==>
   ( exists (v_acc:version_vec) (st_acc:principal_state) (set_account_idx:nat) (acc_sessionid:nat).
       state_inv set_account_idx client v_acc st_acc /\
       acc_sessionid < Seq.length st_acc /\
       ( match parse_acme_client_state st_acc.[acc_sessionid] with
         | Success (Account acc_priv_key acc_url order_url) ->(
                DY.Crypto.pk acc_priv_key == pubkey /\
                is_secret_p app_preds tr_idx acc_priv_key (readable_by_any1 client) DY.Crypto.sig_key_usage (acme_sig_key_usage (reader_any1 client) app_preds) 
           )
         | _ -> False
       )
   )
  );
  assert(client_has_account_public_key client pubkey tr_idx ==>
   ( exists (v_acc:version_vec) (st_acc:principal_state) (set_account_idx:nat) (acc_sessionid:nat).
       state_inv set_account_idx client v_acc st_acc /\
       acc_sessionid < Seq.length st_acc /\
       ( match parse_acme_client_state st_acc.[acc_sessionid] with
         | Success (Account acc_priv_key acc_url order_url) ->(
                DY.Crypto.pk acc_priv_key == pubkey /\
                is_secret_p app_preds tr_idx acc_priv_key (readable_by_any1 client) DY.Crypto.sig_key_usage (acme_sig_key_usage (reader_any1 client) app_preds) /\
                is_public_key_p app_preds tr_idx pubkey (readable_by_any1 client) DY.Crypto.sig_key_usage (acme_sig_key_usage (reader_any1 client) app_preds)                
           )
         | _ -> False
       )
   )
  );
   assert(client_has_account_public_key client pubkey tr_idx ==>
   is_verify_key_p app_preds tr_idx pubkey (readable_by_any1 client) (acme_sig_key_usage (reader_any1 client) app_preds)
  )




#push-options "--z3rlimit 600 --max_fuel 1 --max_ifuel 1 --initial_ifuel 1 --initial_fuel 1"
let _acme_server_receive_challenge_verification server response sender_of_response send_event_idx =
  let trace_index = current_trace_len () in
  let (|trace_index_of_last_set_state, current_version_vec, current_app_state|) = get_last_state server in
  // check if the response belongs to some request that the server sent out
  match lookup_processing_challenge_by_http_request_id #server response.resp_req_id trace_index_of_last_set_state 0 current_version_vec current_app_state with
  | None -> ()
  | Some (|processing_challenge_sessionid, authorization_sessionid, challenge_idx|) -> (
    assert(authorization_sessionid < Seq.length current_version_vec) by smt ();
    match parse_acme_server_state (current_app_state.[authorization_sessionid]), parse_acme_client_state (current_app_state.[authorization_sessionid])  with
    | Success st, Error _ -> (
      match st with
      | Authorization authorization_url authorization order_sessionid -> (
        //check if the response was sent by the owner of the domain
        if (domain_principal_mapping authorization.acme_authorization_identifier <> sender_of_response) ||
           challenge_idx >= Seq.length (authorization.acme_authorization_challenges) ||
           order_sessionid >= Seq.length current_version_vec
        then
          ()
        else (
          let challenge = Seq.index (authorization.acme_authorization_challenges) challenge_idx in
          assert(order_sessionid < Seq.length current_version_vec);
          match parse_acme_server_state (current_app_state.[order_sessionid]) with
          | Success st' -> (
            match st' with
            | Order order user_account_sessionid acc_url acc_pub_key seq_authz_info ->
              let expected_key_authorization = DY.Crypto.concat challenge.acme_challenge_token acc_pub_key in // see Section 8.1 in RFC8555
              let identifier = authorization.acme_authorization_identifier  in
              if eq_bytes response.resp_body expected_key_authorization &&
                 Seq.mem identifier order.acme_order_identifiers
              then (
                assert(
                  authenticated_send_pred send_event_idx sender_of_response server (serialize_http_response response) \/ //honest sender: predicate must hold true
                  is_principal_corrupted_before send_event_idx sender_of_response
                ) by smt ();
                eq_bytes_concat_split_lemma challenge.acme_challenge_token acc_pub_key response.resp_body;
                let Success (token, pub_key) = DY.Crypto.split response.resp_body in
                assert(eq_bytes pub_key acc_pub_key);
                parse_http_response_lemma response;
                assert(~(client_has_account_public_key sender_of_response pub_key send_event_idx) ==> contains_corrupt_principal (corrupt_at send_event_idx) (reader_any1 sender_of_response)) by (set_options "--initial_fuel 1 --initial_fuel 1 --z3rlimit 800"; smt ());
                assert(
                  client_has_account_public_key sender_of_response pub_key send_event_idx \/
                  contains_corrupt_principal (corrupt_at send_event_idx) (reader_any1 sender_of_response)
                ) by smt ();
                http_response_is_publishable_implies_body_is_publishable app_preds send_event_idx response;
                assert(is_publishable_p app_preds send_event_idx response.resp_body) by smt ();
                concatenation_publishable_implies_components_publishable_forall app_preds;
                assert(is_publishable_p app_preds send_event_idx pub_key) by smt ();
                let t = get () in
                assert(send_event_idx < trace_len t);
                assert(later send_event_idx trace_index);
                is_labeled_later_forall app_preds;
                client_has_account_public_key_implies_owner_of_account_pub_key send_event_idx sender_of_response pub_key;
                assert(
                  is_verify_key_p app_preds trace_index pub_key (readable_by_any1 sender_of_response) (acme_sig_key_usage (reader_any1 sender_of_response) app_preds) \/
                  contains_corrupt_principal (corrupt_at trace_index) (readers [any sender_of_response])
                ) by smt ();
                assert(is_valid_p app_preds trace_index pub_key);
                assert(is_valid_p app_preds trace_index acc_pub_key);
                assert(pub_key == acc_pub_key); 
                assert(owner_of_domain_owns_public_key_or_corrupted app_preds trace_index identifier acc_pub_key); //prove from authenticated_send_pred
                let updated_seq_authz_info = set_valid_for_identifier_in_order trace_index order seq_authz_info acc_pub_key identifier in
                assert(is_publishable_p app_preds trace_index (serialize_acme_order order));
                let updated_order = check_valid_and_set_ready_for_order trace_index order updated_seq_authz_info acc_pub_key in
                let updated_order_session = Order updated_order user_account_sessionid acc_url acc_pub_key updated_seq_authz_info in
                let updated_order_st = serialize_acme_server_state updated_order_session in
                let new_app_state = current_app_state.[order_sessionid] <- updated_order_st in
                assert(is_valid_Order_session app_preds trace_index updated_order updated_seq_authz_info acc_pub_key);
                assert(state_inv trace_index server current_version_vec current_app_state);
                assert(is_publishable_p app_preds trace_index (serialize_url acc_url));
                assert(is_publishable_p app_preds trace_index acc_pub_key);
                assert(is_publishable_p app_preds trace_index (serialize_acme_order updated_order));
                assert(valid_acme_server_st app_preds trace_index server updated_order_session);
                state_invariant_remains_true_if_true_for_updated_server_state trace_index current_app_state updated_order_st server current_version_vec order_sessionid;
                assert(state_inv trace_index server current_version_vec new_app_state);
                state_inv_implies_principal_state_readable trace_index server current_version_vec new_app_state;
                set_state server current_version_vec new_app_state
              ) else () // key authorization failed!
            | _ -> ()
            )
          | Error _ -> ()
          )
        )
      | _ -> ()
      )
    | Error _, Success sti -> ()
    | _ -> ()
  )
#pop-options


#push-options "--z3rlimit 600 --max_fuel 1 --max_ifuel 1 --initial_ifuel 1 --initial_fuel 1"
let _acme_server_receive_challenge_verification_faulty server response sender_of_response send_event_idx =
  let trace_index = current_trace_len () in
  let (|trace_index_of_last_set_state, current_version_vec, current_app_state|) = get_last_state server in
  // check if the response belongs to some request that the server sent out
  match lookup_processing_challenge_by_http_request_id #server response.resp_req_id trace_index_of_last_set_state 0 current_version_vec current_app_state with
  | None -> ()
  | Some (|processing_challenge_sessionid, authorization_sessionid, challenge_idx|) -> (
    assert(authorization_sessionid < Seq.length current_version_vec) by smt ();
    match parse_acme_server_state (current_app_state.[authorization_sessionid]) with
    | Success st -> (
      match st with
      | Authorization authorization_url authorization order_sessionid -> (
        //check if the response was sent by the owner of the domain
        if (domain_principal_mapping authorization.acme_authorization_identifier <> sender_of_response) ||
           challenge_idx >= Seq.length (authorization.acme_authorization_challenges) ||
           order_sessionid >= Seq.length current_version_vec
        then
          ()
        else (
          let challenge = Seq.index (authorization.acme_authorization_challenges) challenge_idx in
          assert(order_sessionid < Seq.length current_version_vec);
          match parse_acme_server_state (current_app_state.[order_sessionid]) with
          | Success st' -> (
            match st' with
            | Order order user_account_sessionid acc_url acc_pub_key seq_authz_info ->
              let expected_key_authorization = DY.Crypto.concat challenge.acme_challenge_token acc_pub_key in // see Section 8.1 in RFC8555
              let identifier = authorization.acme_authorization_identifier  in
              if eq_bytes response.resp_body expected_key_authorization &&
                 Seq.mem identifier order.acme_order_identifiers
              then (
                assert(
                  authenticated_send_pred send_event_idx sender_of_response server (serialize_http_response response) \/ //honest sender: predicate must hold true
                  is_principal_corrupted_before send_event_idx sender_of_response
                );
                eq_bytes_concat_split_lemma challenge.acme_challenge_token acc_pub_key response.resp_body;
                let Success (token, pub_key) = DY.Crypto.split response.resp_body in
                assert(eq_bytes pub_key acc_pub_key) by (smt ());
                parse_http_response_lemma response;
                assert(~(client_has_account_public_key sender_of_response pub_key send_event_idx) ==> contains_corrupt_principal (corrupt_at send_event_idx) (reader_any1 sender_of_response)) by smt ();
                assert(
                  client_has_account_public_key sender_of_response pub_key send_event_idx \/
                  contains_corrupt_principal (corrupt_at send_event_idx) (reader_any1 sender_of_response)
                ) by (prune ""; smt ());
                assert(is_publishable_p app_preds send_event_idx (serialize_http_response response)) by prune "";
                http_response_is_publishable_implies_body_is_publishable app_preds send_event_idx response;
                assert(is_publishable_p app_preds send_event_idx response.resp_body) by smt ();
                concatenation_publishable_implies_components_publishable_forall app_preds;
                assert(is_publishable_p app_preds send_event_idx pub_key) by smt ();
                assert(later send_event_idx trace_index);
                is_labeled_later_forall app_preds;
                client_has_account_public_key_implies_owner_of_account_pub_key send_event_idx sender_of_response pub_key;
                assert(
                  is_verify_key_p app_preds trace_index pub_key (readable_by_any1 sender_of_response) (acme_sig_key_usage (reader_any1 sender_of_response) app_preds) \/
                  contains_corrupt_principal (corrupt_at trace_index) (readers [any sender_of_response])
                ) by smt ();
                assert(is_valid_p app_preds trace_index pub_key);
                assert(is_valid_p app_preds trace_index acc_pub_key);
                assert(pub_key == acc_pub_key); 
                assert(owner_of_domain_owns_public_key_or_corrupted app_preds trace_index identifier acc_pub_key); //prove from authenticated_send_pred
                let updated_seq_authz_info = set_valid_for_identifier_in_order trace_index order seq_authz_info acc_pub_key identifier in
                assert(is_publishable_p app_preds trace_index (serialize_acme_order order));               
                print_string "receivechallengeverification - before checking valid\n";
                // BUG here (on purpose): We use the faulty function to check validity of the order.
                let updated_order = check_valid_and_set_ready_for_order_faulty trace_index order updated_seq_authz_info acc_pub_key in
                let updated_order_session = Order updated_order user_account_sessionid acc_url acc_pub_key updated_seq_authz_info in
                let updated_order_st = serialize_acme_server_state updated_order_session in
                let new_app_state = current_app_state.[order_sessionid] <- updated_order_st in
                assert(is_valid_Order_session app_preds trace_index updated_order updated_seq_authz_info acc_pub_key);
                assert(state_inv trace_index server current_version_vec current_app_state);
                assert(is_publishable_p app_preds trace_index (serialize_url acc_url));
                assert(is_publishable_p app_preds trace_index acc_pub_key);
                assert(is_publishable_p app_preds trace_index (serialize_acme_order updated_order));
                assert(valid_acme_server_st app_preds trace_index server updated_order_session);
                state_invariant_remains_true_if_true_for_updated_server_state trace_index current_app_state updated_order_st server current_version_vec order_sessionid;
                assert(state_inv trace_index server current_version_vec new_app_state);
                state_inv_implies_principal_state_readable trace_index server current_version_vec new_app_state;
                set_state server current_version_vec new_app_state;
                print_string "receivechallengeverification - state has been updated\n"
              ) else (
                print_string "receivechallengeverification - error 1\n"
              ) // key authorization failed!
            | _ -> (print_string "receivechallengeverification - error 2\n")
            )
          | Error _ -> (print_string "receivechallengeverification - error 3\n")
          )
        )
      | _ -> (print_string "receivechallengeverification - error 4\n")
      )
    | Error _ -> (print_string "receivechallengeverification - error 5\n")
  )
#pop-options
