/// ACME.Server.TriggerChallengeVerification (implementation)
/// ==========================================================
module ACME.Server.TriggerChallengeVerification


module TacB = FStar.Tactics.Builtins
open FStar.Tactics

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
open Application.Predicates.Helpers
open ACME.Data
open ACME.Data.SerializationHelpers

open SerializationHelpers
open SerializationLemmas
open Helpers
open ACME.Server.HelperFunctions

open ACME.Data.SerializationLemmas

open FStar.Seq

val retrieve_acme_challenge_processing_from_server_st:
  trace_index:nat ->
  server:principal ->
  session_index:nat ->
  current_version_vec:version_vec ->
  current_app_state:app_state trace_index server current_version_vec ->
  Tot
  (option (
    session_idx:nat{session_idx < Seq.length current_version_vec} &
    authorization:acme_authorization{
      match parse_acme_server_state current_app_state.[session_idx] with
      | Success st -> (
        match st with
        | Authorization authorization_url authorization' order_sessionid -> authorization == authorization'
        | _ -> False
      )
      | _ -> False
    } &
    challenge_idx:nat &
    challenge:acme_challenge{
      challenge_idx < (Seq.length authorization.acme_authorization_challenges) /\
      authorization.acme_authorization_challenges.[challenge_idx] == challenge
    }
  ))
  (decreases ((Seq.length current_version_vec) - session_index))

let rec retrieve_acme_challenge_processing_from_server_st trace_index server session_index current_version_vec current_app_state =
  if Seq.length current_version_vec <= session_index then
    None
  else
    ( match parse_acme_server_state current_app_state.[session_index] with
      | Success st ->
        ( match st with
          | Authorization authorization_url authorization order_sessionid ->
            ( // get first processing challenge in this authorization
              match get_acme_challenge_processing_from_sequence authorization.acme_authorization_challenges 0 with
              | Some (|challenge_idx, challenge|) ->
                // check if the server already has sent out some HTTP request for this challenge
                if check_if_acme_challenge_processing_has_sent_out_verification_request trace_index server session_index challenge_idx 0 current_version_vec current_app_state then
                  ( // continue search for another challenge to verify
                    retrieve_acme_challenge_processing_from_server_st trace_index server (session_index + 1) current_version_vec current_app_state
                  )
                else
                  // the challenge found is unprocessed, i.e., we should send out a verification request
                  Some (|session_index, authorization, challenge_idx, challenge|)
              | _ -> // there is an authorization object at current_session_index, but it does not contain a challenge in status processing
                retrieve_acme_challenge_processing_from_server_st trace_index server (session_index + 1) current_version_vec current_app_state
            )
          | _ -> // there is no authorization object at the current session_index
            retrieve_acme_challenge_processing_from_server_st trace_index server (session_index + 1) current_version_vec current_app_state
        )
      | _ -> // there is nothing at the current session index that our parse function is able to interpret
        retrieve_acme_challenge_processing_from_server_st trace_index server (session_index + 1) current_version_vec current_app_state
    )



#push-options "--z3rlimit 100 --max_fuel 4 --max_ifuel 0 --initial_ifuel 0 --initial_fuel 4"
(**
    Helper function for [_acme_server_trigger_challenge_verification] for creating the request.
*)
let _acme_server_trigger_challenge_verification_create_request
    (trace_index:nat)
    (server:principal)
    (request_id:lbytes_at trace_index public)
    (challenge:acme_challenge{is_publishable_p app_preds trace_index (serialize_acme_challenge challenge)})
    (authorization:acme_authorization{is_publishable_p app_preds trace_index (serialize_acme_authorization authorization)})
  : Tot (req:http_request{is_publishable_p app_preds trace_index (serialize_http_request req)})
  =
    let path_list = [(string_to_bytes ".well-known"); (string_to_bytes "acme-challenge"); challenge.acme_challenge_token] in
    let header_list = [(string_to_bytes "Host", serialize_domain authorization.acme_authorization_identifier)] in
    let path = init_seq_bytes_with_list path_list in
    let headers = init_seq_with_list header_list in
    let querystring:Seq.seq (bytes * bytes) = Seq.empty in
    let uri:request_uri = {
      uri_path = path;
      uri_querystring = querystring;
      uri_fragment = None} in
    let req:http_request = {
      req_id = request_id;
      req_method = HTTP_METHOD_GET;
      req_uri = uri;
      req_headers = headers;
      req_body = (string_to_bytes "")} in

    concatenation_of_publishable_bytes_is_publishable_forall app_preds;
    concatenation_publishable_implies_components_publishable_forall app_preds;
    assert(is_publishable_p app_preds trace_index challenge.acme_challenge_token);

    assert(is_publishable_p app_preds trace_index (string_to_bytes "Host"));
    assert(is_publishable_p app_preds trace_index (serialize_domain authorization.acme_authorization_identifier));

    //path is publishable
    assert(is_publishable_p app_preds trace_index (string_to_bytes ".well-known"));
    assert(is_publishable_p app_preds trace_index (string_to_bytes "acme-challenge"));
    assert(is_publishable_p app_preds trace_index challenge.acme_challenge_token);
    init_seq_with_list_equivalence_of_list_and_sequence path_list;
    let a:(bytes -> Type) = fun el -> contains path el in
    let b:(bytes -> Type) = fun el -> List.Tot.memP el path_list in
    let c:(bytes -> Type) = fun el -> is_publishable_p app_preds trace_index el in
    assert(forall (el:bytes). a el <==> b el);
    assert(forall (el:bytes). b el ==> c el);
    assert(forall (el:bytes). a el ==> c el) by smt ();
    assert(is_publishable_p app_preds trace_index (serialize_sequence_of_bytes path)) by (apply_lemma (`SerializationLemmas.serialized_sequence_of_bytes_publishable_if_all_elements_publishable));

    //uri is publishable
    assert(is_publishable_p app_preds trace_index (serialize_request_uri uri)) by smt ();
    assert(is_publishable_p app_preds trace_index (serialize_request_uri req.req_uri)) by smt ();

    //headers are publishable
    init_seq_with_list_equivalence_of_list_and_sequence header_list;
    assert(is_publishable_p app_preds trace_index (dy_concat (string_to_bytes "Host") (serialize_domain authorization.acme_authorization_identifier))) by smt ();
    init_seq_with_list_length_lemma header_list;
    assert(Seq.length headers = 1) by smt ();
    assert(forall (el:http_header). contains headers el ==> el == ((string_to_bytes "Host"), (serialize_domain authorization.acme_authorization_identifier))) by smt ();
    assert(is_publishable_p app_preds trace_index (serialize_sequence_of_bytes_tuples req.req_headers)) by apply_lemma (`SerializationLemmas.serialized_sequence_of_bytes_tuples_publishable_if_all_elements_publishable);

    //body is publishable
    assert(is_publishable_p app_preds trace_index (string_to_bytes "")) by smt ();
    assert(is_publishable_p app_preds trace_index req.req_body) by smt ();

    assert(all_elements_of_http_request_are_publishable app_preds trace_index req) by smt ();
    assert(is_publishable_p app_preds trace_index (serialize_http_request req)) by apply_lemma (`SerializationLemmas.label_of_http_request_can_flow_to_public);
    assert(is_publishable_p app_preds trace_index (serialize_http_request req));
    req
#pop-options


let state_invariant_remains_true_if_true_for_new_state_precond
      (tr_idx:nat)
      (old_state:DY.Entry.principal_state)
      (new_state_el:DY.Entry.session_state)
      (p:principal)
      (vvec: version_vec)
    : Type =
       let vvec_length = Seq.length vvec in
       let vvec' = Seq.snoc vvec 0 in
       let new_state = Seq.snoc old_state new_state_el in
       Seq.length vvec = Seq.length old_state /\
       state_inv tr_idx p vvec old_state /\
       (match parse_acme_server_state new_state.[vvec_length], parse_acme_client_state new_state.[vvec_length] with
            | Success sti, Error _ ->
              serialize_acme_server_state sti == new_state.[vvec_length] /\
              valid_acme_server_st app_preds tr_idx p sti
            | Error _, Success sti ->
               serialize_acme_client_state sti == new_state.[vvec_length] /\
               valid_acme_client_st new_state tr_idx app_preds p sti
            | _ -> False
          )


#push-options "--z3rlimit 200 --max_fuel 2 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 2"
let _acme_server_trigger_challenge_verification server =
  let now = current_trace_len () in
  let (|trace_index_of_last_set_state, current_version_vec, current_app_state|) = get_last_state server in
  // retrieve some challenge that is currently in status processing (but no verification HTTP request has been sent out so far)
  match retrieve_acme_challenge_processing_from_server_st now server 0 current_version_vec current_app_state with
  | Some (|authorization_session_idx, authorization, challenge_idx, challenge|) -> (
    // prepare HTTP request to verify this challenge
    let (|i,request_id|) = guid_gen () in
    assert((Success? (parse_acme_server_state current_app_state.[authorization_session_idx])));
    assert(valid_acme_server_st app_preds now server (Success?.v (parse_acme_server_state current_app_state.[authorization_session_idx])));
    assert(is_publishable_p app_preds now (serialize_acme_authorization authorization));

    serialized_acme_authorization_flows_to_public_implies_components_flow_to_public now authorization;
    sequence_of_challenges_publishable_implies_single_challenge_publishable now authorization.acme_authorization_challenges challenge_idx;
    assert(challenge == authorization.acme_authorization_challenges.[challenge_idx]);
    assert(is_publishable_p app_preds now (serialize_acme_challenge challenge));

    let req = _acme_server_trigger_challenge_verification_create_request now server request_id challenge authorization in
    // store that we are currently verifying the challenge "challenge"
    let version_vec' = Seq.snoc current_version_vec 0 in
    let (new_acme_server_state_element:acme_server_state) = ProcessingChallenge authorization_session_idx challenge_idx request_id in
    let serialized_state_element = serialize_acme_server_state new_acme_server_state_element in
    let new_state = Seq.snoc current_app_state serialized_state_element in
    let len_now = current_trace_len() in

    assert(valid_acme_server_st app_preds now server new_acme_server_state_element);
    assert(can_label_of_bytes_flow_to app_preds now request_id public);
    assert(valid_acme_server_st app_preds len_now server new_acme_server_state_element);
    parse_acme_client_st_of_server_st_returns_none new_acme_server_state_element;

    // Prove state_inv (might be possible to do easier, we basically prove the precondition of
    // state_invariant_remains_true_if_true_for_new_state by hand)
    let vvec = current_version_vec in
    let old_state = current_app_state in
    let new_state_el = serialized_state_element in
    let tr_idx = len_now in
    let p = server in
    let vvec_length = Seq.length vvec in
    let vvec' = Seq.snoc vvec 0 in
    let new_state = Seq.snoc old_state new_state_el in
    assert(Seq.length vvec = Seq.length old_state);
    assert(state_inv trace_index_of_last_set_state p vvec old_state);
    state_inv_later trace_index_of_last_set_state tr_idx p vvec old_state;
    assert(state_inv tr_idx p vvec old_state);
    assert(Success? (parse_acme_server_state new_state.[vvec_length]));
    assert(Error? (parse_acme_client_state new_state.[vvec_length]));
    let sti = Success?.v (parse_acme_server_state new_state.[vvec_length]) in
    assert(serialize_acme_server_state sti == new_state.[vvec_length]);
    assert(valid_acme_server_st app_preds tr_idx p sti);
    assert(state_invariant_remains_true_if_true_for_new_state_precond len_now current_app_state serialized_state_element server current_version_vec);
    state_invariant_remains_true_if_true_for_new_state len_now current_app_state serialized_state_element server current_version_vec;
    assert(state_inv len_now server version_vec' new_state);

    state_with_new_valid_session_is_still_readable_by_server now server current_version_vec current_app_state new_acme_server_state_element;
    assert(is_principal_state_readable now server version_vec' new_state);
    set_state server version_vec' new_state;

    // send out http request to domain
    req
  )
  | _ -> error "No pending challenge"
#pop-options
