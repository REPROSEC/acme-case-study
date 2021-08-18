/// ACME.Server.KeyRollover (implementation)
/// ========================================
module ACME.Server.KeyRollover

open Helpers
open DY.Monad
open DY.Labels
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
open ACME.Data.Predicates


open SerializationHelpers
open SerializationLemmas

open ACME.Server.HelperFunctions
open ACME.Data.SerializationLemmas

open FStar.Seq

module T = FStar.Tactics

#set-options "--z3rlimit 0 --max_fuel 0 --max_ifuel 0 --initial_ifuel 0"

let parse_http_req_body
    (request:http_request)
  : DYL jws_acme_request
    (requires (fun h0 ->
      is_publishable_p app_preds (trace_len h0) (serialize_http_request request)
    ))
    (ensures (fun h0 body h1 ->
      h0 == h1 /\
      is_publishable_p app_preds (trace_len h1) (serialize_jws_acme_request body)
    ))
  =
    match parse_jws_acme_request request.req_body with
    | Error e -> error ("parse_http_req_body (1): " ^ e)
    | Success jws_acme_request -> (
        let len_now = current_trace_len () in
        http_request_is_publishable_implies_body_is_publishable app_preds len_now request;
        parse_jws_acme_request_lemma_publishablity app_preds len_now request.req_body;
        serialize_parse_jws_acme_request_publishability_lemma app_preds len_now request.req_body;
        jws_acme_request
      )


let parse_key_rollover_inner_jws
    (outer_jws:jws_acme_request)
  : DYL acme_new_key_inner_jws
    (requires (fun h0 ->
      is_publishable_p app_preds (trace_len h0) (serialize_jws_acme_request outer_jws)
    ))
    (ensures (fun h0 inner_jws h1 ->
      h0 == h1 /\
      is_publishable_p app_preds (trace_len h1) (serialize_acme_new_key_inner_jws inner_jws)
    ))
  =
    allow_inversion (result acme_new_key_inner_jws);
    match parse_acme_new_key_inner_jws outer_jws.payload with
    | Error e -> error ("parse_key_rollover_inner_jws (1): " ^ e)
    | Success inner_jws -> (
        let len_now = current_trace_len () in
        parse_jws_acme_request_lemma_publishablity app_preds len_now (serialize_jws_acme_request outer_jws);
        serialize_parse_jws_acme_request_publishability_lemma app_preds len_now (serialize_jws_acme_request outer_jws);
        parse_acme_new_key_inner_jws_lemma inner_jws;
        parse_acme_new_key_inner_jws_lemma2 outer_jws.payload;
        inner_jws
      )


let retrieve_account_session_from_server_st
  (trace_index:nat)
  (server:principal)
  (account_url:url)
  (current_version_vec:version_vec)
  (current_server_state:app_state trace_index server current_version_vec{Seq.length current_version_vec = Seq.length current_server_state})
  : Pure (result (acme_server_state * nat))
  (requires (True))
  (ensures (fun r ->
    Success? r ==> (
      let Success (acc_sess, sess_idx) = r in
      UserAccount? acc_sess /\
      eq_url account_url (UserAccount?.account_url acc_sess) /\
      sess_idx < Seq.length current_server_state /\
      parse_acme_server_state (current_server_state.[sess_idx]) == Success acc_sess
    )
  ))
  =
  let opt_acc_sess_id = retrieve_account_session_id_containing_account_url
    trace_index
    server
    account_url
    0
    current_version_vec
    current_server_state in
  match opt_acc_sess_id with
  | None -> Error ""
  | Some acc_sess_id -> (
    match parse_acme_server_state current_server_state.[acc_sess_id] with
    | Error _ -> Error ""
    | Success acc_sess -> (
      match acc_sess with
      | (UserAccount account acc_pub_key acc_url) -> (
        let r = (acc_sess, acc_sess_id) in
        assert(UserAccount? acc_sess);
        assert(eq_url account_url (UserAccount?.account_url acc_sess));
        Success r
      )
      | _ -> Error ""
    )
  )


let empty_ok_http_response_is_publishable
    (req_id:bytes)
    (trace_index:nat)
  : Lemma
    (requires (is_publishable_p app_preds trace_index req_id))
    (ensures (
      let response:http_response = {
        resp_req_id = req_id;
        resp_status = HTTP_STATUS_200_OK;
        resp_headers = Seq.empty;
        resp_body = string_to_bytes ""
      } in
      is_publishable_p app_preds trace_index (serialize_http_response response)
    ))
  =
    let response:http_response = {
      resp_req_id = req_id;
      resp_status = HTTP_STATUS_200_OK;
      resp_headers = Seq.empty;
      resp_body = string_to_bytes ""
    } in
    assert(is_publishable_p app_preds trace_index (string_to_bytes ""));
    assert(is_publishable_p app_preds trace_index (serialize_sequence_of_bytes_tuples Seq.empty))
      by T.(set_options "--max_fuel 1 --initial_fuel 1");
    assert(all_elements_of_http_response_are_publishable app_preds trace_index response);
    label_of_http_response_can_flow_to_public app_preds trace_index response


let replacing_session_does_not_break_state_inv
    (trace_idx:nat)
    (server:principal)
    (v:version_vec)
    (st:DY.Entry.principal_state)
    (sess_idx_to_replace:nat)
    (new_sess_st:acme_server_state)
  : Lemma
    (requires (
      valid_acme_server_st app_preds trace_idx server new_sess_st /\
      state_inv trace_idx server v st /\
      sess_idx_to_replace < Seq.length st /\
      (Error? (parse_acme_client_state st.[sess_idx_to_replace]))
    ))
    (ensures (
      let new_session = serialize_acme_server_state new_sess_st in
      let new_state = Seq.Base.upd st sess_idx_to_replace new_session in
      state_inv trace_idx server v new_state
    ))
  =
    let new_session = serialize_acme_server_state new_sess_st in
    let new_state = Seq.Base.upd st sess_idx_to_replace new_session in
    assert(Seq.length new_state = Seq.length st);
    assert(Success? (parse_acme_server_state new_state.[sess_idx_to_replace]));
    assert(Error? (parse_acme_client_state new_state.[sess_idx_to_replace]));
    assert(forall (i:nat{i <> sess_idx_to_replace}). i < Seq.length new_state ==> st.[i] == new_state.[i]);
    assert(forall i. i < Seq.length v ==> v.[i] == 0);
    assert(Seq.length v = Seq.length new_state);
    assert(forall i. i = sess_idx_to_replace ==> (
      match parse_acme_server_state new_state.[i], parse_acme_client_state new_state.[i] with
      | Success sti, Error _ ->
        serialize_acme_server_state sti == new_state.[i] /\
        valid_acme_server_st app_preds trace_idx server sti
      | _ -> False)
    );
    valid_acme_client_st_does_not_depend_on_server_sessions st new_state trace_idx app_preds server;
    assert(
      forall (i:nat{i <> sess_idx_to_replace}). i < Seq.length v ==> (
        match parse_acme_client_state new_state.[i] with
        | Success sti -> (
          Success? (parse_acme_client_state st.[i]) /\
          (Success?.v (parse_acme_client_state st.[i]) == sti) /\
          (
            valid_acme_client_st st trace_idx app_preds server sti <==>
            valid_acme_client_st new_state trace_idx app_preds server sti
          )
        )
        | _ -> True
      )
    )



#push-options "--z3rlimit 0 --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"
let _acme_server_update_account_key server http_request =
  let (|len_now, current_version_vec, old_state|) = get_last_state server in
  assert(is_publishable_p app_preds (len_now + 1) http_request.req_id);
  let jws_acme_request_obj = parse_http_req_body http_request in
  let verification_result = verify_jws_acme_request len_now http_request server jws_acme_request_obj in
  let inner_jws = parse_key_rollover_inner_jws jws_acme_request_obj in
  let inner_verification_result = verify_acme_new_key_inner_jws len_now server inner_jws in
  let old_kid = jws_acme_request_obj.key_id in
  let outer_url = jws_acme_request_obj.url in
  let are_urls_equal = eq_url outer_url inner_jws.inner_url in
  let are_account_urls_equal = eq_url old_kid inner_jws.inner_payload_account in
  assert(Seq.length current_version_vec = Seq.length old_state);
  let tmp = retrieve_account_session_from_server_st len_now server old_kid current_version_vec old_state in
  if Error? tmp then (
    error "_acme_server_update_account_key (0): Could not find an account with the given account kid!"
  ) else
  let ((UserAccount account acc_pub_key acc_url), user_account_session_id) = Success?.v tmp in
  assert(Seq.length old_state > user_account_session_id);
  if not( dfst verification_result ) then (
    error "_acme_server_update_account_key (1): Invalid signature on JWS!"
  ) else if not( dfst inner_verification_result ) then (
    error "_acme_server_update_account_key (2): Invalid signature on inner JWS!"
  ) else if not (are_urls_equal && are_account_urls_equal) then (
    error "_acme_server_update_account_key (3): URL or account of inner JWS != values in outer JWS!"
  ) else if not( eq_bytes acc_pub_key inner_jws.inner_payload_old_key ) then (
    error "_acme_server_update_account_key (4): old_key in inner JWS != account public key in server state"
  ) else (
    // Replace account entry in server state with updated entry
    let new_acc_session_st = UserAccount account inner_jws.jwk acc_url in
    assert(valid_acme_server_st app_preds len_now server new_acc_session_st);
    let new_acc_session = serialize_acme_server_state new_acc_session_st in
    let new_state = Seq.Base.upd old_state user_account_session_id new_acc_session in
    assert(Seq.length new_state = Seq.length old_state);
    assert(Seq.length new_state = Seq.length current_version_vec);
    replacing_session_does_not_break_state_inv len_now server current_version_vec old_state user_account_session_id new_acc_session_st;
    assert(state_inv len_now server current_version_vec new_state);
    state_inv_implies_principal_state_readable len_now server current_version_vec new_state;
    assert(is_principal_state_readable len_now server current_version_vec new_state);
    set_state server current_version_vec new_state;
    let new_len = current_trace_len () in
    assert(new_len = len_now + 1);
    let response:http_response = {
      resp_req_id = http_request.req_id;
      resp_status = HTTP_STATUS_200_OK;
      resp_headers = Seq.empty;
      resp_body = string_to_bytes ""
    } in
    empty_ok_http_response_is_publishable http_request.req_id new_len;
    response
  )
#pop-options
