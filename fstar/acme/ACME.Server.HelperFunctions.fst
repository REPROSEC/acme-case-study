/// ACME.Server.HelperFunctions (implementation)
/// =============================================
module ACME.Server.HelperFunctions

module LC = Labeled.Crypto
open Web.Messages
module DC = DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
module LA = Labeled.ApplicationAPI
open Application.Predicates
friend Application.Predicates

open ACME.Data
open ACME.Data.SerializationHelpers
friend ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas

open SerializationHelpers
open SerializationLemmas

open FStar.Seq

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

let rec retrieve_public_account_key_from_server_st_inner
    (trace_index:nat)
    (server:principal)
    (key_id:url)
    (session_index:nat)
    (state:(now:nat & v:version_vec & DY.Entry.principal_state)):
  Pure (option (pubk:DC.bytes{LC.is_publishable_p app_preds trace_index pubk}))
    (requires ((
      let (|now, v, s|) = state in
      now = trace_index /\ // Needed to get state_inv at trace_index
      (exists i. i < now /\ is_set_state_at i server v s) /\
         state_inv now server v s /\
         is_principal_state_readable now server v s)))
    (ensures (fun _ -> True))
    (decreases (
      let (|_, _, current_app_state|) = state in
      (Seq.length current_app_state) - session_index
    ))
  =
     let (|trace_index_of_last_set_state, current_version_vec, current_app_state|) = state in
     if Seq.length current_version_vec <= session_index then None else (
       match parse_acme_server_state current_app_state.[session_index] with
       | Success (UserAccount account public_key account_url) ->
         if eq_url account_url key_id then (
           Some public_key
         )
         else retrieve_public_account_key_from_server_st_inner trace_index server key_id (session_index + 1) state
       | _ -> retrieve_public_account_key_from_server_st_inner trace_index server key_id (session_index + 1) state
     )


let retrieve_public_account_key_from_server_st trace_index server key_id =
  let s = LA.get_last_state server in
  retrieve_public_account_key_from_server_st_inner trace_index server key_id 0 s


(**
    Helper function for [retrieve_private_ca_key_from_server].
*)
let rec _retrieve_private_ca_key_from_server_st
  (trace_index:nat)
  (server:principal)
  (session_index:nat)
  (current_version_vec:version_vec)
  (current_app_state:app_state trace_index server current_version_vec{Seq.length current_version_vec = Seq.length current_app_state})
  : Pure (option (nat * DC.bytes))
       (requires Seq.length current_version_vec = Seq.length current_app_state)
       (ensures (fun r ->
         Some? r ==> (
         let si = fst (Some?.v r) in
         let key = snd (Some?.v r) in
         Seq.length current_app_state > si /\
         (match parse_acme_server_state (current_app_state.[si]) with
         | Success (PrivateCAKey private_ca_key) -> key == private_ca_key
         | _ -> False
       ))))
       (decreases (Seq.length current_version_vec - session_index))
  =
    if Seq.length current_version_vec <= session_index then None else
    match parse_acme_server_state current_app_state.[session_index] with
    | Success (PrivateCAKey private_ca_key) -> Some (session_index, private_ca_key)
    | _ -> _retrieve_private_ca_key_from_server_st trace_index server (session_index + 1) current_version_vec current_app_state

let retrieve_private_ca_key_from_server_st trace_index server current_version_vec current_app_state =
    _retrieve_private_ca_key_from_server_st trace_index server 0 current_version_vec current_app_state

#push-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"
let verify_jws_acme_request_signature trace_index server jws_acme_request_object =
  let some_public_key = retrieve_public_account_key_from_server_st trace_index server jws_acme_request_object.key_id in
  let msg = generate_message_for_jws_signature jws_acme_request_object.key_id jws_acme_request_object.url jws_acme_request_object.replay_nonce jws_acme_request_object.payload in
  match some_public_key with
  | None -> (|false, None|)
  | Some public_key -> (
    parse_jws_acme_request_lemma_publishablity app_preds trace_index (serialize_jws_acme_request jws_acme_request_object);
    generate_message_for_jws_signature_preserves_publishability app_preds trace_index jws_acme_request_object.key_id jws_acme_request_object.url jws_acme_request_object.replay_nonce jws_acme_request_object.payload;
    let m:LC.msg_p app_preds trace_index public = msg in
    let s:LC.msg_p app_preds trace_index public = jws_acme_request_object.signature in
    if LC.verify_un #app_preds #trace_index #public #public public_key m s then (
      (|true, Some public_key|)
    ) else
      (|false, None|)
  )
#pop-options


let verify_jws_acme_request trace_index request server jws_acme_request_object =
  match get_header_from_headers "Host" request.req_headers 0 with
  | None -> (print_string "verify_jws_acme_request: No host header!\n"; (|false, None|))
  | Some (host_header_key, host_header_value) -> (
    match parse_domain host_header_value with
    | Error _ -> (print_string "verify_jws_acme_request: Host header not parseable!\n"; (|false, None|))
    | Success d -> (
      let expected_url = {
        url_scheme = HTTPS;
        url_domain = d;
        url_request_uri = request.req_uri
      } in
      if eq_url expected_url jws_acme_request_object.url
      then verify_jws_acme_request_signature trace_index server jws_acme_request_object
      else (print_string "verify_jws_acme_request: JWS url != request url!\n"; (|false, None|))
     )
   )


#push-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --initial_ifuel 0"
let verify_acme_new_key_inner_jws trace_index server jws =
  let some_public_key = retrieve_public_account_key_from_server_st trace_index server jws.inner_payload_account in
  let msg = generate_message_for_new_key_inner_jws_signature jws.alg jws.jwk jws.inner_url jws.inner_payload_account jws.inner_payload_old_key in
  match some_public_key with
  | None -> (|false, None|)
  | Some public_key -> (
      parse_acme_new_key_inner_jws_lemma_publishablity app_preds trace_index (serialize_acme_new_key_inner_jws jws);
      generate_message_for_new_key_inner_jws_signature_preserves_publishability
        app_preds
        trace_index
        jws.alg jws.jwk jws.inner_url jws.inner_payload_account jws.inner_payload_old_key;
      assert(LC.is_publishable_p app_preds trace_index msg);
      let m:LC.msg_p app_preds trace_index public = msg in
      let s:LC.msg_p app_preds trace_index public = jws.inner_signature in
      if LC.verify_un #app_preds #trace_index #public #public public_key m s then (
        (|true, Some public_key|)
      ) else
        (|false, None|)
    )
#pop-options

let retrieve_account_session_containing_account_url_from_server_st trace_index server account_url =
  match LA.get_last_state server with
  | (|trace_index_of_last_set_state, current_version_vec, current_server_state|) -> (
    let opt_acc_sess_id = retrieve_account_session_id_containing_account_url
      trace_index
      server
      account_url
      0
      current_version_vec
      current_server_state in
    match opt_acc_sess_id with
    | None -> None
    | Some acc_sess_id -> (
      match parse_acme_server_state current_server_state.[acc_sess_id] with
      | Error _ -> None
      | Success acc_sess -> (
        match acc_sess with
        | (UserAccount account acc_pub_key acc_url) ->  (
          Some (acc_sess, acc_sess_id)
          )
        | _ -> None
      )
    )
  )


let rec find_index_of_identifier_in_sequence_of_authorization_info
  (seq_authz_info: Seq.seq authorization_info)
  (identifier:domain)
  (idx:nat)
  :Tot (option (identifier_idx:nat{
    identifier_idx < Seq.length seq_authz_info /\
    (seq_authz_info.[identifier_idx]).authz_info_identifier = identifier
  }))
  (decreases (Seq.length seq_authz_info - idx))
 =
  if idx >= Seq.length seq_authz_info then
    None
  else(
    if identifier = (seq_authz_info.[idx]).authz_info_identifier then
      Some idx
    else
      find_index_of_identifier_in_sequence_of_authorization_info seq_authz_info identifier (idx+1)
  )

let set_valid_for_identifier_in_order trace_index order seq_authz_info acc_pub_key identifier =
  match find_index_of_identifier_in_sequence_of_authorization_info seq_authz_info identifier 0 with
  | Some iden_idx ->(
      let old_authz_info = seq_authz_info.[iden_idx] in
      let new_authz_info:authorization_info = {
        authz_info_identifier = old_authz_info.authz_info_identifier;
        authz_info_status = Valid
      } in
      let updated_seq_authz_info = seq_authz_info.[iden_idx] <- new_authz_info in
      updated_seq_authz_info
    )
  | _ -> seq_authz_info

let rec are_all_authorization_valid
  (seq_authz_info:Seq.seq authorization_info)
  (idx:nat)
 : Tot (b:bool{
   b <==>
   ( forall (i:nat). (i<Seq.length seq_authz_info /\ i>=idx) ==>
       (seq_authz_info.[i]).authz_info_status = Valid
   )
 })
 (decreases (Seq.length seq_authz_info - idx))
 =
  if idx >= Seq.length seq_authz_info then(
    true
  )else(
    let hd = seq_authz_info.[idx] in
    if hd.authz_info_status = Valid then(
      are_all_authorization_valid seq_authz_info (idx+1)
    )else
      false
  )

let check_valid_and_set_ready_for_order trace_index order seq_authz_info acc_pub_key =
  if are_all_authorization_valid seq_authz_info 0 then(
    assert(LC.is_publishable_p app_preds trace_index (serialize_acme_order order));
    let updated_order = {order with acme_order_status = Some Ready} in
    serialized_updated_acme_order_flows_to_public_status trace_index order;
    assert(LC.is_publishable_p app_preds trace_index (serialize_acme_order updated_order));
    updated_order
  )else order


let rec exists_one_authorization_valid
  (seq_authz_info:Seq.seq authorization_info)
  (idx:nat)
 : Tot (b:bool{
   b <==>
   ( exists (i:nat). (i<Seq.length seq_authz_info /\ i>=idx) /\
       (seq_authz_info.[i]).authz_info_status = Valid
   )
 })
 (decreases (Seq.length seq_authz_info - idx))
 =
  if idx >= Seq.length seq_authz_info then(
    false
  )else(
    let hd = seq_authz_info.[idx] in
    if hd.authz_info_status = Valid then(
      true
    )else
      exists_one_authorization_valid seq_authz_info (idx+1)
  )

let check_valid_and_set_ready_for_order_faulty trace_index order seq_authz_info acc_pub_key =
  if exists_one_authorization_valid seq_authz_info 0 then(
    assert(LC.is_publishable_p app_preds trace_index (serialize_acme_order order));
    let updated_order = {order with acme_order_status = Some Ready} in
    serialized_updated_acme_order_flows_to_public_status trace_index order;
    assert(LC.is_publishable_p app_preds trace_index (serialize_acme_order updated_order));
     //without following assume, this function cannot be typechecked, because the server did not check the status of ALL authorizations of the order
    assume(is_valid_Order_session app_preds trace_index updated_order seq_authz_info acc_pub_key);
    updated_order
  )else order


let generate_sequence_of_authorization_info_for_order trace_index order acc_pub_key =
  let len = Seq.length order.acme_order_identifiers in
  let contents:(i:nat { i < len } -> Tot authorization_info) =(
      fun i -> {
       authz_info_identifier = (order.acme_order_identifiers).[i];
       authz_info_status = Pending
     }
  )in
  let seq_authz_info = Seq.init #authorization_info (Seq.length order.acme_order_identifiers) contents in

  assert(each_order_identifier_has_one_authorization order seq_authz_info); //integrity property #1
  assert(authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before app_preds trace_index seq_authz_info acc_pub_key); //integrity property #3
  assert(order.acme_order_status <> Some Ready);
  assert(order.acme_order_status = Some Ready ==>
   (forall (i:nat). i<Seq.length seq_authz_info ==> (seq_authz_info.[i]).authz_info_status = Valid)
  );
  assert(order_status_is_Ready_implies_all_authorizations_are_Valid order seq_authz_info); //integrity property #2
  assert(is_valid_Order_session app_preds trace_index order seq_authz_info acc_pub_key);
  seq_authz_info
