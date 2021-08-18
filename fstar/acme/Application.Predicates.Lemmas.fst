/// Application.Predicates.Lemmas (implementation)
/// =================================================
module Application.Predicates.Lemmas
open DY.Labels
open DY.Principals
open DY.Crypto
open DY.Trace
open Labeled.Crypto
open Web.Messages
open SerializationHelpers
open ACME.Data
open ACME.Data.SerializationHelpers
friend ACME.Data.SerializationHelpers
open Application.Predicates.Helpers
open Application.Predicates
friend Application.Predicates

open SerializationLemmas
open ACME.Data.SerializationLemmas

#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2 "
let valid_serialize_acme_client_st_lemma state trace_idx p si st =
  match st with
  |Account private_key account_url order_url ->
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_url account_url)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label  (serialize_url order_url)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |HTTPSPendingRequest request_nonce reference_sessionid serv_dom ->
    can_flow_transitive (app_preds.model.corrupt_at trace_idx) (get_label request_nonce) (readable_by (readers [any p]))  (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label  (nat_to_bytes app_preds trace_idx reference_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    label_of_domain_flows_to_public app_preds trace_idx serv_dom;
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_domain serv_dom)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |ACMEOrder acme_order_object account_sessionid current_order_url->
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_opt_url current_order_url)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label  (serialize_acme_order acme_order_object)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
     flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label  (nat_to_bytes app_preds trace_idx account_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |ACMEAuthorziation acme_authorization_object acme_order_sessionid ->
     flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_acme_authorization acme_authorization_object)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
     flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label  (nat_to_bytes app_preds trace_idx acme_order_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |CSR cert_priv_key identifiers order_sessionid csr_set_state_idx ->
    serialized_sequence_of_domains_flows_to_public app_preds trace_idx identifiers;
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_sequence_of_domains identifiers)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label  (nat_to_bytes app_preds trace_idx order_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx csr_set_state_idx)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |RetrieveCertificate csr_sessionid ->
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx csr_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |ReceivedCertificate cert retrieve_cert_sessionid tr_idx ->
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_acme_certificate cert)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx retrieve_cert_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx tr_idx)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |ChallengeResponse authz_sessionid request_id ->
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx authz_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
    flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label request_id) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |ReplayNonce nonce valid serv_dom -> 
     flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (literal_to_bytes app_preds trace_idx (Bool valid))) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
     flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label nonce) (readable_by ({issuers = []; readers = [sess_ver p si 0]}));
     label_of_domain_flows_to_public app_preds trace_idx serv_dom;
     flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_domain serv_dom)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
  |ReplayNonceRequest serv_dom -> 
     label_of_domain_flows_to_public app_preds trace_idx serv_dom;
     flows_to_public_can_flow (app_preds.model.corrupt_at trace_idx) (get_label (serialize_domain serv_dom)) (readable_by ({issuers = []; readers = [sess_ver p si 0]}))
#pop-options

#push-options "--z3rlimit 150 --max_fuel 10 --max_ifuel 5 "
let valid_serialize_acme_server_st_lemma (trace_idx:nat) (p:principal) (si:nat) (j:nat) (st:acme_server_state)  =
  match st with
  | IssuedValidNonce t -> ()
  | PrivateCAKey k ->()
  | Order acme_order user_account_session_id acc_url acc_pub_key seq_authz_info ->
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (serialize_acme_order acme_order )) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx user_account_session_id)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (serialize_url acc_url)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label acc_pub_key) (readable_by (readers [sess_ver p si j]));
        sequence_of_authorization_info_is_publishable app_preds trace_idx seq_authz_info;
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (serialize_sequence_of_authorization_info seq_authz_info)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        assert(is_session_state_readable trace_idx p si j (serialize_acme_server_state st))
  | Authorization authorization_url authorization_object new_order_session_id ->
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (serialize_acme_authorization authorization_object)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (serialize_url authorization_url)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx new_order_session_id)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        assert(is_session_state_readable trace_idx p si j (serialize_acme_server_state st))
  | Certificate set_cert_st_idx cert cert_url acc_pub_key ->
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (serialize_acme_certificate cert)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (serialize_url cert_url)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label acc_pub_key) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx set_cert_st_idx)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        assert(is_session_state_readable trace_idx p si j (serialize_acme_server_state st))
  | ProcessingChallenge authorization_sessionid challenge_idx http_request_id ->
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx authorization_sessionid)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label (nat_to_bytes app_preds trace_idx challenge_idx)) (readable_by ({issuers = []; readers = [sess_ver p si j]}));
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label http_request_id) (readable_by ({issuers = []; readers = [sess_ver p si j]}))
  | UserAccount account public_key account_url ->
        flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label  (serialize_acme_account account)) (readable_by (readers [sess_ver p si j]));
         flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label  (serialize_url account_url)) (readable_by (readers [sess_ver p si j]));
          flows_to_public_can_flow  (app_preds.model.corrupt_at trace_idx) (get_label public_key) (readable_by (readers [sess_ver p si j]))
  | _ -> ()



val state_inv_implies_principal_state_readable_si
  (idx:nat)
  (p:principal)
  (v:version_vec)
  (s:principal_state)
  (si:nat{si < Seq.length v})
 :Lemma
  (requires state_inv idx p v s)
  (ensures is_session_state_readable idx p si 0 s.[si])
  [SMTPat (state_inv idx p v s); SMTPat (is_session_state_readable idx p si 0 s.[si])]

let state_inv_implies_principal_state_readable_si idx p v s si =
  match parse_acme_server_state s.[si], parse_acme_client_state s.[si] with
  | Success sti, Error _ ->
      assert(valid_acme_server_st app_preds idx p sti);
      assert(serialize_acme_server_state sti == s.[si]);
      valid_serialize_acme_server_st_lemma idx p si 0 sti
  | Error _, Success sti ->
      assert(serialize_acme_client_state sti == s.[si]);
      valid_serialize_acme_client_st_lemma s idx p si sti
  | _ -> ()



let state_inv_implies_principal_state_readable idx p v s =
  assert(forall i. i < Seq.length v ==> v.[i] = 0);
  assert(forall i. i < Seq.length v ==> is_session_state_readable idx p i 0 s.[i])


#push-options "--z3rlimit 150 --max_fuel 10 --max_ifuel 5 "
(**
    Lemma stating that when a server adds a new session to its state, all sessions are
    readable by the server if:

    (1) the new session is valid according to valid_acme_server_st and
    (2) previously, all sessions were readable by the server
*)
let state_with_new_valid_session_is_still_readable_by_server
      (tr_idx:nat)
      (server:principal)
      (current_version_vec:version_vec)
      (current_server_state:principal_state)
      (new_server_state:acme_server_state)
    : Lemma
      (requires(
        (Seq.length current_version_vec = Seq.length current_server_state) /\
        valid_acme_server_st app_preds tr_idx server new_server_state /\
        (forall i. i < Seq.length current_version_vec ==> is_session_state_readable tr_idx server i current_version_vec.[i] current_server_state.[i])
      ))
      (ensures(
        let serialized_new_order_state = serialize_acme_server_state new_server_state in
        let new_version_vector = Seq.snoc current_version_vec 0 in
        let new_state = Seq.snoc current_server_state serialized_new_order_state in
        (forall i. i < Seq.length new_version_vector ==> is_session_state_readable tr_idx server i new_version_vector.[i] new_state.[i])
      ))
    =
      assert(valid_acme_server_st app_preds tr_idx server new_server_state);
      valid_serialize_acme_server_st_lemma tr_idx server (Seq.length current_version_vec) 0 new_server_state

#pop-options

#push-options "--z3rlimit 150 --max_fuel 10 --max_ifuel 5 "
(**
    Lemma stating that when a server updates a new session, all sessions are
    readable by the server if:

    (1) the updated session is valid according to valid_acme_server_st and
    (2) previously, all sessions were readable by the server
*)
let state_with_updated_valid_session_is_still_readable_by_server
      (tr_idx: nat)
      (server:principal)
      (current_version_vec:version_vec)
      (current_server_state:principal_state)
      (updated_server_state:session_state)
      (session_idx:nat{session_idx < Seq.length current_server_state})
    =
      let parsed_server_state = Success?.v (parse_acme_server_state updated_server_state) in
      let new_state = current_server_state.[session_idx] <- (updated_server_state) in
      assert(valid_acme_server_st app_preds tr_idx server parsed_server_state);
      valid_serialize_acme_server_st_lemma tr_idx server session_idx  current_version_vec.[session_idx]  parsed_server_state;
      assert(is_session_state_readable tr_idx server session_idx current_version_vec.[session_idx] new_state.[session_idx])

#pop-options


(**
   Lemma showing that the state invariant remains true if the conditions of the invariant hold true
   for the new state.
*)
#push-options "--z3rlimit 150 --max_fuel 10 --max_ifuel 5 "
let state_invariant_remains_true_if_true_for_new_state
      tr_idx
      old_state
      new_state_el
      p
      vvec
    =
      let (new_state:principal_state) = Seq.snoc old_state new_state_el in
      let (vvec':version_vec) = Seq.snoc vvec 0 in
      assert(Seq.length vvec' = Seq.length new_state);

      assert((forall si. si < Seq.length vvec ==>
       ( match parse_acme_server_state old_state.[si], parse_acme_client_state old_state.[si] with
         | Success sti, Error _ -> True
         | Error _, Success sti -> True
         | _ -> False
      )));

      assert((forall si. si < Seq.length vvec' ==>
       ( match parse_acme_server_state new_state.[si], parse_acme_client_state new_state.[si] with
         | Success sti, Error _ -> True
         | Error _, Success sti -> True
         | _ -> False
      )));

     assert(state_inv tr_idx p vvec' new_state)
#pop-options


let achieve_valid_Certifiate_sesison_lemma tr_idx acc_pub_key cert cert_url set_cert_st_idx = ()


let ready_Order_session_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corrupted tr_idx order seq_authz_info acc_pub_key = ()


let state_invariant_remains_true_if_true_for_updated_server_state tr_idx old_state new_state_el server v session_idx =
  let new_state:principal_state = old_state.[session_idx] <- new_state_el in
  assert(forall si. si < Seq.length v && si <> session_idx ==> new_state.[si] == old_state.[si]);
  assert(forall si. si <  session_idx ==> new_state.[si] == old_state.[si]);
  assert(forall si. si < Seq.length v /\ si <>  session_idx ==> new_state.[si] == old_state.[si])


#set-options "--z3refresh --max_fuel 8 --max_ifuel 8 --z3rlimit 500"
let add_valid_server_session_state_preserves_state_inv tr_idx server v state new_ss =
  let new_state = Seq.snoc state (serialize_acme_server_state new_ss) in
  let new_v = Seq.snoc v 0 in
  valid_serialize_acme_server_st_lemma tr_idx server (Seq.length v) 0 new_ss;
  parse_acme_server_state_lemma new_ss;
  parse_acme_client_st_of_server_st_returns_none new_ss;
  assert(state_inv tr_idx server new_v new_state); 
  state_inv_implies_principal_state_readable tr_idx server new_v new_state
