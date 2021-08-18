/// Application.Predicates.Lemmas
/// =================================================
module Application.Predicates.Lemmas
open Helpers
open DY.Labels
open DY.Principals
open DY.Crypto
open DY.Entry
open DY.Trace
open Labeled.Crypto
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Web.Messages
open SerializationHelpers
open ACME.Data
open ACME.Data.SerializationHelpers
open Application.Predicates.Helpers
open Application.Predicates


val valid_serialize_acme_client_st_lemma:
  (state:principal_state) ->
  (tr_idx:nat) ->
  (p:principal) ->
  (si:nat)->
  (st:acme_client_state)->
  Lemma (requires valid_acme_client_st state tr_idx app_preds  p st)
        (ensures (is_session_state_readable tr_idx p si 0 (serialize_acme_client_state st)))


val valid_serialize_acme_server_st_lemma: tr_idx:nat -> (p:principal)-> (si:nat)-> (j:nat)-> (st:acme_server_state)->
  Lemma (requires valid_acme_server_st app_preds tr_idx p st)
        (ensures (is_session_state_readable tr_idx p si j (serialize_acme_server_state st)))


val state_inv_implies_principal_state_readable:
  (idx:nat) ->
  (p:principal) ->
  (v:version_vec) ->
  (s:principal_state) ->
 Lemma
  (requires state_inv idx p v s)
  (ensures is_principal_state_readable idx p v s)


(**
    Lemma stating that when a server adds a new session to its state, all sessions are
    readable by the server if:

    (1) the new session is valid according to valid_acme_server_st and
    (2) previously, all sessions were readable by the server
*)
val state_with_new_valid_session_is_still_readable_by_server
      (tr_idx:nat)
      (server:principal)
      (current_version_vec:version_vec)
      (current_server_state:principal_state)
      (new_server_state:acme_server_state)
    : Lemma
      (requires(
        (Seq.length current_version_vec = Seq.length current_server_state) /\
        valid_acme_server_st app_preds  tr_idx server new_server_state /\
        (forall i. i < Seq.length current_version_vec ==> is_session_state_readable tr_idx server i current_version_vec.[i] current_server_state.[i])
      ))
      (ensures(
        let serialized_new_order_state = serialize_acme_server_state new_server_state in
        let new_version_vector = Seq.snoc current_version_vec 0 in
        let new_state = Seq.snoc current_server_state serialized_new_order_state in
        (forall i. i < Seq.length new_version_vector ==> is_session_state_readable tr_idx server i new_version_vector.[i] new_state.[i])
      ))

(**
    Lemma stating that when a server updates a new session, all sessions are
    readable by the server if:

    (1) the updated session is valid according to valid_acme_server_st and
    (2) previously, all sessions were readable by the server
*)
val state_with_updated_valid_session_is_still_readable_by_server
      (tr_idx:nat)
      (server:principal)
      (current_version_vec:version_vec)
      (current_server_state:principal_state)
      (updated_server_state:session_state)
      (session_idx:nat{session_idx < Seq.length current_server_state})
    : Lemma
      (requires(
        (Seq.length current_version_vec = Seq.length current_server_state) /\
        (Success? (parse_acme_server_state updated_server_state)) /\
        valid_acme_server_st app_preds tr_idx server (Success?.v (parse_acme_server_state updated_server_state)) /\
        (forall i. i < Seq.length current_version_vec ==> is_session_state_readable tr_idx server i current_version_vec.[i] current_server_state.[i]) /\
        updated_server_state == serialize_acme_server_state (Success?.v (parse_acme_server_state updated_server_state))
      ))
      (ensures(
        let new_state = current_server_state.[session_idx] <- (updated_server_state) in
        (forall i. i < Seq.length current_version_vec ==> is_session_state_readable tr_idx server i current_version_vec.[i] new_state.[i])
      ))


(**
   Lemma showing that the state invariant remains true if the conditions of the invariant hold true
   for the new state.
*)
val state_invariant_remains_true_if_true_for_new_state
      (tr_idx:nat)
      (old_state:principal_state)
      (new_state_el:session_state)
      (p:principal)
      (vvec: version_vec)
    : Lemma
     (requires(
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
     ))
     (ensures(
       let new_state = Seq.snoc old_state new_state_el in
       let vvec' = Seq.snoc vvec 0 in
       state_inv tr_idx p vvec' new_state
     ))


val achieve_valid_Certifiate_sesison_lemma:
  tr_idx:nat ->
  acc_pub_key: bytes ->
  cert: acme_certificate ->
  cert_url:url ->
  set_cert_st_idx: nat ->
 Lemma
  (requires
    (forall (sec_intendees:secret_intendees).
       is_verify_key_p app_preds set_cert_st_idx acc_pub_key (readable_by sec_intendees) (acme_sig_key_usage sec_intendees app_preds)   ==>
       (
         (
            exists (client:principal).
            sec_intendees == (readers [any client]) /\ //in the honest case, there is only one client who signed the message
           (exists (set_csr_st_idx:nat) .
              client_stored_CSR client set_csr_st_idx cert.acme_certificate_identifiers cert.acme_certificate_pub_key /\
              client_sent_newOrder_request_for_domains client cert.acme_certificate_identifiers /\
              //we need that to prove secrecy property
              is_pub_key_generated_for_client app_preds set_cert_st_idx client cert.acme_certificate_pub_key /\
              set_csr_st_idx < set_cert_st_idx
            )

         ) \/
           contains_corrupt_principal (app_preds.model.corrupt_at set_cert_st_idx) sec_intendees
       )
     ) /\
     (forall (i:nat). i<Seq.length cert.acme_certificate_identifiers ==> (
         let client = domain_principal_mapping ( cert.acme_certificate_identifiers).[i] in
         is_verify_key_p app_preds set_cert_st_idx acc_pub_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client])  app_preds) \/
         contains_corrupt_principal (app_preds.model.corrupt_at set_cert_st_idx) (readers [any client])
       )
     )
  )
  (ensures is_valid_Certificate_session app_preds tr_idx set_cert_st_idx cert cert_url acc_pub_key
  )

(**
Lemma 3 in proof-tex
*)
val ready_Order_session_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corrupted:
  (tr_idx:nat)->
  (order:acme_order)->
  (seq_authz_info:Seq.seq authorization_info)->
  (acc_pub_key:bytes)->
 Lemma
  (requires is_valid_Order_session app_preds tr_idx order seq_authz_info acc_pub_key /\ order.acme_order_status = Some Ready)
  (ensures
     (forall (i:nat). i<Seq.length order.acme_order_identifiers ==> (
        let dom_owner = domain_principal_mapping (order.acme_order_identifiers).[i] in
        is_verify_key_p app_preds tr_idx acc_pub_key (readable_by (readers [any dom_owner])) (acme_sig_key_usage (readers [any dom_owner])  app_preds)  \/
        contains_corrupt_principal (app_preds.model.corrupt_at tr_idx) (readers [any dom_owner])
     ))
  )


(**
   Lemma showing that the state invariant remains true if a server session is updated.
*)
val state_invariant_remains_true_if_true_for_updated_server_state:
  (tr_idx:nat) ->
  (old_state:principal_state) ->
  (new_state_el:session_state) ->
  (server:principal) ->
  (v: version_vec) ->
  (session_idx: nat{session_idx < Seq.length old_state}) ->
  Lemma
  (requires(
    let new_state = old_state.[session_idx] <- new_state_el in
    state_inv tr_idx server v old_state /\
    Seq.length v = Seq.length old_state /\
    Success? (parse_acme_server_state old_state.[session_idx]) /\
    Success? (parse_acme_server_state new_state_el ) /\
    (match parse_acme_server_state new_state_el with
      | Success sti ->
        serialize_acme_server_state sti == new_state_el /\
        valid_acme_server_st app_preds tr_idx server sti
    )
  ))
  (ensures(
    let new_state = old_state.[session_idx] <- new_state_el in
    state_inv tr_idx server v new_state
  ))


val add_valid_server_session_state_preserves_state_inv:
  tr_idx:nat ->
  server:principal ->
  current_version_vec: version_vec ->
  current_state:app_state tr_idx server current_version_vec ->
  new_ss:acme_server_state{valid_acme_server_st app_preds tr_idx server new_ss} ->
  Lemma
  (requires state_inv tr_idx server current_version_vec current_state)
  (ensures (
    let new_state = Seq.snoc current_state (serialize_acme_server_state new_ss) in
    let new_version_vec = Seq.snoc current_version_vec 0 in
    state_inv tr_idx server new_version_vec new_state /\
    is_principal_state_readable tr_idx server new_version_vec new_state
  ))
  
