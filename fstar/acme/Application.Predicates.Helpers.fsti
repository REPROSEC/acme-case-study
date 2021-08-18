/// Application.Predicates.Helpers
/// ================================================
module Application.Predicates.Helpers
open DY.Principals
open DY.Labels
open DY.Crypto
open DY.Trace
open DY.Entry
open Labeled.Crypto
open Web.Messages
open SerializationHelpers
open ACME.Data
open ACME.Data.SerializationHelpers

open ACME.Data.Predicates
open Helpers

module T = FStar.Tactics

(*!
 ONLY add helper PREDICATES used for Application.Predicates here
*)
let client_sent_newOrder_request
  (client: principal)
  (domains: Seq.seq domain)
  (v: version_vec)
  (state: principal_state)
  (set_order_state_idx: nat)
  (newOrder_idx: nat)
 : Type0
 =
  is_set_state_at set_order_state_idx client v state /\
  newOrder_idx < Seq.length state /\
  ( match parse_acme_client_state state.[newOrder_idx] with
    | Success (ACMEOrder order acc_idx _) -> (
        order.acme_order_identifiers = domains
      )
    | _ -> False
  )

let client_has_account_public_key
  (client:principal)
  (acc_pub_key:bytes)
  (trace_length:nat)
 : Type0
 =
   exists (v_acc:version_vec)
  (st_acc:principal_state)
  (set_account_idx:nat)
  (acc_sessionid:nat).
  is_set_state_at set_account_idx client v_acc st_acc /\
  set_account_idx < trace_length /\
  acc_sessionid < Seq.length st_acc /\
  ( match parse_acme_client_state st_acc.[acc_sessionid] with
    | Success (Account acc_priv_key acc_url order_url) ->(
        DY.Crypto.pk acc_priv_key == acc_pub_key
      )
    | _ -> False
  )

let client_stored_CSR_in_state
 (client: principal)
  (set_csr_state_idx: nat)
  (v:version_vec)
  (state:principal_state)
  (csr_sessionid:nat)
  (domains: Seq.seq domain)
  (cert_pub_key: bytes)
 =
  is_set_state_at set_csr_state_idx client v state /\
  csr_sessionid < Seq.length state /\
  ( match parse_acme_client_state state.[csr_sessionid] with
    | Success (CSR cert_priv_key identifiers  order_idx _) -> (
        DY.Crypto.pk cert_priv_key == cert_pub_key /\
        domains = identifiers
      )
    | _ -> False
  )

let client_stored_CSR
  (client: principal)
  (set_csr_state_idx: nat)
  (domains: Seq.seq domain)
  (cert_pub_key: bytes)
   : Type0
 =
 exists (v:version_vec) (state:principal_state) (csr_sessionid:nat).
  is_set_state_at set_csr_state_idx client v state /\
  csr_sessionid < Seq.length state /\
  ( match parse_acme_client_state state.[csr_sessionid] with
    | Success (CSR cert_priv_key identifiers order_idx _) -> (
        DY.Crypto.pk cert_priv_key == cert_pub_key /\
        domains = identifiers
      )
    | _ -> False
  )




let client_has_authorization_session
  (trace_length:nat)
  (client:principal)
  (authz_token: bytes)
  (acc_pub_key: bytes)
 =
  exists (set_state_idx:nat)(v:version_vec) (state:principal_state) (authz_idx:nat).
  is_set_state_at set_state_idx client v state /\
  authz_idx < Seq.length state /\
  set_state_idx < trace_length /\
  ( match parse_acme_client_state state.[authz_idx] with
    | Success (ACMEAuthorziation authorization order_idx) -> (
        Seq.length authorization.acme_authorization_challenges > 0 /\
        //same token
        (authz_token == ((authorization.acme_authorization_challenges).[0]).acme_challenge_token) /\
          client_has_account_public_key client acc_pub_key trace_length
      )
    | _ -> False
  )


(**
  This is the post-condition of [certificate_of_client_corresponds_to_csr_stored_by_client] (equal to
  [certificate_corresponds_to_csr_stored_previously]).
*)
let is_valid_client_certificate_session
    (client:principal)
    (certificate:acme_certificate)
    (retrieve_cert_sessionid:nat)
    (cert_set_state_idx:nat)
  =
    exists (csr_trace_idx:nat) (csr_v:version_vec) (csr_state:principal_state).
    csr_trace_idx < cert_set_state_idx /\
    is_set_state_at csr_trace_idx client csr_v csr_state /\
    retrieve_cert_sessionid < Seq.length csr_state /\
    (match parse_acme_client_state (csr_state.[retrieve_cert_sessionid]) with
      | Success (RetrieveCertificate csr_sessionid) -> (
        if(csr_sessionid >= Seq.length csr_state) then False else (
          match parse_acme_client_state (csr_state.[csr_sessionid]) with
          | Success (CSR csr_cert_priv_key csr_identifiers csr_acme_order_sessionid _) -> (
            eq_bytes certificate.acme_certificate_pub_key (DY.Crypto.pk csr_cert_priv_key) /\
            is_same_set certificate.acme_certificate_identifiers csr_identifiers
            )
          | _ -> False
        )
        )
      | _ -> False
    )


(**
  This is the post-condition of [csr_stored_by_client_corresponds_to_order_stored_by_client] (equal to
  [identifiers_were_previously_stored_in_order]).
*)
let is_valid_client_csr_session
    (client:principal)
    (identifiers:Seq.seq domain)
    (acme_order_sessionid:nat)
    (csr_set_state_idx:nat)
  =
    exists (order_trace_idx:nat) (order_v:version_vec) (order_state:principal_state).
    order_trace_idx < csr_set_state_idx /\
    is_set_state_at order_trace_idx client order_v order_state /\
    acme_order_sessionid  < Seq.length order_state /\
    (match parse_acme_client_state (order_state.[acme_order_sessionid]) with
      | Success (ACMEOrder order _ _) -> (
        identifiers = order.acme_order_identifiers
        )
      | _ -> False
    )

//usage pred for the private key of the certificate, so far it is never used
unfold let acme_pke_key_usage (reader:secret_intendees) = DY.Crypto.pke_key_usage_pred (fun idx m -> True)

let is_pub_key_generated_for_client
  (pr:preds)
  (idx: nat)
  (client:principal)
  (pub_key:bytes)
 =
   exists (priv_key:bytes). is_labeled_p pr idx priv_key (readable_by (readers [any client]))  /\ DY.Crypto.pk priv_key == pub_key

let client_sent_newOrder_request_for_domains
  (client:principal)
  (domains: Seq.seq domain)
 =
 exists (set_order_st_idx:nat) (v:version_vec) (state:principal_state) (order_sessionid:nat).
 is_set_state_at set_order_st_idx client v state /\
 order_sessionid < Seq.length state /\
 ( match parse_acme_client_state state.[order_sessionid] with
    | Success (ACMEOrder order acc_idx _) -> (
        order.acme_order_identifiers = domains
      )
    | _ -> False
 )

//we just sign jws acme request, nothing else
let acme_sign_pred (sec_intendees:secret_intendees) (pr:preds) (idx:nat) (m:bytes) =
  exists (p:principal).   
   sec_intendees == readers [any p] /\
   (
     // We expect a JWS as "signature payload" here.
   match DY.Crypto.split m with
   | Success (nonce_bytes, snd_part) -> (
     match DY.Crypto.split snd_part with
     | Success (keyID_bytes, snd_part) -> (
         match DY.Crypto.split snd_part with
         | Success (url_bytes, payload_bytes) -> (
             match parse_acme_csr payload_bytes with
             | Success csr -> (
                 exists (set_csr_st_idx:nat).
                 client_stored_CSR p set_csr_st_idx csr.acme_csr_identifiers csr.acme_csr_pub_key /\
                 client_sent_newOrder_request_for_domains p csr.acme_csr_identifiers /\
                 idx > set_csr_st_idx /\ //temporal properties, saying that the signing was done AFTER client stored CSR in its state              
                 is_pub_key_generated_for_client pr idx p csr.acme_csr_pub_key
              )
            | _ -> True //other signing cases
          )
        | _ -> True
      )
     | _ -> True
   )
   | _ -> True
   )


let acme_sign_pred_lemma (sec_intendees:secret_intendees) (pr:preds) (idx:nat) (m:bytes):Lemma
 (requires True)
 (ensures acme_sign_pred sec_intendees pr idx m <==>(
   exists (client:principal).
   sec_intendees == readers [any client] /\
   ( match DY.Crypto.split m with
     | Success (nonce_bytes, snd_part) -> (
     match DY.Crypto.split snd_part with
     | Success (keyID_bytes, snd_part) ->(
        match DY.Crypto.split snd_part with
        | Success (url_bytes, payload_bytes) -> (
            match parse_acme_csr payload_bytes with
            | Success csr -> (
              (exists (set_csr_st_idx:nat) .
              client_stored_CSR client set_csr_st_idx csr.acme_csr_identifiers csr.acme_csr_pub_key /\
              client_sent_newOrder_request_for_domains client csr.acme_csr_identifiers /\
              //we need that to prove secrecy property
               idx > set_csr_st_idx /\
               is_pub_key_generated_for_client pr idx client csr.acme_csr_pub_key
              )
              )
            | _ -> True //other signing cases
          )
        | _ -> True
      )
     | _ -> True
    )
   | _ -> True
  )))
  [SMTPat (acme_sign_pred sec_intendees pr idx m)]
  = ()

val sign_pred_payload_lemma: i:nat -> sec_intendees:secret_intendees -> pr:preds -> m:bytes -> m': bytes ->
Lemma (eq_bytes m m' ==> (acme_sign_pred sec_intendees pr i m <==> acme_sign_pred sec_intendees pr i m'))
[SMTPat (acme_sign_pred sec_intendees pr i m); SMTPat (acme_sign_pred sec_intendees pr i m')]

(** Short for DC.sig_key_usage_pred (acme_sign_pred reader pr) - this is basically a usage predicate
for sig_key_usages. *)
unfold let acme_sig_key_usage (reader:secret_intendees) (pr:preds):DY.Crypto.usage_pred sig_key_usage = DY.Crypto.sig_key_usage_pred (acme_sign_pred reader pr)



let valid_acme_client_st
  (state:principal_state)
  (tr_idx:nat)
  (pr:preds)
  (p:principal)
  (st:acme_client_state)
  : Type0 =
  match st with
  | Account private_key account_url order_url ->
      is_sign_key_p pr tr_idx private_key (readable_by (readers [any p])) (acme_sig_key_usage (readers [any p]) pr) /\
      (can_label_of_bytes_flow_to pr tr_idx (serialize_url account_url ) public) /\
      (can_label_of_bytes_flow_to pr tr_idx (serialize_url order_url ) public)
  | HTTPSPendingRequest request_nonce reference_sessionid serv_dom ->
      can_label_of_bytes_flow_to pr tr_idx request_nonce (readable_by (readers [any p]))
  | ACMEOrder acme_order_object account_sessionid current_order_url ->
      (can_label_of_bytes_flow_to pr tr_idx (serialize_opt_url current_order_url ) public) /\
      can_label_of_bytes_flow_to pr tr_idx (serialize_acme_order acme_order_object ) public
  | ACMEAuthorziation acme_authorization_object acme_order_sessionid   ->
      (can_label_of_bytes_flow_to pr tr_idx (serialize_acme_authorization acme_authorization_object) public)
  | CSR cert_priv_key identifiers order_sessionid set_state_idx ->
      is_labeled_p pr tr_idx cert_priv_key (readable_by (readers [any p])) /\
      (exists (v:version_vec) (state:principal_state) (set_order_state_idx:nat) (newOrder_idx:nat).
        client_sent_newOrder_request p identifiers v state set_order_state_idx newOrder_idx
      ) /\
      is_valid_client_csr_session p identifiers order_sessionid set_state_idx /\
      set_state_idx <= tr_idx
  | RetrieveCertificate csr_sessionid ->
      csr_sessionid < Seq.length state /\
      //this session id points to a CSR session
      (match (parse_acme_client_state (state.[csr_sessionid])) with
       | Success (CSR _ _ _ _ ) -> True
       | _ -> False
      )
  | ReceivedCertificate certificate retrieve_cert_sessionid set_state_idx ->
      (can_label_of_bytes_flow_to pr tr_idx (serialize_acme_certificate certificate) public) /\
      is_valid_client_certificate_session p certificate retrieve_cert_sessionid set_state_idx /\
      set_state_idx <= tr_idx /\
      //[retrieve_cert_sessionid] points to a [RetrieveCertificate] session, which contains a session
      //id pointing to a [CSR] session containing the same identifiers as in the certificate.
      retrieve_cert_sessionid < Seq.length state /\
      (match (parse_acme_client_state (state.[retrieve_cert_sessionid])) with
       | Success (RetrieveCertificate ret_cert_sid) -> (
           ret_cert_sid < Seq.length state /\
           (match parse_acme_client_state (state.[ret_cert_sid]) with
            | Success (CSR csr_cert_priv_key csr_identifiers csr_acme_order_sessionid csr_trace_idx) ->
                is_same_set certificate.acme_certificate_identifiers csr_identifiers
            | _ -> False //[ret_cert_sid] points to a [CSR] session
           )
         )
       | _ -> False //[retrieve_cert_sessionid] points always to a [RetrieveCertificate] session
      )
  | ChallengeResponse authz_sessionid request_id -> is_publishable_p pr tr_idx request_id
  | ReplayNonce nonce valid _ -> is_publishable_p pr tr_idx nonce
  | ReplayNonceRequest _ -> True


#push-options "--max_fuel 0 --max_ifuel 0"
private let valid_acme_client_st_does_not_depend_on_server_sessions_specific
    (state1:principal_state)
    (state2:principal_state)
    (tr_idx:nat)
    (pr:preds)
    (p:principal)
    (st:acme_client_state)
  : Lemma
    (requires (
      Seq.length state1 = Seq.length state2 /\ (
      forall i.
      (
        i < Seq.length state1 /\
        (
          Success? (parse_acme_client_state state1.[i]) \/
          Success? (parse_acme_client_state state2.[i])
        )
       )
       ==>
       state1.[i] == state2.[i]
      )
    ))
    (ensures (
      valid_acme_client_st state1 tr_idx pr p st <==> valid_acme_client_st state2 tr_idx pr p st
    ))
  =
    match st with
    | RetrieveCertificate _ -> ()
    | ReceivedCertificate certificate retrieve_cert_sessionid set_state_idx -> (
      if not(retrieve_cert_sessionid < Seq.length state1) then () else
      match (parse_acme_client_state (state1.[retrieve_cert_sessionid])) with
      | Success (RetrieveCertificate ret_cert_sid) -> (
        assert(Success?.v (parse_acme_client_state (state2.[retrieve_cert_sessionid])) == (RetrieveCertificate ret_cert_sid));
        ()
      )
      | _ -> ()
    )
    | _ -> ()


let valid_acme_client_st_does_not_depend_on_server_sessions
    (state1:principal_state)
    (state2:principal_state)
    (tr_idx:nat)
    (pr:preds)
    (p:principal)
  : Lemma
    (requires (
      Seq.length state1 = Seq.length state2 /\ (
      forall i.
      (
        i < Seq.length state1 /\
        (
          Success? (parse_acme_client_state state1.[i]) \/
          Success? (parse_acme_client_state state2.[i])
        )
       )
       ==>
       state1.[i] == state2.[i]
      )
    ))
    (ensures (
      forall st.
      valid_acme_client_st state1 tr_idx pr p st <==> valid_acme_client_st state2 tr_idx pr p st
    ))
  =
    assert(forall st. valid_acme_client_st state1 tr_idx pr p st <==> valid_acme_client_st state2 tr_idx pr p st)
      by T.(
        let _ = forall_intro () in
        apply_lemma (`valid_acme_client_st_does_not_depend_on_server_sessions_specific)
      )
#pop-options


val valid_acme_client_st_later_lemma:
  (state:principal_state) ->
  (tr_idx:nat) ->
  (pr:preds) ->
  (p:principal) ->
  (st:acme_client_state) ->
   Lemma
   (requires valid_acme_client_st state tr_idx pr p st)
   (ensures forall (i:nat). later tr_idx i ==> valid_acme_client_st state i pr p st)
   [SMTPat (valid_acme_client_st state tr_idx pr p st)]


(*!
Most important predicate
*)
let is_valid_Certificate_session (pr:preds) (trace_index:nat) (set_cert_state_idx:nat) (cert:acme_certificate) (cert_url:url) (account_pub_key:bytes) =
  ( let cert_domains = cert.acme_certificate_identifiers in
   (
    (*
       either there is some client who sent the CSR
       to prove this at the server side, we need to enrich sign_pred
    *)
    (
      exists (client:principal) (set_csr_st_idx:nat).
      client_stored_CSR client set_csr_st_idx cert.acme_certificate_identifiers cert.acme_certificate_pub_key /\
      //client sent CSR before
      set_csr_st_idx < set_cert_state_idx /\
      client_sent_newOrder_request_for_domains client cert.acme_certificate_identifiers /\
      //client is the owner of the account public key
      is_verify_key_p pr set_cert_state_idx account_pub_key (readable_by (readers [any client])) (sig_key_usage_pred (acme_sign_pred (readers [any client]) pr))
    ) \/
    //or all of the owners of identifiers is dishonest. To prove this we need to use authenticated_predicate
    (
       forall (i:nat). i<Seq.length cert_domains ==>
       contains_corrupt_principal (pr.model.corrupt_at set_cert_state_idx) (readers [any (domain_principal_mapping (cert_domains.[i]))])
    )
   ) /\
   ( //if there is an honest domain owner, then it is the one who generated the certificate private key
     forall (i:nat). i<Seq.length cert_domains ==> (
         let client = domain_principal_mapping cert_domains.[i] in
         (~ (contains_corrupt_principal (pr.model.corrupt_at set_cert_state_idx) (readers [any client]))) ==>
         is_verify_key_p pr set_cert_state_idx account_pub_key (readable_by (readers [any client])) (sig_key_usage_pred (acme_sign_pred (readers [any client]) pr)) /\
           //we need that to prove secrecy property
           is_pub_key_generated_for_client pr set_cert_state_idx client cert.acme_certificate_pub_key
       )
   )
  )

val is_valid_Certificate_session_later_lemma:
 (pr:preds)-> 
 (trace_index:nat)->
 (set_cert_state_idx:nat)->
 (cert:acme_certificate)->
 (cert_url:url)->
 (account_pub_key:bytes)->
 Lemma
 (requires is_valid_Certificate_session pr trace_index set_cert_state_idx cert cert_url account_pub_key)
 (ensures forall (i:nat). later trace_index i ==> is_valid_Certificate_session pr i set_cert_state_idx cert cert_url account_pub_key)


let each_order_identifier_has_one_authorization
  (order:acme_order)
  (seq_authz_info: Seq.seq authorization_info)
 : Type0
 =
  forall (i:nat). i<Seq.length order.acme_order_identifiers ==>
    ( exists (j:nat).
         j < Seq.length seq_authz_info /\
         (seq_authz_info.[j]).authz_info_identifier = (order.acme_order_identifiers).[i]
    )

let order_status_is_Ready_implies_all_authorizations_are_Valid
  (order:acme_order)
  (seq_authz_info: Seq.seq authorization_info)
 :Type0
  =
  order.acme_order_status = Some Ready ==>
  ( forall (i:nat). i<Seq.length seq_authz_info ==>
       (seq_authz_info.[i]).authz_info_status = Valid
  )

let owner_of_domain_owns_public_key_or_corrupted
  (pr:preds)
  (trace_index:nat)
  (dom:domain)
  (acc_pub_key:bytes)
 :Type0
 =
  let dom_owner = domain_principal_mapping dom in
  is_verify_key_p pr trace_index acc_pub_key (readable_by (readers [any dom_owner])) (sig_key_usage_pred (acme_sign_pred (readers [any dom_owner]) pr)) \/
  contains_corrupt_principal (pr.model.corrupt_at trace_index) (readers [any dom_owner])


val  owner_of_domain_owns_public_key_or_corrupted_later_lemma:
  (pr:preds) ->
  (trace_index:nat) ->
  (dom:domain) ->
  (acc_pub_key:bytes) ->
  Lemma
  (requires owner_of_domain_owns_public_key_or_corrupted pr trace_index dom acc_pub_key)
  (ensures  forall (i:nat). later trace_index i ==> owner_of_domain_owns_public_key_or_corrupted pr i dom acc_pub_key )
  
  
let authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before
  (pr:preds)
  (trace_index:nat)
  (seq_authz_info:Seq.seq authorization_info)
  (acc_pub_key:bytes)
 : Type0
 =
  forall i. i< Seq.length seq_authz_info ==>
  ( (seq_authz_info.[i]).authz_info_status = Valid ==>
    owner_of_domain_owns_public_key_or_corrupted pr trace_index (seq_authz_info.[i]).authz_info_identifier acc_pub_key
  )

val  authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before_later_lemma:
  (pr:preds) ->
  (trace_index:nat)->
  (seq_authz_info:Seq.seq authorization_info) ->
  (acc_pub_key:bytes)->
  Lemma
  (requires authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before pr trace_index seq_authz_info acc_pub_key)
  (ensures forall (i:nat). later trace_index i ==> authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before pr i seq_authz_info acc_pub_key)
  [SMTPat (authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before pr trace_index seq_authz_info acc_pub_key)]

let is_valid_Order_session
  (pr:preds)
  (trace_index:nat)
  (order:acme_order)
  (seq_authz_info:Seq.seq authorization_info)
  (acc_pub_key:bytes)
 : Type0
 =
  each_order_identifier_has_one_authorization order seq_authz_info /\ 
  order_status_is_Ready_implies_all_authorizations_are_Valid order seq_authz_info /\ 
  authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before pr trace_index seq_authz_info acc_pub_key 


val is_valid_Order_session_later_lemma:
  (pr:preds) ->
  (trace_index:nat) ->
  (order:acme_order) ->
  (seq_authz_info:Seq.seq authorization_info) ->
  (acc_pub_key:bytes) ->
  Lemma
  (requires is_valid_Order_session pr trace_index order seq_authz_info acc_pub_key)
  (ensures forall (i:nat). later trace_index i ==> is_valid_Order_session pr i order seq_authz_info acc_pub_key)
  

let is_valid_ProcessingChallenge_session
 (server:principal)
 (authorization_sessionid: nat)
 (challenge_idx:nat)
 (http_request_id: bytes)
: Type0
=
 exists (state:principal_state) (v:version_vec) (tr_idx:nat).
 is_set_state_at tr_idx server v state /\
 ( authorization_sessionid < Seq.length state /\
             ( match parse_acme_server_state state.[authorization_sessionid] with
               | Success sti' ->
                 ( match sti' with
                   | Authorization  authz_url authorization order_sessionid ->
                     ( challenge_idx < Seq.length authorization.acme_authorization_challenges
                     )
                   | _ -> False
                 )
               | _ -> False
             )
           )


let valid_acme_server_st (pr:preds) (trace_index:nat) (p:principal) (st:acme_server_state) : Type0 =
  match st with
  | IssuedValidNonce t -> is_labeled_p pr trace_index t public
  | PrivateCAKey k -> is_sign_key_p pr trace_index k (readable_by (readers [any p])) (acme_sig_key_usage (readers [any p]) pr)
  | Order acme_order user_account_sessionid acc_url acc_pub_key seq_authz_info ->
      (can_label_of_bytes_flow_to pr trace_index (serialize_acme_order acme_order ) public) /\
      is_publishable_p pr trace_index (serialize_url acc_url) /\
      is_publishable_p pr trace_index acc_pub_key /\
      is_valid_Order_session pr trace_index acme_order seq_authz_info acc_pub_key
  | Authorization authorization_url authorization_object new_order_session_id ->
    (can_label_of_bytes_flow_to pr trace_index (serialize_acme_authorization authorization_object ) public) /\
    (can_label_of_bytes_flow_to pr trace_index (serialize_url authorization_url ) public)
  | Certificate set_state_cert_idx cert cert_url acc_pub_key ->
      is_valid_Certificate_session pr trace_index set_state_cert_idx cert cert_url acc_pub_key /\
      (can_label_of_bytes_flow_to pr trace_index (serialize_acme_certificate cert) public) /\
      (can_label_of_bytes_flow_to pr trace_index (serialize_url cert_url) public) /\
      is_publishable_p pr trace_index acc_pub_key
  | ProcessingChallenge authorization_sessionid challenge_idx http_request_id ->
      (can_label_of_bytes_flow_to pr trace_index http_request_id public)
  | UserAccount account public_key account_url ->
      is_publishable_p pr trace_index public_key /\
      is_publishable_p pr trace_index (serialize_acme_account account) /\
      is_publishable_p pr trace_index (serialize_url account_url)
  | _ -> False


val valid_acme_server_st_later_lemma :
  (pr:preds)-> 
  (trace_index:nat)-> 
  (p:principal) -> 
  (st:acme_server_state)->
  Lemma
  (requires valid_acme_server_st pr trace_index p st)
  (ensures forall (i:nat). later trace_index i ==> valid_acme_server_st pr i p st)
  [SMTPat (valid_acme_server_st pr trace_index p st)]
