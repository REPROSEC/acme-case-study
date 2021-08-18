/// ACME.SecurityProperties
/// =======================
///
/// This module contains the definitions and proofs of the security properties presented in the
/// paper, in particular, the secure binding theorem and the two integrity properties.
///
/// We additionally prove several other properties, e.g., that the private key of an (honest) ACME
/// server never leaks (see ``private_CA_key_of_honest_server_does_not_leak_lemma``), or that the
/// domains of a certificate that the client receives (and stores in its state) were previously
/// contained in a CSR created by the client (see
/// ``certificate_of_client_corresponds_to_csr_stored_by_client_lemma``).
///
/// Note that these properties are actually properties of ``valid_trace``, and as such do not
/// directly depend on the ACME protocol implementation (though they are linked to the
/// implementation through the ``valid_trace`` predicate).

module ACME.SecurityProperties

open Helpers
open DY.Monad
open DY.Entry
open Labeled.Crypto
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Labeled.ApplicationAPI
open Application.Predicates


open SerializationHelpers
open SerializationLemmas

open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas

open Application.Predicates.Helpers
open FStar.Seq


(*!
 Helper predicates
*)
val is_order_and_authorization_info_in_server_state:
  server: principal ->
  order:acme_order ->
  seq_authz_info:Seq.seq authorization_info ->
  acc_pub_key:bytes ->
  set_order_st_idx:nat ->
  v:version_vec ->
  state: principal_state ->
  order_sessionid:nat ->
  Type0


(**
  True, if the client stores the certificate at a [ReceivedCertificate] session at session index
  [received_cert_sessionid], together with [retrieve_cert_sessionid], and if the corresponding [state]
  was set at trace index [cert_set_state_idx].
*)
val client_stores_certificate_in_state:
  client:principal->
  state:principal_state ->
  v:version_vec ->
  certificate:acme_certificate ->
  received_cert_sessionid:nat ->
  retrieve_cert_sessionid:nat ->
  cert_set_state_idx:nat ->
  Type0


(**
  True, if the client sets a [state] containing a CSR session at trace index [set_state_idx],
  and if this CSR session contains the [identifiers], the [acme_order_sessionid], and the
  [set_state_idx].
*)
val client_stores_csr_information_in_state:
  client:principal->
  state:principal_state ->
  v:version_vec ->
  identifiers:Seq.seq domain -> //identifiers stored in the csr session
  acme_order_sessionid:nat -> //corresponding order session. The sessionid is stored in the csr session
  csr_sessionid:nat -> //session index at which the csr information is stored
  set_state_idx:nat -> //trace index at which the state was set when storing the CSR
  Type0


(**
  True, if the identifiers and public key of the certificate are the same as in the corresponding
  CSR used previously by the client. The session id of the CSR session is stored at a
  [RetrieveCertificate] session stored at [retrieve_cert_sessionid].

  The CSR must be contained in a state that was set before the trace index [cert_set_state_idx].
*)
val certificate_corresponds_to_csr_stored_previously:
  client:principal->
  certificate:acme_certificate ->
  cert_set_state_idx:nat ->
  retrieve_cert_sessionid:nat ->
  Type0


(**
  True, if the [identifiers] are contained in an ACMEOrder session (located at [order_sessionid]) of
  a state that was set before the trace index [csr_set_state_idx].
*)
val domains_previously_stored_in_order:
  client:principal->
  identifiers:Seq.seq domain ->
  csr_set_state_idx:nat ->
  order_sessionid:nat ->
  Type0


val is_certificate_in_server_state:
   (server:principal)->
   set_cert_state_idx:nat ->
   v_cert:version_vec->
   state_cert:principal_state ->
   cert_session:nat ->
   (certificate:acme_certificate)->  // The issued certificate
   Type0


val is_domain_in_certificate:
  certificate:acme_certificate ->
  dom:domain ->
  cert_identifier_idx:nat->
  Type0


val server_issues_certificate_for_domain_with_account_key:
   (server:principal)->
   set_cert_state_idx:nat ->
   v_cert:version_vec->
   state_cert:principal_state ->
   cert_session:nat ->
   (certificate:acme_certificate)->  // The issued certificate
   (acc_pub_key:bytes) -> //account public key used to verify requests for certificate
   (cert_dom:domain) -> //one domain of the certificate
   (cert_dom_idx:nat) -> //index of the domain in the list of certificate identifiers
   cert_url:url -> //url to get certificate
   Type0


val is_private_CA_key_in_server_state:
  server: principal ->
  set_ca_idx: nat ->
  v_ca:version_vec ->
  state_ca:principal_state ->
  ca_sessionid:nat ->
  priv_ca_key:bytes ->
  Type0



(*!
Integrity properties
*)


/// Integrity properties
/// --------------------
///
/// Intuition: A certificate should only be issued if the receiver of that certificate actually
/// "wanted" that certificate, i.e., "ordered" it.
///
/// We do this in two steps:
///
///   - If a client receives a certificate, that client sent a certificate signing request for that
///     certificate (same set of domains, same key) before.
///   - If a client receives a certificate, that client sent a newOrder request for the same set of
///     domains before.
///
/// This ensures integrity of both the list of identifiers as well as the key that is signed in the
/// certificate.


(**
  If the client stores the given [identifiers] and [acme_order_sessionid] in a CSR session, then the
  [identifiers] were previously stored in an ACMEOrder session.
*)
val csr_stored_by_client_corresponds_to_order_stored_by_client:
  client:principal ->
  state:principal_state ->
  v:version_vec ->
  csr_set_state_idx:nat -> //trace index at which the state was set when storing the CSR
  csr_sessionid:nat -> //session index at which the csr information is stored
  identifiers:Seq.seq domain -> //identifiers stored in the csr session
  acme_order_sessionid:nat -> //corresponding order session. This sessionid is stored in the csr session
  DYL unit
  (requires (fun h0 -> (
    client_stores_csr_information_in_state client state v identifiers acme_order_sessionid csr_sessionid csr_set_state_idx
  )))
  (ensures (fun h0 _ h1 -> (
    h0 == h1 /\
    domains_previously_stored_in_order client identifiers csr_set_state_idx acme_order_sessionid
  )))


(**
  If the client stores the the given [certificate] (along with [retrieve_cert_sessionid]), then the
  identifiers and the public key of the certificate are stored in a CSR session (which the client
  used for sending a CSR). The CSR session is contained in a state set by the client before saving
  the certificate.

  [retrieve_cert_sessionid] is stored together with the certificate and points to a
  [RetrieveCertificate] session. This session contains the session id of the session at which the
  private key and identifiers used for the CSR are stored.
*)
val certificate_of_client_corresponds_to_csr_stored_by_client_lemma:
  client:principal ->
  state:principal_state ->
  v:version_vec ->
  cert_set_state_idx:nat -> //trace index at which the state was set when receiving the certificate
  received_cert_sessionid:nat -> //session index at which the certificate is stored
  certificate:acme_certificate ->
  retrieve_cert_sessionid:nat ->
  DYL unit
  (requires (fun h0 -> (
    client_stores_certificate_in_state client state v certificate received_cert_sessionid retrieve_cert_sessionid cert_set_state_idx
  )))
  (ensures (fun h0 _ h1 -> (
    h0 == h1 /\
    certificate_corresponds_to_csr_stored_previously client certificate cert_set_state_idx retrieve_cert_sessionid
  )))


val each_order_identifier_has_one_authorization_lemma:
  server: principal ->
  order:acme_order ->
  seq_authz_info:Seq.seq authorization_info ->
  acc_pub_key:bytes ->
  set_order_st_idx:nat ->
  v:version_vec ->
  state: principal_state ->
  order_sessionid:nat ->
  DYL unit
  (requires fun h ->
     is_order_and_authorization_info_in_server_state server order seq_authz_info acc_pub_key set_order_st_idx v state order_sessionid /\
     set_order_st_idx < trace_len h
  )
  (ensures fun h0 _ h1 ->
     h0 == h1 /\
     each_order_identifier_has_one_authorization order seq_authz_info
  )


val order_status_is_Ready_implies_all_authorizations_are_Valid_lemma:
  server: principal ->
  order:acme_order ->
  seq_authz_info:Seq.seq authorization_info ->
  acc_pub_key:bytes ->
  set_order_st_idx:nat ->
  v:version_vec ->
  state: principal_state ->
  order_sessionid:nat ->
  DYL unit
  (requires fun h ->
     is_order_and_authorization_info_in_server_state server order seq_authz_info acc_pub_key set_order_st_idx v state order_sessionid /\
     set_order_st_idx < trace_len h
  )
  (ensures fun h0 _ h1 ->
     h0 == h1 /\
     order_status_is_Ready_implies_all_authorizations_are_Valid order seq_authz_info
  )


val authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before_lemma:
  server: principal ->
  order:acme_order ->
  seq_authz_info:Seq.seq authorization_info ->
  acc_pub_key:bytes ->
  set_order_st_idx:nat ->
  v:version_vec ->
  state: principal_state ->
  order_sessionid:nat ->
  DYL unit
  (requires fun h ->
     is_order_and_authorization_info_in_server_state server order seq_authz_info acc_pub_key set_order_st_idx v state order_sessionid /\
     set_order_st_idx < trace_len h
  )
  (ensures fun h0 _ h1 ->
     h0 == h1 /\
     authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before app_preds (trace_len h1) seq_authz_info acc_pub_key
  )


val certificate_issued_by_honest_server_implies_client_sent_CSR_or_domain_owner_corruption_lemma:
   server:principal->
   set_cert_state_idx:nat ->
   v_cert:version_vec->
   state_cert:principal_state ->
   cert_session:nat ->
   certificate:acme_certificate->
   DYL unit
   (requires fun h ->
      is_certificate_in_server_state server set_cert_state_idx v_cert state_cert cert_session certificate
   )
   (ensures fun h0 _ h1 ->
      h0 == h1 /\
      ( let cert_domains = certificate.acme_certificate_identifiers in
        (exists (client:principal) (set_csr_st_idx:nat).
           client_stored_CSR client set_csr_st_idx cert_domains certificate.acme_certificate_pub_key
        ) \/
        ( forall (i:nat). i<Seq.length cert_domains ==>
       contains_corrupt_principal (app_preds.model.corrupt_at (trace_len h1)) (readers [any (domain_principal_mapping (cert_domains.[i]))])
        )
      )
   )


(**
This is the server-side integrity property as described in Section 7.2 of the paper.

If a server issues a certificate for a domain owned an by honest principal, then:
 - the owner of that domain has sent new Order request for the all domains in certificate
 - the owner of that domain also the account public key used to verify the request
*)
val server_side_integrity_property:
   server:principal->
   set_cert_state_idx:nat ->
   v_cert:version_vec->
   state_cert:principal_state ->
   cert_sessionid:nat ->
   certificate:acme_certificate->
   acc_pub_key:bytes -> //account public key used to verify requests for certificate
   cert_dom:domain -> //one domain of the certificate
   cert_dom_idx:nat -> //index of the domain in the list of certificate identifiers
   cert_url:url ->
   DYL unit
   (requires fun h ->
      server_issues_certificate_for_domain_with_account_key server set_cert_state_idx v_cert state_cert cert_sessionid certificate acc_pub_key cert_dom cert_dom_idx cert_url /\
      //the owner of domain stays honest
      (~ (contains_corrupt_principal (app_preds.model.corrupt_at (trace_len h)) (readers [any (domain_principal_mapping cert_dom)])))
   )
   (ensures fun h0 _ h1 ->
      h0 == h1 /\
      ( let client = domain_principal_mapping cert_dom in
           client_sent_newOrder_request_for_domains client certificate.acme_certificate_identifiers /\
           //the client owns the account public key used to verify request
           is_verify_key_p app_preds (trace_len h1) acc_pub_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds)
      )
   )


(**
This is the client-side integrity property as described in Section 7.2 of the paper.

If a client stores a certificate, then it follows that the client previously created an ACME order
with the same domains as in the certificate.
*)
val client_side_integrity_property:
  client:principal ->
  state:principal_state ->
  v:version_vec ->
  cert_set_state_idx:nat -> //trace index at which the state was set when receiving the certificate
  received_cert_sessionid:nat -> //session index at which the certificate is stored
  certificate:acme_certificate ->
  retrieve_cert_sessionid:nat ->
  DYL unit
  (requires (fun h0 -> (
    client_stores_certificate_in_state client state v certificate received_cert_sessionid retrieve_cert_sessionid cert_set_state_idx
  )))
  (ensures (fun h0 _ h1 -> (
    h0 == h1 /\
   //The identifiers of the certificate were previously (i.e., at a trace index smaller than
   //[cert_set_state_idx]) stored in the ACMEOrder session identified by
   //[retrieve_cert_sessionid]. (This session id points to a RetrieveCertificate session, which
   //contains a pointer to a CSR session, which then points to the corresponding ACMEOrder session.
    retrieve_cert_sessionid < Seq.length state /\
    (match parse_acme_client_state (state.[retrieve_cert_sessionid]) with
      | Success (RetrieveCertificate csr_sessionid) -> (
        if(csr_sessionid >= Seq.length state) then False else (
          match parse_acme_client_state (state.[csr_sessionid]) with
          | Success (CSR _ _ csr_acme_order_sessionid _) -> (
            domains_previously_stored_in_order client certificate.acme_certificate_identifiers cert_set_state_idx csr_acme_order_sessionid
            )
          | _ -> False
        )
        )
      | _ -> False
    )
  )))


(*!
Secrecy property
*)

/// Private keys of "honest" certificates are not derivable by the attacker
/// -----------------------------------------------------------------------
///
/// The intuitive property we want to show is: If an ACME server :math:`s` issues a certificate with
/// public key :math:`k_{cert} := pk(\hat{k}_{cert})` for a set :math:`D` of domains, it must hold
/// true that either :math:`\hat{k}_{cert}` is secret (i.e., not derivable by the attacker) OR
/// either the server :math:`s` or all owners of domains in :math:`D` are corrupted.
///
/// More formally, we want to show (note that we denote the issuing server with :math:`s`):
///
/// .. math::
///
///   \forall\ \text{issued certificates}\ c = \left(k_c := pk(\hat{k}_c), D := [d_1, \ldots, d_n], sign(\langle k_c, D\rangle, \hat{k}_{s})\right)
///
///   \left((\exists d_i \in D: \text{owner of }d_i\text{ is honest}) \land s\text{ is honest} \Longrightarrow \hat{k}_c \text{ not derivable by attacker} \right)
///
/// Note that the private key must be kept secret even if one of the domain owners is corrupted (but
/// not if all owners are corrupted).

(**
This is the Secure Binding property as described in Section 7.1 of the paper.

The private key for a certificate that is valid for an honest domain must be secret (unless the
issuing server is compromised before).
*)
val secure_binding_theorem:
   (server:principal)->
   set_cert_state_idx:nat ->
   v_cert:version_vec->
   state_cert:principal_state ->
   cert_session:nat ->
   (certificate:acme_certificate)->  // The issued certificate
   dom:domain ->
   cert_identifier_idx:nat->
   cert_priv_key:bytes ->
  DYL unit
    (requires (fun h0 -> (
      is_certificate_in_server_state server set_cert_state_idx v_cert state_cert cert_session certificate /\
      is_domain_in_certificate certificate dom cert_identifier_idx /\
      DY.Crypto.pk cert_priv_key == certificate.acme_certificate_pub_key /\
      (~(contains_corrupt_principal_before set_cert_state_idx (app_preds.model.corrupt_at set_cert_state_idx)(readers [any server])))
    )))
    (ensures (fun h0 _ h1 -> (
      h0 == h1 /\ (
        // Either the certificate's private key is secret or ...
        DY.AttackerAPI.is_unknown_to_attacker_at (trace_len h0) cert_priv_key \/
        // ... the owner of the certificate domain is compromised. Note that this property must hold
        // for all inputs to this lemma - i.e., we don't need to check _all_ domain owners here, if
        // there is at least one honest domain owner, we have to show that either the server is
        contains_corrupt_principal (app_preds.model.corrupt_at (trace_len h0)) (readers [(any (domain_principal_mapping dom))])
      )
    )))


(**
Private CA key of honest server is secret
*)
val private_CA_key_of_honest_server_does_not_leak_lemma:
  server: principal ->
  set_ca_idx: nat ->
  v_ca:version_vec ->
  state_ca:principal_state ->
  ca_sessionid:nat ->
  priv_ca_key:bytes ->
 DYL unit
  (requires fun h -> set_ca_idx < trace_len h /\ is_private_CA_key_in_server_state server set_ca_idx v_ca state_ca ca_sessionid priv_ca_key)
  (ensures fun h0 _ h1 ->
     h0 == h1 /\
     (  //either the private CA key is unknown to the attacker
       DY.AttackerAPI.is_unknown_to_attacker_at (trace_len h0) priv_ca_key \/
        //or the server is corrupted
       contains_corrupt_principal (app_preds.model.corrupt_at (trace_len h0)) (readers [(any server)])
     )
  )
