/// ACME.SecurityProperties (implementation)
/// ========================================
module ACME.SecurityProperties

open Application.Predicates.Helpers
friend Application.Predicates
open Labeled.SecrecyLemmas

#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 50"

let is_order_and_authorization_info_in_server_state server order seq_authz_info acc_pub_key set_order_st_idx v state order_sessionid =
  is_set_state_at set_order_st_idx server v state /\
  order_sessionid < Seq.length state /\
  ( match parse_acme_server_state (state.[order_sessionid]) with
    | Success (Order acme_order user_account_sessionid acc_url acc_pub_key' seq_authz_info') -> (
        acc_pub_key' == acc_pub_key /\
        seq_authz_info' == seq_authz_info /\
        acme_order == order
      )
    | _ -> False
  )


let client_stores_certificate_in_state client state v certificate received_cert_sessionid retrieve_cert_sessionid cert_set_state_idx =
  is_set_state_at cert_set_state_idx client v state /\
  received_cert_sessionid < Seq.length state /\
  (match parse_acme_client_state (state.[received_cert_sessionid]) with
    | Success (ReceivedCertificate cert sid tr_idx) -> (
        certificate == cert /\
        retrieve_cert_sessionid = sid
      )
    | _ -> False
  )


let client_stores_csr_information_in_state client state v identifiers acme_order_sessionid csr_sessionid set_state_idx =
  is_set_state_at set_state_idx client v state /\
  csr_sessionid < Seq.length state /\
  (match parse_acme_client_state (state.[csr_sessionid]) with
    | Success (CSR _ csr_identifiers csr_acme_order_sessionid csr_set_state_idx) -> (
      csr_identifiers = identifiers /\
      csr_acme_order_sessionid = acme_order_sessionid
      )
    | _ -> False
  )


let certificate_corresponds_to_csr_stored_previously client certificate cert_set_state_idx retrieve_cert_sessionid =
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


let domains_previously_stored_in_order client identifiers csr_set_state_idx order_sessionid =
  exists (order_trace_idx:nat) (order_v:version_vec) (order_state:principal_state).
  order_trace_idx < csr_set_state_idx /\
  is_set_state_at order_trace_idx client order_v order_state /\
  order_sessionid  < Seq.length order_state /\
  (match parse_acme_client_state (order_state.[order_sessionid]) with
    | Success (ACMEOrder order _ _) -> (
      is_same_set identifiers order.acme_order_identifiers
      )
    | _ -> False
  )


let is_certificate_in_server_state server set_cert_state_idx v_cert state_cert cert_sessionid certificate =
  is_set_state_at set_cert_state_idx server v_cert state_cert /\
  cert_sessionid < Seq.length state_cert /\
  ( match parse_acme_server_state (state_cert.[cert_sessionid]) with
    | Success (Certificate set_cert_state_idx' cert cert_url acc_pub_key) -> (
        certificate == cert /\
        set_cert_state_idx' <= set_cert_state_idx
      )
    | _ -> False
  )


let is_domain_in_certificate certificate dom cert_identifier_idx =
  cert_identifier_idx < Seq.length (certificate.acme_certificate_identifiers) /\
  dom = (certificate.acme_certificate_identifiers).[cert_identifier_idx]


let server_issues_certificate_for_domain_with_account_key
  server set_cert_state_idx v_cert state_cert cert_sessionid certificate acc_pub_key cert_dom cert_dom_idx cert_url =
  is_set_state_at set_cert_state_idx server v_cert state_cert /\
  cert_sessionid < Seq.length state_cert /\
  ( match parse_acme_server_state (state_cert.[cert_sessionid]) with
    | Success (Certificate set_cert_state_idx' cert cert_url' acc_pub_key') -> (
        certificate == cert /\
        set_cert_state_idx' <= set_cert_state_idx /\
        acc_pub_key' == acc_pub_key /\
        is_domain_in_certificate certificate cert_dom cert_dom_idx /\
        cert_url' == cert_url
      )
    | _ -> False
  )


let is_private_CA_key_in_server_state server set_ca_idx v_ca state_ca ca_sessionid priv_ca_key =
  is_set_state_at set_ca_idx server v_ca state_ca /\
  ca_sessionid < Seq.length state_ca /\
  ( match parse_acme_server_state (state_ca.[ca_sessionid]) with
    | Success (PrivateCAKey k) -> k == priv_ca_key
    | _ -> False
  )


#push-options "--z3rlimit 150 --max_fuel 2 --max_ifuel 0"
let csr_stored_by_client_corresponds_to_order_stored_by_client client state v csr_set_state_idx csr_sessionid identifiers acme_order_sessionid =
  is_set_state_at_implies_set_state_before_now csr_set_state_idx client v state;
  match(parse_acme_client_state (state.[csr_sessionid])) with
  | Success sti -> (
    match sti with
    | CSR priv_key csr_identifiers csr_acme_order_sessionid set_state_idx -> ()
    | _ -> ()
    )
  | _ -> ()
#pop-options


#push-options "--z3rlimit 150 --max_fuel 2 --max_ifuel 0"
let certificate_of_client_corresponds_to_csr_stored_by_client_lemma
    client
    state
    v
    cert_set_state_idx
    received_cert_sessionid
    certificate
    retrieve_cert_sessionid
  =
    is_set_state_at_implies_set_state_before_now cert_set_state_idx client v state;
    assert(exists (v:version_vec). is_set_state_at cert_set_state_idx client v state);
    match(parse_acme_client_state (state.[received_cert_sessionid])) with
    | Success sti -> (
      match sti with
      | ReceivedCertificate cert retr_cert_sid set_state_idx -> (
        assert(cert_set_state_idx >= set_state_idx);
        assert(is_valid_client_certificate_session client certificate retrieve_cert_sessionid cert_set_state_idx)
        )
      | _ -> ()
      )
    | _ -> ()
#pop-options


let each_order_identifier_has_one_authorization_lemma server order seq_authz_info acc_pub_key set_order_st_idx v state order_sessionid =
   is_set_state_at_implies_set_state_before_now set_order_st_idx server v state


let order_status_is_Ready_implies_all_authorizations_are_Valid_lemma server order seq_authz_info acc_pub_key set_order_st_idx v state order_sessionid =
   is_set_state_at_implies_set_state_before_now set_order_st_idx server v state


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before_lemma
  server order seq_authz_info acc_pub_key set_order_st_idx v state order_sessionid =
   is_set_state_at_implies_set_state_before_now set_order_st_idx server v state;
   assert(state_inv set_order_st_idx server v state);
   assert(authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before app_preds set_order_st_idx seq_authz_info acc_pub_key);
   let len_now = current_trace_len () in
   assert(set_order_st_idx < len_now);
   assert(authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before app_preds len_now seq_authz_info acc_pub_key)


let certificate_issued_by_honest_server_implies_client_sent_CSR_or_domain_owner_corruption_lemma
server set_cert_state_idx v_cert state_cert cert_sessionid certificate =
  is_set_state_at_implies_set_state_before_now set_cert_state_idx server v_cert state_cert
#pop-options


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let server_side_integrity_property
  server
  set_cert_state_idx
  v_cert
  state_cert
  cert_sessionid
  certificate
  acc_pub_key
  cert_dom
  cert_dom_idx
  cert_url
  =
  assert(server_issues_certificate_for_domain_with_account_key server set_cert_state_idx v_cert state_cert cert_sessionid certificate acc_pub_key cert_dom cert_dom_idx cert_url);
  assert(is_set_state_at set_cert_state_idx server v_cert state_cert);
  is_set_state_at_implies_set_state_before_now set_cert_state_idx server v_cert state_cert;
  assert(is_valid_Certificate_session app_preds set_cert_state_idx set_cert_state_idx certificate cert_url acc_pub_key);
  let len_now = current_trace_len () in
  assert(later set_cert_state_idx len_now);
  assert(is_valid_Certificate_session app_preds len_now set_cert_state_idx certificate cert_url acc_pub_key);
  let client = domain_principal_mapping cert_dom in
  assert( is_verify_key_p app_preds set_cert_state_idx acc_pub_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));
  assert( is_verify_key_p app_preds len_now acc_pub_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));
  assert(~ (contains_corrupt_principal (app_preds.model.corrupt_at (len_now)) (readers [any client])));
  assert(~ (contains_corrupt_principal (app_preds.model.corrupt_at set_cert_state_idx) (readers [any client])));
  assert(
      exists (client1:principal) (set_csr_st_idx:nat).
      client_stored_CSR client1 set_csr_st_idx certificate.acme_certificate_identifiers certificate.acme_certificate_pub_key /\
      client_sent_newOrder_request_for_domains client1 certificate.acme_certificate_identifiers /\
      //client is the owner of the account public key
      is_verify_key_p app_preds set_cert_state_idx acc_pub_key (readable_by (readers [any client1])) (sig_key_usage_pred (acme_sign_pred (readers [any client1]) app_preds))
    );
  assert(
      exists (client1:principal).
      client_sent_newOrder_request_for_domains client1 certificate.acme_certificate_identifiers /\
      //client is the owner of the account public key
      is_verify_key_p app_preds set_cert_state_idx acc_pub_key (readable_by (readers [any client1])) (sig_key_usage_pred (acme_sign_pred (readers [any client1]) app_preds))
    );
  assert(
      exists (client1:principal).
      client_sent_newOrder_request_for_domains client1 certificate.acme_certificate_identifiers /\
      //client is the owner of the account public key
      is_verify_key_p app_preds set_cert_state_idx acc_pub_key (readable_by (readers [any client1])) (sig_key_usage_pred (acme_sign_pred (readers [any client1]) app_preds)) /\
      client1 = client
    );
  assert(client_sent_newOrder_request_for_domains client certificate.acme_certificate_identifiers)
#pop-options


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let client_side_integrity_property
  client
  state
  v
  cert_set_state_idx
  received_cert_sessionid
  certificate
  retrieve_cert_sessionid
  =
    certificate_of_client_corresponds_to_csr_stored_by_client_lemma client state v cert_set_state_idx received_cert_sessionid certificate retrieve_cert_sessionid;
    assert(certificate_corresponds_to_csr_stored_previously client certificate cert_set_state_idx retrieve_cert_sessionid);
    is_set_state_at_implies_set_state_before_now cert_set_state_idx client v state;

    assert(received_cert_sessionid < Seq.length state);
    match parse_acme_client_state (state.[received_cert_sessionid]) with
      | Success (ReceivedCertificate cert sid tr_idx) -> (
        assert(sid = retrieve_cert_sessionid);
        assert(sid < Seq.length state);
        match parse_acme_client_state (state.[retrieve_cert_sessionid]) with
        | Success (RetrieveCertificate csr_sessionid) -> (
          assert(csr_sessionid < Seq.length state);
          if(csr_sessionid >= Seq.length state) then () else (
            match parse_acme_client_state (state.[csr_sessionid]) with
           | Success (CSR csr_cert_priv_key csr_identifiers csr_acme_order_sessionid csr_trace_idx) -> (
             assert(is_same_set csr_identifiers certificate.acme_certificate_identifiers);
             assert(domains_previously_stored_in_order client csr_identifiers csr_trace_idx csr_acme_order_sessionid) 
             )
           | _ -> ()
          )
          )
        | _ -> ()
        )
      | _ -> ()
#pop-options


#push-options "--z3rlimit 250 --max_fuel 4 --max_ifuel 4"
let secure_binding_theorem server set_cert_state_idx v_cert state_cert cert_sessionid certificate dom cert_identifier_idx cert_priv_key =
    let len_now = current_trace_len () in
    let client = domain_principal_mapping dom in
    let cert_domains = certificate.acme_certificate_identifiers in
    let cert_pub_key = certificate.acme_certificate_pub_key in
    let Success (Certificate set_cert_state_idx' cert cert_url acc_pub_key) = parse_acme_server_state (state_cert.[cert_sessionid]) in
    is_set_state_at_implies_set_state_before_now set_cert_state_idx server v_cert state_cert ;
    assert(state_inv set_cert_state_idx server v_cert state_cert);
    assert(is_valid_Certificate_session app_preds len_now set_cert_state_idx' cert cert_url acc_pub_key);
    assert(cert == certificate);
    pk_injective_lemma_forall cert_priv_key;
    assert(is_pub_key_generated_for_client app_preds set_cert_state_idx client cert_pub_key \/ contains_corrupt_principal (app_preds.model.corrupt_at set_cert_state_idx) (readers [any client]));
    assert((exists (priv_key:bytes). is_labeled_p app_preds set_cert_state_idx priv_key (readable_by (readers [any client])) /\ DY.Crypto.pk priv_key == cert_pub_key) \/ contains_corrupt_principal (app_preds.model.corrupt_at set_cert_state_idx) (readers [any client]));

    assert(forall (priv_key:bytes). DY.Crypto.pk priv_key == cert_pub_key ==> DY.Crypto.pk priv_key == DY.Crypto.pk cert_priv_key);
     assert(forall (priv_key:bytes). DY.Crypto.pk priv_key == cert_pub_key ==> priv_key == cert_priv_key);

    assert(is_labeled_p app_preds set_cert_state_idx cert_priv_key (readable_by (readers [any client]))  \/ contains_corrupt_principal (app_preds.model.corrupt_at set_cert_state_idx) (readers [any client]));
    assert(is_labeled_p app_preds len_now cert_priv_key (readable_by (readers [any client]))  \/ contains_corrupt_principal (app_preds.model.corrupt_at set_cert_state_idx) (readers [any client]));
    conditional_secrecy_lemma cert_priv_key (readers [any client])
#pop-options


let private_CA_key_of_honest_server_does_not_leak_lemma server set_ca_idx v_ca state_ca ca_sessionid priv_ca_key =
  secrecy_lemma priv_ca_key (readers [any server])
