/// ACME.Server.FinalizeOrder (implementation)
/// ===============================================
module ACME.Server.FinalizeOrder

open Helpers
open DY.Monad
open DY.Entry
open Web.Messages
open DY.Labels
open DY.Principals
open DY.Crypto
open DY.Trace
open Labeled.Crypto
open Labeled.ApplicationAPI
open Application.Predicates.Helpers
open Application.Predicates
friend Application.Predicates
open Application.Predicates.Lemmas
open ACME.Data
open ACME.Data.SerializationHelpers


open SerializationHelpers
open SerializationLemmas

open ACME.Server.HelperFunctions
open ACME.Data.SerializationLemmas
open Application.Predicates.Helpers
open FStar.Seq

#push-options "--z3rlimit 50 --max_ifuel 8 --max_fuel 8"
(** Search for an acme_order with the given finalize_url in server's state and return the order and the session index of that order if found. *)
let rec retrieve_order_from_server_st
  (server:principal)
  (tr_idx:nat)
  (finalize_url:url)
  (session_index:nat)
  (current_version_vec:version_vec)
  (current_app_state:app_state tr_idx server current_version_vec)
  : Pure(result (acme_order * nat * nat))
       (requires (
         Seq.length current_version_vec = Seq.length current_app_state) /\
         state_inv tr_idx server current_version_vec current_app_state
       )
       (ensures (fun r ->
         match r with
         | Success (order, order_idx, account_idx) -> (
           Seq.length current_app_state > session_index /\
           Seq.length current_app_state > order_idx /\
           (can_label_of_bytes_flow_to app_preds tr_idx (serialize_acme_order (order) ) public) /\
           //the returned session id points to an order session:
           (Success? (parse_acme_server_state current_app_state.[order_idx])) /\
           Order? (Success?.v (parse_acme_server_state current_app_state.[order_idx]))
          )
         | Error _ -> True))
       (decreases (Seq.length current_version_vec - session_index))
  =
      if Seq.length current_version_vec <= session_index then
        Error "server: cannot retrieve order from state"
      else
        match parse_acme_server_state current_app_state.[session_index] with
        | Success (Order acme_order user_account_sessionid acc_url acc_pub_key seq_authz_info) -> (
            //the following assertions are needed for showing that the label
            //of the returned order can flow to public.
            assert(session_index < Seq.length current_version_vec);
            assert((
              match parse_acme_server_state current_app_state.[session_index], parse_acme_client_state current_app_state.[session_index] with
              | Success sti, Error _ -> valid_acme_server_st app_preds tr_idx server sti
              | Error _, Success sti -> valid_acme_client_st current_app_state tr_idx app_preds server sti
              | _ -> False
            ));
            assert(valid_acme_server_st app_preds tr_idx server (Order acme_order user_account_sessionid acc_url acc_pub_key seq_authz_info));
            match acme_order.acme_order_finalize with
            | None -> retrieve_order_from_server_st server tr_idx finalize_url (session_index + 1) current_version_vec current_app_state
            | Some finalize_url_in_state -> (
                if eq_url finalize_url_in_state finalize_url then (
                  Success (acme_order, session_index, user_account_sessionid)
                ) else
                  retrieve_order_from_server_st server tr_idx finalize_url (session_index + 1) current_version_vec current_app_state
              )
          )
        | _ -> retrieve_order_from_server_st server tr_idx finalize_url (session_index + 1) current_version_vec current_app_state

#pop-options

(**
  Helper function creating the response for [_acme_server_finalize_order].
*)
let _acme_server_finalize_order_create_response
  (len1: nat)
  (len2: nat {later len1 len2})
  (len3: nat {later len2 len3})
  (req: http_request{is_publishable_p app_preds len1 (serialize_http_request req)})
  (order: acme_order{is_publishable_p app_preds len2 (serialize_acme_order order)})
: Tot (response:http_response{is_publishable_p app_preds len3 (serialize_http_response response)})
  =
    let response = {
      resp_req_id = req.req_id;
      resp_status = HTTP_STATUS_200_OK;
      resp_headers = Seq.empty; 
      resp_body = serialize_acme_order order
    } in
    later_is_transitive len1 len2 len3;
    http_request_is_publishable_implies_request_id_is_publishable app_preds len1 req;
    is_publishable_p_later_lemma app_preds len1 req.req_id;
    is_publishable_p_later_lemma app_preds len2 (serialize_acme_order order);
    assert(all_elements_of_http_response_are_publishable app_preds len3 response);
    label_of_http_response_can_flow_to_public app_preds len3 response;
    response


#push-options "--z3rlimit 50 --max_ifuel 8 --max_fuel 8"
(**
  Helper function updating the order for [_acme_server_finalize_order].
*)
let _acme_server_finalize_order_update_order
    (tr_idx:nat)
    (server:principal)
    (server_domain:domain)
    (order:acme_order)
    (seq_authz_info:Seq.seq authorization_info)
    (acc_pub_key:bytes)
    (cert_path_nonce:lbytes_at tr_idx public)
  : Pure (updated_order:acme_order)
    (requires (
      is_publishable_p app_preds tr_idx (serialize_acme_order order) /\
      is_valid_Order_session app_preds tr_idx order seq_authz_info acc_pub_key ))
    (ensures (fun updated_order ->
       is_publishable_p app_preds tr_idx (serialize_acme_order updated_order) /\
       Some? updated_order.acme_order_certificate /\
       is_publishable_p app_preds tr_idx (serialize_url (Some?.v updated_order.acme_order_certificate)) /\
       is_valid_Order_session app_preds tr_idx updated_order seq_authz_info acc_pub_key
    ))
  =
    let cert_url = create_cert_url tr_idx server_domain cert_path_nonce in
    let updated_order:acme_order = {
      order with
      acme_order_status = Some Valid;
      acme_order_certificate = Some cert_url
    } in
    create_cert_url_creates_urls_that_contain_no_secrets tr_idx server_domain cert_path_nonce;
    label_of_url_flows_to_public app_preds tr_idx cert_url;
    serialized_updated_acme_order_flows_to_public tr_idx order cert_url;
    assert(is_valid_Order_session app_preds tr_idx updated_order seq_authz_info acc_pub_key);
    updated_order
#pop-options

#push-options "--z3rlimit 150 --max_ifuel 4 --max_fuel 4"
(**
  Helper function creating the signature for [_acme_server_finalize_order].
*)
let _acme_server_finalize_order_create_signature
    (tr_idx: nat)
    (acme_server_principal:principal)
    (pub_key_for_cert:bytes{is_publishable_p app_preds tr_idx pub_key_for_cert})
    (private_ca_key:bytes{is_sign_key_p app_preds tr_idx private_ca_key (readable_by (readers [any acme_server_principal])) (acme_sig_key_usage (readers [any acme_server_principal]) app_preds)})
    (identifiers:seq domain)
    (server_domain:domain)
  : Tot (signature:msg_p app_preds tr_idx public)
  =
    let serialized_identifiers = serialize_sequence_of_domains identifiers in
    let serialized_server_domain = serialize_domain server_domain in
    let signature_data = DY.Crypto.concat (DY.Crypto.concat pub_key_for_cert serialized_identifiers) serialized_server_domain in

    //signature_data is publishable:
    assert(can_label_of_bytes_flow_to app_preds tr_idx pub_key_for_cert public);
    serialized_sequence_of_domains_flows_to_public app_preds tr_idx identifiers;
    assert(can_label_of_bytes_flow_to app_preds tr_idx (serialize_sequence_of_domains identifiers) public);
    label_of_domain_flows_to_public app_preds tr_idx server_domain;
    assert(can_label_of_bytes_flow_to app_preds tr_idx(serialize_domain server_domain) public);
    concatenation_of_publishable_bytes_is_publishable_forall app_preds ;
    assert(can_label_of_bytes_flow_to app_preds tr_idx signature_data public);
    let sig_label = get_label signature_data in
    let public_signature_data:msg_at tr_idx public  = signature_data in
    assert(is_sign_key_p app_preds tr_idx private_ca_key (readable_by (readers [any acme_server_principal])) (acme_sig_key_usage (readers [any acme_server_principal]) app_preds));
    let signature =
       sign
       #tr_idx
       #(readable_by (readers [any acme_server_principal]))
       #(acme_sig_key_usage (readers [any acme_server_principal]) app_preds)
       #public
       private_ca_key public_signature_data in
    signature
#pop-options

#push-options "--z3rlimit 50 --max_ifuel 2 --max_fuel 4"
(**
  Helper function adding a Certificate session to the server state.
*)
let _acme_server_finalize_order_add_certificate_session
    (tr_idx:nat)
    (server:principal)
    (set_cert_state_idx:nat)
    (cert:acme_certificate{is_publishable_p app_preds tr_idx (serialize_acme_certificate cert) })
    (acc_pub_key:bytes{is_publishable_p app_preds tr_idx acc_pub_key})
    (cert_url:url{is_valid_Certificate_session app_preds tr_idx set_cert_state_idx cert cert_url acc_pub_key /\ is_publishable_p app_preds tr_idx (serialize_url cert_url)})
    (v:version_vec)
    (current_state:app_state tr_idx server v{state_inv tr_idx server v current_state})
  : Tot (new_state:app_state tr_idx server (Seq.snoc v 0){
      state_inv tr_idx server (Seq.snoc v 0) new_state /\
      (forall i. i < Seq.length current_state ==> (current_state.[i] == new_state.[i])) /\
      Seq.length current_state + 1 = Seq.length new_state
    })
  =
    let cert_session_st = Certificate set_cert_state_idx cert cert_url acc_pub_key in
    let serialized_cert_session_st = (serialize_acme_server_state cert_session_st) in
    let new_state = Seq.snoc current_state serialized_cert_session_st in
    let v' = Seq.snoc v 0 in
    concatenation_of_publishable_bytes_is_publishable_forall app_preds;
    assert(can_label_of_bytes_flow_to app_preds tr_idx (serialize_acme_certificate cert) public);
    assert(valid_acme_server_st app_preds tr_idx server cert_session_st);
    state_with_new_valid_session_is_still_readable_by_server tr_idx server v current_state cert_session_st;
    assert(is_principal_state_readable tr_idx server v' new_state);
    state_invariant_remains_true_if_true_for_new_state tr_idx current_state
      (serialize_acme_server_state cert_session_st) server v;
    assert(state_inv tr_idx server v' new_state);
    new_state
#pop-options

(**
  Helper function updating the Order session and setting the state.
*)
#push-options "--z3rlimit 350 --max_fuel 4 --max_ifuel 0"
let _acme_server_finalize_order_set_order_state
    (acme_server_principal:principal)
    (updated_order:acme_order)
    (order_sess_idx:nat)
    (account_sess_idx:nat)
    (acc_url:url)
    (acc_pub_key:bytes)
    (seq_authz_info:Seq.seq authorization_info)
    (v:version_vec)
    (old_state: principal_state)
  : DYL unit
    (requires (fun h0 ->
      is_publishable_p app_preds (trace_len h0) (serialize_acme_order updated_order) /\
      is_publishable_p app_preds (trace_len h0) (serialize_url acc_url) /\
      is_publishable_p app_preds (trace_len h0) acc_pub_key /\
      (account_sess_idx < Seq.length v) /\
      state_inv (trace_len h0) acme_server_principal v old_state /\
      is_principal_state_readable (trace_len h0) acme_server_principal v old_state /\
      (order_sess_idx < Seq.length old_state) /\
      (Success? (parse_acme_server_state old_state.[order_sess_idx])) /\
      (Order? (Success?.v (parse_acme_server_state old_state.[order_sess_idx]))) /\
      is_valid_Order_session app_preds (trace_len h0) updated_order seq_authz_info acc_pub_key
    ))
    (ensures (fun h0 _ h1 -> later (trace_len h0) (trace_len h1)
    ))
  =
    let updated_order_ss = Order updated_order account_sess_idx acc_url acc_pub_key seq_authz_info in
    let updated_order_session = serialize_acme_server_state updated_order_ss in
    let newer_state = old_state.[order_sess_idx] <- updated_order_session in
    let len_now = current_trace_len () in
    assert(valid_acme_server_st app_preds len_now acme_server_principal updated_order_ss);
    state_with_updated_valid_session_is_still_readable_by_server len_now acme_server_principal v old_state updated_order_session order_sess_idx;
    state_invariant_remains_true_if_true_for_updated_server_state len_now old_state updated_order_session  acme_server_principal v order_sess_idx;
    assert(state_inv len_now acme_server_principal v newer_state);
    set_state acme_server_principal v newer_state
#pop-options

val _acme_server_finalize_order_helper:
  acme_server_principal:principal ->
  request:http_request ->
  DYL (
    pub_key_for_cert: bytes *
    identifiers_from_csr:Seq.seq domain *
    verify_key: bytes *
    finalize_url: url *
    cert_path_nonce:bytes *
    jws_acme_request_object: jws_acme_request
  )
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_request request))
  (ensures fun h0 (pub_key_for_cert, identifiers_from_csr, verify_key, finalize_url,  cert_path_nonce, jws_acme_request_object) h1 ->
    is_labeled_p app_preds (trace_len h1) cert_path_nonce public /\
    is_publishable_p app_preds (trace_len h1) pub_key_for_cert /\
    is_valid_p app_preds (trace_len h1) verify_key /\
    (  let signed_msg = generate_message_for_jws_signature jws_acme_request_object.key_id jws_acme_request_object.url jws_acme_request_object.replay_nonce jws_acme_request_object.payload in
       forall ps. is_verify_key_p app_preds  (trace_len h1) verify_key (readable_by ps) (acme_sig_key_usage ps app_preds) ==>
		            (contains_corrupt_principal (corrupt_at (trace_len h1)) ps \/
			     acme_sign_pred ps app_preds  (trace_len h1) signed_msg)
    ) /\
    (match parse_acme_csr jws_acme_request_object.payload with
        | Error _ -> False
        | Success csr_object -> (
           pub_key_for_cert == csr_object.acme_csr_pub_key /\
           identifiers_from_csr = csr_object.acme_csr_identifiers
        )
    ) /\
    later (trace_len h0) (trace_len h1)
  )

#push-options "--z3rlimit 350 --max_fuel 4 --max_ifuel 4"
let _acme_server_finalize_order_helper acme_server_principal request =
  let (|i, cert_path_nonce|) = guid_gen () in
  let len_now = current_trace_len () in
  assert(later i len_now);
  //is_publishable_p_later_lemma app_preds i cert_path_nonce;
  //is_publishable_p_later_lemma app_preds i (serialize_http_request request);
  http_request_is_publishable_implies_request_id_is_publishable app_preds len_now request;
  assert(is_publishable_p app_preds len_now request.req_id);
  http_request_publishable_implies_payload_of_jws_publishable app_preds len_now request;
  assert(payload_of_jws_in_http_request_is_publishable app_preds len_now request);
  concatenation_publishable_implies_components_publishable_forall app_preds;
  match parse_jws_acme_request request.req_body with
  | Error _ -> error "server: not jws request"
  | Success jws_acme_request_object -> (
      assert(is_publishable_p app_preds len_now request.req_body);
      serialize_parse_jws_acme_request_publishability_lemma app_preds len_now request.req_body;
      assert(is_publishable_p app_preds len_now (serialize_jws_acme_request jws_acme_request_object));
      let (|verify_r, o_verify_key|) = verify_jws_acme_request len_now request acme_server_principal jws_acme_request_object in
      if verify_r then (
        http_request_publishable_implies_payload_of_jws_publishable app_preds len_now request;
        assert(is_publishable_p app_preds len_now jws_acme_request_object.payload);
        assert(Some? o_verify_key);
        let verify_key = Some?.v o_verify_key in
        let s_csr_object = jws_acme_request_object.payload in
        match parse_acme_csr s_csr_object with
        | Error _ -> error "server: CSR is invalid"
        | Success csr_object -> (
          let pub_key_for_cert = csr_object.acme_csr_pub_key in
          let identifiers_from_csr = csr_object.acme_csr_identifiers in
          parse_acme_csr_publishablity_lemma app_preds len_now jws_acme_request_object.payload;
          assert(is_publishable_p app_preds len_now pub_key_for_cert);
          // Retrieve order object (by request url == order finalize url)
          let finalize_url = jws_acme_request_object.url in
           (pub_key_for_cert, identifiers_from_csr, verify_key, finalize_url,  cert_path_nonce, jws_acme_request_object)
        )
      ) else (
        error "server: cannot finalize order"
      )
    )


let _acme_server_finalize_order_helper2
  (acme_server_principal:principal)
  (request:http_request)
 : DYL (
   updated_order: acme_order *
   order_sess_idx: nat *
   account_sess_idx: nat *
   acc_url: url *
   acc_pub_key: bytes *
   seq_authz_info: Seq.seq authorization_info *
   v: version_vec *
   new_state: principal_state

 )
  (requires fun h0 ->  is_publishable_p app_preds (trace_len h0) (serialize_http_request request))
  (ensures fun h0 (updated_order, order_sess_idx, account_sess_idx, acc_url, acc_pub_key, seq_authz_info, v, new_state) h1 ->
     later (trace_len h0) (trace_len h1) /\
     is_publishable_p app_preds (trace_len h1) (serialize_acme_order updated_order) /\
      is_publishable_p app_preds (trace_len h1) (serialize_url acc_url) /\
      is_publishable_p app_preds (trace_len h1) acc_pub_key /\
      (account_sess_idx < Seq.length v) /\
      state_inv (trace_len h1) acme_server_principal v new_state /\
      is_principal_state_readable (trace_len h1) acme_server_principal v new_state /\
      (order_sess_idx < Seq.length new_state) /\
      (Success? (parse_acme_server_state new_state.[order_sess_idx])) /\
      (Order? (Success?.v (parse_acme_server_state new_state.[order_sess_idx]))) /\
      is_valid_Order_session app_preds (trace_len h1) updated_order seq_authz_info acc_pub_key
  )
  =
  let (pub_key_for_cert, identifiers_from_csr, verify_key, finalize_url, cert_path_nonce, jws_acme_request_object) = _acme_server_finalize_order_helper acme_server_principal request in
  let (|len_now, v, current_state|) = get_last_state acme_server_principal in
          match retrieve_order_from_server_st acme_server_principal len_now finalize_url 0 v current_state with
          | Error err_msg  -> error err_msg
          | Success (_, order_sess_idx, account_sess_idx) -> (
            // Verify that the JWS is signed by the right account
            // note that verify_jws_acme_request checked whether the JWS is signed with key_id
            assert(order_sess_idx < Seq.length current_state);
            if account_sess_idx >= Seq.length current_state then
              error "server: cannot finalize order"
            else(
              match parse_acme_server_state current_state.[order_sess_idx] with
              | Success (Order order acc_sessionid acc_url acc_pub_key seq_authz_info) -> (
                assert(is_publishable_p app_preds len_now (serialize_url acc_url));
                assert( is_publishable_p app_preds len_now acc_pub_key);
                if //eq_url acc_url jws_acme_request_object.key_id &&
                   eq_bytes acc_pub_key verify_key &&
                   Some? order.acme_order_status &&
                   (Some?.v order.acme_order_status) = Ready &&
                   order.acme_order_identifiers = identifiers_from_csr
                then (
                    let server_domain = finalize_url.url_domain in
                  // Update order object

                    let updated_order = _acme_server_finalize_order_update_order len_now acme_server_principal server_domain order seq_authz_info acc_pub_key cert_path_nonce in
                    let cert_url = Some?.v (updated_order.acme_order_certificate) in

                    // create and store cert in state such that it can be retrieved later
                    let identifiers = order.acme_order_identifiers in
                  //get the private ca key for signing the certificate
                      let opt_si_and_private_ca_key = retrieve_private_ca_key_from_server_st len_now acme_server_principal v current_state in
                      match opt_si_and_private_ca_key with
                      | None ->  error "server: cannot finalize order"
                      | Some (private_ca_key_si, private_ca_key) -> (
                        assert(state_inv len_now acme_server_principal v current_state);
                        assert(is_sign_key_p app_preds len_now private_ca_key (readable_by (readers [any acme_server_principal])) (acme_sig_key_usage (readers [any acme_server_principal]) app_preds));
                        let signature = _acme_server_finalize_order_create_signature
                                          len_now
                                          acme_server_principal
                                          pub_key_for_cert
                                          private_ca_key
                                          identifiers
                                          server_domain in

                        let cert:acme_certificate = {
                          acme_certificate_pub_key = pub_key_for_cert;
                          acme_certificate_identifiers = identifiers;
                          acme_certificate_issuer = server_domain;
                          acme_certificate_signature = signature;
                        } in

                        assert(is_publishable_p app_preds len_now pub_key_for_cert);
                        assert(is_publishable_p app_preds len_now signature);

                        label_of_domain_flows_to_public app_preds len_now server_domain;
                        concatenation_of_publishable_bytes_is_publishable_forall app_preds;
                        concatenation_publishable_implies_components_publishable_forall app_preds;
                        assert(is_publishable_p app_preds len_now (serialize_sequence_of_domains identifiers));
                        assert(is_publishable_p app_preds len_now (serialize_acme_certificate cert));

                        assert(is_publishable_p app_preds len_now (serialize_url cert_url));
                        (* proof structure *)
                        let signed_msg = generate_message_for_jws_signature jws_acme_request_object.key_id jws_acme_request_object.url jws_acme_request_object.replay_nonce jws_acme_request_object.payload in
                        generate_message_for_jws_signature_returns_concat jws_acme_request_object.key_id jws_acme_request_object.url jws_acme_request_object.replay_nonce jws_acme_request_object.payload;
                        assert(signed_msg == DY.Crypto.concat jws_acme_request_object.replay_nonce (DY.Crypto.concat (serialize_url jws_acme_request_object.key_id) (DY.Crypto.concat (serialize_url jws_acme_request_object.url) jws_acme_request_object.payload)));
                        assert(forall ps. is_verify_key_p app_preds len_now verify_key (readable_by ps) (acme_sig_key_usage ps app_preds) ==>
		            (contains_corrupt_principal (corrupt_at len_now) ps \/
			     acme_sign_pred ps app_preds len_now signed_msg));
                        assert(is_valid_p app_preds len_now acc_pub_key);
                        assert(is_valid_p app_preds len_now verify_key);                 
                        assert(acc_pub_key == verify_key);
                        assert(forall ps.
                            is_verify_key_p app_preds len_now acc_pub_key (readable_by ps) (acme_sig_key_usage ps app_preds) ==>
		            ( acme_sign_pred ps app_preds len_now signed_msg \/
                              contains_corrupt_principal (corrupt_at len_now) ps
                            ));
                         assert(forall (ps:secret_intendees).
                                 is_verify_key_p app_preds len_now acc_pub_key (readable_by ps) (acme_sig_key_usage ps app_preds) ==>
                                  (
                                    (
                                      exists (client:principal).
                                      ps == (readers [any client]) /\ //in the honest case, there is only one client who signed the message
                                      (exists (set_csr_st_idx:nat) .
                                      client_stored_CSR client set_csr_st_idx cert.acme_certificate_identifiers cert.acme_certificate_pub_key /\
                                      client_sent_newOrder_request_for_domains client cert.acme_certificate_identifiers /\
                                      is_pub_key_generated_for_client app_preds len_now client cert.acme_certificate_pub_key /\
                                      set_csr_st_idx < len_now

                                      )
                                     )
                                    ) \/
                                    contains_corrupt_principal (app_preds.model.corrupt_at len_now) ps

                                  );

                        assert(is_valid_Order_session app_preds len_now order seq_authz_info acc_pub_key /\ order.acme_order_status = Some Ready);
                        ready_Order_session_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corrupted len_now order  seq_authz_info acc_pub_key;
                        assert (forall (i:nat). i<Seq.length identifiers ==> (
                          let client = domain_principal_mapping identifiers.[i] in
                          is_verify_key_p app_preds len_now acc_pub_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds) \/
                          contains_corrupt_principal (app_preds.model.corrupt_at len_now) (readers [any client])
                        )); 
                        achieve_valid_Certifiate_sesison_lemma len_now acc_pub_key cert cert_url len_now;
                        assert(is_valid_Certificate_session app_preds len_now len_now cert cert_url acc_pub_key);
                        assert(state_inv len_now acme_server_principal v current_state);
                        let new_state = _acme_server_finalize_order_add_certificate_session len_now acme_server_principal len_now cert acc_pub_key cert_url v current_state in
                        let v' = Seq.snoc v 0 in


                        // Store updated order
                        assert(Success? (parse_acme_server_state current_state.[order_sess_idx]));
                        assert(order_sess_idx < Seq.length new_state);
                        assert(Success? (parse_acme_server_state new_state.[order_sess_idx]));

                        assert(Order? (Success?.v (parse_acme_server_state new_state.[order_sess_idx])));
                        assert(is_publishable_p app_preds len_now (serialize_acme_order updated_order));
                        assert(is_valid_Order_session app_preds len_now updated_order seq_authz_info acc_pub_key);
                        
                        (updated_order, order_sess_idx, account_sess_idx, acc_url, acc_pub_key, seq_authz_info, v', new_state)
                        )
                ) else  error "server: cannot finalize order"
               )
              | _ ->  error "server: cannot finalize order"
             )
            )


let _acme_server_finalize_order acme_server_principal request =
  let len1 = current_trace_len () in
  let (updated_order, order_sess_idx, account_sess_idx, acc_url, acc_pub_key, seq_authz_info, v', new_state) = _acme_server_finalize_order_helper2 acme_server_principal request in
  let len2 = current_trace_len () in
  _acme_server_finalize_order_set_order_state acme_server_principal updated_order order_sess_idx account_sess_idx acc_url acc_pub_key seq_authz_info v' new_state;
  let len3 = current_trace_len () in
  let response = _acme_server_finalize_order_create_response len1 len2 len3 request updated_order in
  response


#pop-options

