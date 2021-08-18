/// ACME.Server.NewOrder (implementation)
/// ======================================
module ACME.Server.NewOrder


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

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"

#push-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"
(**
    Helper function that creates a new authorization object for one domain
    Returns authorization object along with a url for this object
*)
let create_acme_authorization_object
  (server_domain:domain)
  (client_dom:domain)
  : DYL (
      authz:acme_authorization *
      u:url
    )
    (requires (fun h0 -> True))
    (ensures (fun h0 (authz, u) h1 ->
      later (trace_len h0) (trace_len h1) /\
      is_publishable_p app_preds (trace_len h1) (serialize_acme_authorization authz) /\
      is_url_publishable app_preds (trace_len h1) u /\
      is_publishable_p app_preds (trace_len h1) (serialize_url u)
    ))
  =
    let len0 = current_trace_len () in
    let (|i1, challenge_id|) = guid_gen() in //used for the path of the challenge url
    let (|i2, token |) = guid_gen() in

    //let len_now = current_trace_len () in
    //assert(len_now = trace_len_h0 + 4);
    let len1 = current_trace_len () in
    assert(later len0 len1);
    let challenge_url = create_challenge_url len1 server_domain challenge_id in

    create_challenge_url_creates_urls_that_contain_no_secrets len1 server_domain challenge_id;
    assert(is_url_publishable app_preds len1 challenge_url);
    // create challenge object
    let challenge_object:acme_challenge = {acme_challenge_challenge_type = HTTP01; acme_challenge_url = challenge_url; acme_challenge_status = Pending; acme_challenge_token = token } in
    assert(acme_challenge_contains_no_secrets app_preds len1 challenge_object);

    // create sequence of challenges
    let challenge_seq_for_authz_object = Seq.create 1 challenge_object in
    Seq.Properties.lemma_contains_singleton challenge_object;
    assert(sequence_of_acme_challenges_contains_no_secrets app_preds len1 challenge_seq_for_authz_object);

    // create authorization object
    let authorization_object:acme_authorization = {acme_authorization_identifier = client_dom; acme_authorization_status = Pending; acme_authorization_challenges = Seq.create 1 challenge_object} in
    label_of_domain_flows_to_public app_preds len1 client_dom;
    assert(can_label_of_bytes_flow_to app_preds len1 (serialize_domain client_dom) public);
    serialized_acme_authorization_can_flow_to_public len1 authorization_object;
    assert(can_label_of_bytes_flow_to app_preds len1 (serialize_acme_authorization authorization_object ) public);
    let (|i2, authz_path_nonce|) = guid_gen () in
    let len2 = current_trace_len () in
    assert(later len1 len2);
    let authorization_url = create_authorization_url len2 server_domain authz_path_nonce in

    create_authorization_url_creates_urls_that_contain_no_secrets len2 server_domain authz_path_nonce;
    assert(is_url_publishable app_preds len2 authorization_url);
    label_of_url_flows_to_public app_preds len2 authorization_url;
    assert(can_label_of_bytes_flow_to app_preds len2 (serialize_url authorization_url ) public);
    later_is_transitive len0 len1 len2;
    assert(later len0 len2);
    (authorization_object, authorization_url)
#pop-options

private let simple_arith_helper_lemma (x:nat) (y:nat) (m:nat) (n:nat): Lemma
  (requires m = x - y - 1 /\ n = m+1)
  (ensures n = x - y)
  =()


#push-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"
(**
    Helper function that creates new authorization objects for a sequence of domains
*)
let rec create_acme_authorization_objects
  (server_domain:domain)
  (client_doms:(Seq.seq domain))
  (idx:nat{idx <= Seq.length client_doms})
  : DYL (
      authzs:Seq.seq (
        authz:acme_authorization *
        u:url
        ))
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 ->
      later (trace_len h0) (trace_len h1) /\
      (Seq.length r = Seq.length client_doms - idx) /\
      (forall (i:nat). i<Seq.length r ==>
          is_publishable_p app_preds (trace_len h1) (serialize_acme_authorization (fst (r.[i])) ) /\
          is_url_publishable app_preds (trace_len h1) (snd (r.[i])) /\
          is_publishable_p app_preds (trace_len h1) (serialize_url (snd (r.[i])))
      )
    ))
    (decreases (Seq.length client_doms - idx))
  =
   let len = Seq.length client_doms in
   assert(idx<=len);
    if idx = len then (
      let r = Seq.empty #(acme_authorization * url) in
      assert(Seq.length r = 0);
      r
    ) else (
      let authzs_tl = create_acme_authorization_objects server_domain client_doms (idx + 1) in
      let len_authzs_tl = Seq.length authzs_tl in
      let len_doms = Seq.length client_doms in
      assert(len_authzs_tl = len_doms - idx - 1);
      let len_now1 = current_trace_len () in
      assert( forall (i:nat). i< len_authzs_tl ==>
          is_publishable_p app_preds len_now1 (serialize_acme_authorization (fst (authzs_tl.[i])) ) /\
          is_url_publishable app_preds len_now1 (snd (authzs_tl.[i])) /\
          is_publishable_p app_preds len_now1 (serialize_url (snd (authzs_tl.[i])))
      );
      let authzs_hd = create_acme_authorization_object server_domain client_doms.[idx] in
      let len_now2 = current_trace_len () in
      assert(later len_now1 len_now2);
      assert(is_publishable_p app_preds len_now2 (serialize_acme_authorization (fst authzs_hd) ) /\
          is_url_publishable app_preds len_now2 (snd authzs_hd) /\
          is_publishable_p app_preds len_now2 (serialize_url (snd authzs_hd))
      );
      assert( forall (i:nat). i< len_authzs_tl ==>
          is_publishable_p app_preds len_now2 (serialize_acme_authorization (fst (authzs_tl.[i])) ) /\
          is_url_publishable app_preds len_now2 (snd (authzs_tl.[i])) /\
          is_publishable_p app_preds len_now2 (serialize_url (snd (authzs_tl.[i])))
      );
      let r = Seq.snoc authzs_tl authzs_hd in
      let len_r = Seq.length r in
      assert(forall i. i< len_authzs_tl ==> r.[i] == authzs_tl.[i]);
      seq_snoc_length_plus_one_lemma authzs_tl authzs_hd;
      assert(len_r = len_authzs_tl + 1);

      simple_arith_helper_lemma len_doms idx len_authzs_tl len_r;
      assert(len_r = len_doms - idx);
      assert(r.[len_authzs_tl] == authzs_hd);
      seq_snoc_length_lemma authzs_tl authzs_hd;
      assert(forall (i:nat). i< len_r ==> i < len_authzs_tl \/ i = len_authzs_tl);
      r
    )
#pop-options

#push-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
(**
    Helper function that extracts a sequence of urls from an authzs sequence
*)
let rec extract_urls_from_authzs
  (tr_idx:nat)
  (authzs:Seq.seq (
    authz:acme_authorization *
    u:url))
  (idx:nat{idx <= Seq.length authzs})
  :
  Pure (Seq.seq url)
  (requires
    forall (i:nat). i < Seq.length authzs ==>
    is_publishable_p app_preds tr_idx (serialize_acme_authorization (fst (authzs.[i])) ) /\
    is_url_publishable app_preds tr_idx (snd (authzs.[i])) /\
    is_publishable_p app_preds tr_idx (serialize_url (snd (authzs.[i])))
  )
  (ensures fun urls ->
    forall u . Seq.contains urls u ==> (is_url_publishable app_preds  tr_idx u /\ can_label_of_bytes_flow_to app_preds  tr_idx (serialize_url u) public)
  )
    (decreases (Seq.length authzs - idx))
  =
    if idx = Seq.length authzs then (
      let result = Seq.empty in
      lemma_contains_empty #url;
      result
    ) else (
      let urls_tl = extract_urls_from_authzs tr_idx authzs (idx + 1) in
      let urls_hd = snd authzs.[idx] in
      Seq.contains_snoc urls_tl urls_hd;
      Seq.snoc urls_tl urls_hd
    )
#pop-options


#push-options "--z3rlimit 250 --max_fuel 0 --max_ifuel 0"
(**
    Helper function for _acme_server_new_order.
    Returns the modified acme order and a sequence of  authorization objects with their respective urls.
*)
let _acme_server_new_order_helper
  (acme_order_object:acme_order)
  (server_domain:domain)
  :DYL (
      order:acme_order{ (order.acme_order_status = Some Pending)} *
      authzs:Seq.seq (
        authz:acme_authorization *
        u:url))
    (requires (fun h0 -> True))
    (ensures (fun h0 (order, authzs) h1 ->
      (*valid_trace h1 /\
      (trace_len h1 = trace_len h0 + 2 + (Prims.op_Multiply 6 (Seq.length (snd resp)))) /\
      (modifies_trace h0 h1) *)
      later (trace_len h0) (trace_len h1) /\
      Seq.length authzs = Seq.length acme_order_object.acme_order_identifiers  /\
      acme_order_is_publishable app_preds (trace_len h1) order /\
       ( forall (i:nat). i<Seq.length authzs ==>
          is_publishable_p app_preds (trace_len h1) (serialize_acme_authorization (fst (authzs.[i])) ) /\
          is_url_publishable app_preds (trace_len h1) (snd (authzs.[i])) /\
          is_publishable_p app_preds (trace_len h1) (serialize_url (snd (authzs.[i])))
      )
    ))
  =
    let (|i,finalize_path_nonce|) = guid_gen () in
    let len_now1 = current_trace_len () in
    let finalize_url = create_finalize_url len_now1 server_domain finalize_path_nonce in

    let identifiers = acme_order_object.acme_order_identifiers in
    let authzs = create_acme_authorization_objects server_domain identifiers 0 in
    let len_now2 = current_trace_len () in
    let authz_urls = extract_urls_from_authzs len_now2 authzs 0 in

    //create an updated order for the identifiers
    let updated_acme_order = {
        acme_order_status = Some Pending;
        acme_order_identifiers = identifiers;
        acme_order_authorizations = Some authz_urls;
        acme_order_finalize = Some finalize_url;
        acme_order_certificate = None} in

    //in the following, we show that the label of the updated_acme_order can flow to public
    label_of_domain_flows_to_public app_preds len_now2 server_domain;
    create_finalize_url_creates_urls_that_contain_no_secrets len_now2 server_domain finalize_path_nonce;
    assert(is_url_publishable app_preds len_now2 finalize_url);

    serialized_acme_order_flows_to_public len_now2 updated_acme_order;
    assert(can_label_of_bytes_flow_to app_preds len_now2 (serialize_acme_order updated_acme_order ) public);
    assert(acme_order_is_publishable app_preds len_now2 updated_acme_order);
    assert(Seq.length authzs = Seq.length acme_order_object.acme_order_identifiers);
    (updated_acme_order, authzs)
#pop-options


#push-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"
(**
  Helper function for creating a new [Order] session at the server state.
*)
let store_order_object_in_server_state
  (server:principal)
  (order:acme_order{order.acme_order_status = Some Pending})
  (acc_session_id:nat)
  (acc_url:url)
  (acc_pub_key:bytes)
  : DYL (order_sess_idx:nat)
  (requires (fun h0 ->
     is_publishable_p app_preds (trace_len h0) (serialize_acme_order order) /\
     is_publishable_p app_preds (trace_len h0) (serialize_url acc_url) /\
     is_publishable_p app_preds (trace_len h0) acc_pub_key
  ))
  (ensures (fun h0 resp h1 -> later (trace_len h0) (trace_len h1)))
  =
  let (|trace_index_of_last_set_state, current_version_vec, current_server_state|) = get_last_state server in
    // Store Order Object
    assert(order.acme_order_status <> Some Ready);
    let len_now1 = current_trace_len () in
    let seq_authz_info = generate_sequence_of_authorization_info_for_order len_now1 order acc_pub_key in
    let len_now2 = current_trace_len () in
    assert(is_valid_Order_session app_preds len_now2 order seq_authz_info acc_pub_key);
    let new_order_state_element = Order order acc_session_id acc_url acc_pub_key seq_authz_info in
    let serialized_new_order_state = serialize_acme_server_state new_order_state_element in
    let new_state = Seq.snoc current_server_state serialized_new_order_state in
    let new_version_vector = Seq.snoc current_version_vec 0 in
    let new_order_session_idx = (Seq.length new_version_vector) - 1 in
    assert(valid_acme_server_st app_preds len_now2 server new_order_state_element);
    state_with_new_valid_session_is_still_readable_by_server len_now2 server current_version_vec current_server_state new_order_state_element ;

    assert(forall i. i < Seq.length new_version_vector ==> is_session_state_readable len_now2 server i new_version_vector.[i] new_state.[i]);
    parse_acme_server_state_lemma new_order_state_element;
    //let len_now = current_trace_len () in
    state_invariant_remains_true_if_true_for_new_state len_now2 current_server_state serialized_new_order_state server current_version_vec;
    assert(Seq.length new_state = Seq.length new_version_vector);
    set_state server new_version_vector new_state;
    new_order_session_idx
#pop-options


#push-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
(**
  Helper function for creating a new [Authorization] session at the server state.
*)
let store_authz_object_to_server_state
  (server:principal)
  (authz_url:url)
  (authz:acme_authorization)
  (order_session_id:nat)
  : DYL unit
  (requires (fun h0 ->
    is_url_publishable app_preds (trace_len h0) authz_url /\
    can_label_of_bytes_flow_to app_preds (trace_len h0) (serialize_url authz_url) public /\
    can_label_of_bytes_flow_to app_preds (trace_len h0) (serialize_acme_authorization authz ) public
  ))
  (ensures (fun h0 _ h1 -> later (trace_len h0) (trace_len h1)))
  =
    let (|trace_index_of_last_set_state, current_version_vec, current_server_state|) = get_last_state server in
      // Store Authorization Object
      // the Authorization session points to the session that stores the corresponding order
      let (new_authorization_state_element:acme_server_state) = Authorization authz_url authz order_session_id in
      let serialized_new_authorization_state = serialize_acme_server_state new_authorization_state_element in
      let new_state = Seq.snoc current_server_state serialized_new_authorization_state in
      let new_version_vector = Seq.snoc current_version_vec 0 in
      let last_idx = (Seq.length new_version_vector) - 1 in
      let len_now = current_trace_len () in
      assert(can_label_of_bytes_flow_to app_preds len_now (nat_to_bytes order_session_id) public);
      assert(valid_acme_server_st app_preds len_now server new_authorization_state_element);
      state_with_new_valid_session_is_still_readable_by_server len_now server current_version_vec current_server_state new_authorization_state_element;
      assert(forall i. i < Seq.length new_version_vector ==> is_session_state_readable len_now server i new_version_vector.[i] new_state.[i]);
      //let len_now = current_trace_len () in
      assert(match parse_acme_server_state new_state.[(Seq.length current_version_vec)], parse_acme_client_state new_state.[(Seq.length current_version_vec)] with
        | Success sti, Error _ -> valid_acme_server_st app_preds len_now server sti
        | Error _, Success sti -> valid_acme_client_st new_state len_now app_preds server sti
        | _ -> False
      );
      assert(match parse_acme_server_state new_state.[(Seq.length current_version_vec)] with
        | Success sti -> valid_acme_server_st app_preds len_now server sti
        | _ -> False
      );
      state_invariant_remains_true_if_true_for_new_state len_now current_server_state serialized_new_authorization_state server current_version_vec;
      set_state server new_version_vector new_state
#pop-options

#push-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
(**
    Helper function to store multiple authorizations in server state
*)
let rec store_authzs_to_server_state
  (server:principal)
  (authzs:Seq.seq (
        authz:acme_authorization *
        u:url))
  (idx:nat{idx < Seq.length authzs})
  (order_session_id:nat)
  : DYL unit
  (requires (fun h0 ->
     forall (i:nat). i < Seq.length authzs ==>
     is_publishable_p app_preds (trace_len h0) (serialize_acme_authorization (fst (authzs.[i])) ) /\
    is_url_publishable app_preds  (trace_len h0) (snd (authzs.[i])) /\
    is_publishable_p app_preds  (trace_len h0) (serialize_url (snd (authzs.[i])))
  ))
  (ensures (fun h0 _ h1 -> later (trace_len h0) (trace_len h1)))
  (decreases (Seq.length authzs - idx))
  =
    let (authz, authz_url) = authzs.[idx] in
    store_authz_object_to_server_state server authz_url authz order_session_id;
    if idx + 1 < Seq.length authzs then (
      store_authzs_to_server_state server authzs (idx + 1) order_session_id
    ) else (
      ()
    )
#pop-options

#push-options "--z3rlimit 50 --max_fuel 1 --initial_fuel 1 --max_ifuel 0"
(**
  Helper function creating the response for [_acme_server_new_order].
*)
let _acme_server_new_order_create_response
  (tr_idx: nat)
  (req_id:bytes{is_publishable_p app_preds tr_idx req_id})
  (order:acme_order{is_publishable_p app_preds tr_idx (serialize_acme_order order)})
  : Tot (response:http_response{
        response.resp_status == HTTP_STATUS_201_CREATED
        /\ acme_order_in_http_response_is_publishable app_preds tr_idx response
        /\ is_publishable_p app_preds tr_idx (serialize_http_response response)
      })
  =
    let response = {
          resp_req_id = req_id;
          resp_status = HTTP_STATUS_201_CREATED;
          resp_headers = Seq.empty;
          resp_body = serialize_acme_order order
    } in
    assert(all_elements_of_http_response_are_publishable app_preds tr_idx response);
    label_of_http_response_can_flow_to_public app_preds tr_idx response;
    response
#pop-options


#push-options "--z3rlimit 200 --max_fuel 0 --initial_fuel 0 --max_ifuel 0"
let _acme_server_new_order server http_request =
  match parse_jws_acme_request http_request.req_body with
  | Error _ -> error "cannot parse jws acme request"
  | Success jws_acme_request_object -> (
    let len_now1 = current_trace_len () in
    http_request_is_publishable_implies_body_is_publishable app_preds len_now1 http_request;
    assert(is_publishable_p app_preds len_now1 http_request.req_body);
    parse_jws_acme_request_lemma_publishablity app_preds len_now1 http_request.req_body;
    serialize_parse_jws_acme_request_publishability_lemma app_preds len_now1 http_request.req_body;
    if (dfst (verify_jws_acme_request len_now1 http_request server jws_acme_request_object)) then (
      let kid = jws_acme_request_object.key_id in //this is the same as the account_url
      match parse_acme_order jws_acme_request_object.payload with
      | Error _ ->  error "cannot parse payload of jws acme request"
      | Success acme_order_object -> (
        let opt_user_account_session = retrieve_account_session_containing_account_url_from_server_st len_now1 server kid in
        //let h2 = ST.get() in
        //assert(h1 == h2);
        match opt_user_account_session with
        | None -> error "there is no account for incomming request"  // there is no user account for kid
                      //(as the verification of the jws was successful, this should never happen)
        | Some ((UserAccount account acc_pub_key acc_url), user_account_session_id) -> (
          //assert(user_account_session_id < Seq.length current_server_state);
          match get_header_from_headers "Host" http_request.req_headers 0 with //parse_acme_server_state (current_server_state.[user_account_session_id]) with
          | Some (host_header_key, host_header_value) -> (
            match parse_domain host_header_value with
            | Error _ -> error "cannot parse host header"
            | Success domain_from_req -> ( // this is a domain of the server
              let server_domain:domain = domain_from_req in
              assert(Seq.length acme_order_object.acme_order_identifiers > 0);
              let (updated_acme_order, authzs) =
                _acme_server_new_order_helper acme_order_object server_domain in
              assert(Seq.length authzs > 0);
              let len_now2 = current_trace_len () in
              assert(later len_now1 len_now2);
              assert(is_publishable_p app_preds len_now2 (serialize_url acc_url));
              assert(is_publishable_p app_preds len_now2 acc_pub_key);
              let new_order_session_idx = store_order_object_in_server_state
                  server
                  updated_acme_order
                  user_account_session_id
                  acc_url
                  acc_pub_key in
              let len_now3 = current_trace_len () in
              assert(later len_now2 len_now3);
              later_is_transitive len_now1 len_now2 len_now3;
              assert(later len_now1 len_now3);
                store_authzs_to_server_state server authzs 0 new_order_session_idx;
                http_request_is_publishable_implies_request_id_is_publishable app_preds len_now3 http_request;
                assert(is_publishable_p app_preds len_now3 http_request.req_id);
                let len_now4 = current_trace_len () in
                assert(later len_now3 len_now4);
              later_is_transitive len_now1 len_now3 len_now4;
              assert(later len_now1 len_now4);
                let (response:http_response{
                   response.resp_status == HTTP_STATUS_201_CREATED
                   /\ acme_order_in_http_response_is_publishable app_preds len_now4  response
                   /\ is_publishable_p app_preds len_now4 (serialize_http_response response)
                   }) =
                   _acme_server_new_order_create_response len_now4 http_request.req_id updated_acme_order in
                response
                //)
              )
             )
           | _ -> error "fail to create new order session on server state"
          )
        )
      )
    else error "the request object has an invalid signature" //the request object has an invalid signature
  )
#pop-options
