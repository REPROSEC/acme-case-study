/// ACME.Server.HelperFunctions
/// ============================
module ACME.Server.HelperFunctions

module LC = Labeled.Crypto
open Web.Messages
module DC = DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open DY.Monad
module LA = Labeled.ApplicationAPI
open Application.Predicates.Helpers
open Application.Predicates
open ACME.Data
open ACME.Data.Predicates
open ACME.Data.SerializationHelpers
open HelperFunctions
open Helpers
open SerializationHelpers
open SerializationLemmas
open ACME.Data.SerializationLemmas
open FStar.Seq

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

(**
  Returns the domain that is contained in the 'Host' header of the http request.
*)
let get_domain_from_request
  (http_request:http_request)
: result domain
=
  match get_header_from_headers "Host" http_request.req_headers 0 with
  | None -> Error "No Host header"
  | Some (host_header_key, host_header_value) -> parse_domain host_header_value

/// Helper Functions for Creating URLs
/// -----------------------------------
/// The following functions create the urls needed by the server.

(**
  Helper function creating a URL corresponding to https://[server_domain]/acme/authz/[authz_path_nonce]
*)
let create_authorization_url
      (trace_index:nat)
      (server_domain:domain)
      (authz_path_nonce:LA.lbytes_at trace_index public)
    : Tot url =
      let authz_path = init_seq_bytes_with_list [DC.string_to_bytes "acme"; DC.string_to_bytes "authz"; authz_path_nonce] in
      let authz_request_uri = {
        uri_path = authz_path;
        uri_querystring = Seq.empty;
        uri_fragment = Some (DC.string_to_bytes "")} in
      let authorization_url = {
        url_scheme = HTTPS;
        url_domain = server_domain;
        url_request_uri = authz_request_uri} in
      authorization_url

(**
  Helper function creating a URL corresponding to https://[server_domain]/acme/order/[finalize_path_nonce]/finalize
*)
let create_finalize_url
      (trace_index:nat)
      (server_domain:domain)
      (finalize_path_nonce:LA.lbytes_at trace_index public)
    : Tot url =
      let finalize_path_list = [DC.string_to_bytes "acme"; DC.string_to_bytes "order"; finalize_path_nonce; DC.string_to_bytes "finalize"] in
      let finalize_path = init_seq_bytes_with_list finalize_path_list in
      let finalize_request_uri = {
        uri_path = finalize_path;
        uri_querystring = Seq.empty;
        uri_fragment = Some (DC.string_to_bytes "")} in
      let finalize_url = {
        url_scheme = HTTPS;
        url_domain = server_domain;
        url_request_uri = finalize_request_uri} in
      finalize_url

(**
  Helper function creating a URL corresponding to https://[server_domain]/acme/chall/[challenge_id]
*)
let create_challenge_url
     (trace_index:nat)
     (server_domain:domain)
     (challenge_id:LA.lbytes_at trace_index public)
   : Tot url =
     let challenge_path = init_seq_bytes_with_list [DC.string_to_bytes "acme"; DC.string_to_bytes "chall"; challenge_id] in
     let challenge_request_uri = {
       uri_path = challenge_path;
       uri_querystring = Seq.empty;
       uri_fragment = Some (DC.string_to_bytes "")} in
     let challenge_url = {
       url_scheme = HTTPS;
       url_domain = server_domain;
       url_request_uri = challenge_request_uri} in
     challenge_url

(**
  Helper function creating a URL corresponding to https://[server_domain]/acme/cert/[cert_path_nonce]
*)
let create_cert_url
      (trace_index:nat)
      (server_domain:domain)
      (cert_path_nonce:LA.lbytes_at trace_index public)
    : Tot url =
      let cert_path_list = [DC.string_to_bytes "acme"; DC.string_to_bytes "cert"; cert_path_nonce] in
      let cert_path = init_seq_bytes_with_list cert_path_list in
      let cert_request_uri = {
        uri_path = cert_path;
        uri_querystring = Seq.empty;
        uri_fragment = None
      } in
      let cert_url = {
        url_scheme = HTTPS;
        url_domain = server_domain;
        url_request_uri = cert_request_uri
      } in
      cert_url

/// Lemmas on Functions for Creating URLs
/// --------------------------------------
/// The following lemmas show that the URLs that are created by the helper functions fulfill
/// [url_contains_no_secrets]. For URLs that fulfill this predicate, [label_of_url_flows_to_public]
/// shows that the label of the serialized URLs can also flow to public.

#push-options "--z3rlimit 25 --max_fuel 5 --max_ifuel 0"
(**
    Lemma stating that urls created by create_authorization_url contain no secrets (according to
    [is_url_publishable]).
*)
let create_authorization_url_creates_urls_that_contain_no_secrets
      (trace_index:nat)
      (server_domain:domain)
      (auth_path_nonce:LA.lbytes_at trace_index public)
    : Lemma (is_url_publishable app_preds trace_index (create_authorization_url trace_index server_domain auth_path_nonce))
    =
      let authorize_path_list = [DC.string_to_bytes "acme"; DC.string_to_bytes "authz"; auth_path_nonce] in
      init_seq_with_list_equivalence_of_list_and_sequence #DC.bytes authorize_path_list
#pop-options

#push-options "--z3rlimit 25 --max_fuel 5 --max_ifuel 0"
(**
    Lemma stating that urls created by create_finalize_url contain no secrets (according to
    [is_url_publishable]).
*)
let create_finalize_url_creates_urls_that_contain_no_secrets
      (trace_index:nat)
      (server_domain:domain)
      (finalize_path_nonce:LA.lbytes_at trace_index public)
    : Lemma (is_url_publishable app_preds trace_index (create_finalize_url trace_index server_domain finalize_path_nonce))
    =
      let finalize_path_list = [
        DC.string_to_bytes "acme";
        DC.string_to_bytes "order";
        finalize_path_nonce;
        DC.string_to_bytes "finalize"] in
      init_seq_with_list_equivalence_of_list_and_sequence #DC.bytes finalize_path_list
#pop-options

#push-options "--z3rlimit 25 --max_fuel 5 --max_ifuel 0"
(**
    Lemma stating that urls created by create_challenge_url contain no secrets (according to
    [is_url_publishable app_preds]).
*)
let create_challenge_url_creates_urls_that_contain_no_secrets
      (trace_index:nat)
      (server_domain:domain)
      (challenge_id:LA.lbytes_at trace_index public)
    : Lemma (is_url_publishable app_preds trace_index (create_challenge_url trace_index server_domain challenge_id))
    =
      let challenge_path_list = [DC.string_to_bytes "acme"; DC.string_to_bytes "chall"; challenge_id] in
      init_seq_with_list_equivalence_of_list_and_sequence #DC.bytes challenge_path_list
#pop-options

#push-options "--z3rlimit 25 --max_fuel 5 --max_ifuel 0"
(**
    Lemma stating that urls created by create_cert_url contain no secrets (according to
    [is_url_publishable app_preds]).
*)
let create_cert_url_creates_urls_that_contain_no_secrets
      (trace_index:nat)
      (server_domain:domain)
      (cert_path_nonce:LA.lbytes_at trace_index public)
    : Lemma (is_url_publishable app_preds trace_index (create_cert_url trace_index server_domain cert_path_nonce))
    =
      let cert_path_list = [DC.string_to_bytes "acme"; DC.string_to_bytes "cert"; cert_path_nonce] in
      init_seq_with_list_equivalence_of_list_and_sequence #DC.bytes cert_path_list
#pop-options

/// Helper Functions
/// ------------------
/// The following functions are mainly for retrieving certain objects from the server state.

val retrieve_public_account_key_from_server_st:
      (trace_index:nat) ->
      (server:principal) ->
      (key_id:url) ->
      LA.DYL (option (pubk:DC.bytes{LC.is_publishable_p app_preds trace_index pubk }))
         (requires (fun h0 -> trace_index == trace_len h0))
         (ensures (fun h0 r h1 -> h0 == h1))

(**
    Returns a private CA key from [current_app_state], together with the session index at which the
    key is stored.
*)
val retrieve_private_ca_key_from_server_st:
  (trace_index:nat) ->
  (server:principal) ->
  (current_version_vec:version_vec) ->
  (current_app_state:app_state trace_index server current_version_vec) ->
  Pure (option (nat * DC.bytes)) //(session index, private_ca_key)
       (requires Seq.length current_version_vec = Seq.length current_app_state)
       (ensures (fun r ->
         Some? r ==> (
         //the returned key is stored at the returned session index
         let si = fst (Some?.v r) in
         let key = snd (Some?.v r) in
         (state_inv trace_index server current_version_vec current_app_state ==> LC.is_sign_key_p app_preds trace_index key (readable_by (readers [any server])) (acme_sig_key_usage (readers [any server]) app_preds))  /\
         Seq.length current_app_state > si /\
         (match parse_acme_server_state (current_app_state.[si]) with
         | Success (PrivateCAKey private_ca_key) -> key == private_ca_key
         | _ -> False
       ))))

(**
 Verifies the signature of a JWS. For verification, this function retrieves the public key of the account indicated in the JWS.

 Returns the result of the verification and the public key used to verify if verification is successful.
*)
val verify_jws_acme_request_signature:
      (trace_index:nat) ->
      (server:principal) ->
      (jws_acme_request_object:jws_acme_request{
        LC.is_publishable_p app_preds trace_index (serialize_jws_acme_request jws_acme_request_object)
      }) ->
      LA.DYL (r:bool & (pubk:(option (LC.msg_p app_preds trace_index public)){
        let jws_msg = generate_message_for_jws_signature jws_acme_request_object.key_id jws_acme_request_object.url jws_acme_request_object.replay_nonce jws_acme_request_object.payload in
        if r then (
          (Some? pubk) /\
          (forall ps.
             LC.is_verify_key_p app_preds trace_index (Some?.v pubk) (readable_by ps) (acme_sig_key_usage ps app_preds) ==>
               (LC.contains_corrupt_principal (corrupt_at trace_index) ps \/
               acme_sign_pred ps app_preds trace_index jws_msg)
          )
        ) else (
          None? pubk
        )
      }))
      (requires (fun h0 -> trace_index = trace_len h0))
      (ensures (fun h0 r h1 -> h0 == h1))

(**
 Verifies a JWS.

 Returns the result of the verification and the public key used to verify the signature if verification is successful.
*)
val verify_jws_acme_request:
      (trace_index:nat) ->
      (request:http_request) ->
      (server:principal) ->
      (jws_acme_request_object:jws_acme_request{
        LC.is_publishable_p app_preds trace_index (serialize_jws_acme_request jws_acme_request_object)
      }) ->
      LA.DYL (r:bool & (pubk:(option (LC.msg_p app_preds trace_index public)){
        let jws_msg = generate_message_for_jws_signature jws_acme_request_object.key_id jws_acme_request_object.url jws_acme_request_object.replay_nonce jws_acme_request_object.payload in
        if r then (
          (Some? pubk) /\
          (forall ps.
            LC.is_verify_key_p app_preds trace_index (Some?.v pubk) (readable_by ps) (acme_sig_key_usage ps app_preds) ==>
              (LC.contains_corrupt_principal (corrupt_at trace_index) ps \/
              acme_sign_pred ps app_preds trace_index jws_msg)
          )
        ) else (None? pubk)}))
      (requires (fun h0 -> trace_index = trace_len h0))
      (ensures (fun h0 r h1 -> h0 == h1))


val verify_acme_new_key_inner_jws:
      (trace_index:nat) ->
      (server:principal) ->
      (jws:acme_new_key_inner_jws{
        LC.is_publishable_p app_preds trace_index (serialize_acme_new_key_inner_jws jws)
      }) ->
      LA.DYL (r:bool & (pubk:(option (LC.msg_p app_preds trace_index public)){
        let jws_msg = generate_message_for_new_key_inner_jws_signature jws.alg jws.jwk jws.inner_url jws.inner_payload_account jws.inner_payload_old_key in
        if r then (
          (Some? pubk) /\
          (forall ps.
            LC.is_verify_key_p app_preds trace_index (Some?.v pubk) (readable_by ps) (acme_sig_key_usage ps app_preds) ==>
              (LC.contains_corrupt_principal (corrupt_at trace_index) ps \/
              acme_sign_pred ps app_preds trace_index jws_msg)
          )
        ) else (None? pubk)}))
      (requires (fun h0 -> trace_index = trace_len h0))
      (ensures (fun h0 r h1 -> h0 == h1))


#push-options "--max_ifuel 0 --max_fuel 0"
(**
    Search for an acme account with the given account_url in server's state and return the session index of that account if found.

*)
let rec retrieve_account_session_id_containing_account_url
  (trace_index:nat)
  (server:principal)
  (account_url:url)
  (session_index:nat)
  (current_version_vec:version_vec)
  (current_app_state:app_state trace_index server current_version_vec)
  : Pure (option nat)
       (requires Seq.length current_version_vec = Seq.length current_app_state)
       (ensures (fun r ->
         Some? r ==> (
           Seq.length current_app_state > session_index /\
           Seq.length current_app_state > (Some?.v r) /\
           Success? (parse_acme_server_state current_app_state.[(Some?.v r)]) /\
           UserAccount? (Success?.v (parse_acme_server_state current_app_state.[(Some?.v r)])) /\
           (
             let Success (UserAccount _ _ ua_account_url) = parse_acme_server_state current_app_state.[(Some?.v r)] in
             eq_url account_url ua_account_url
           )
       )))
       (decreases (Seq.length current_version_vec - session_index))
  =
      if Seq.length current_version_vec <= session_index then
        None
      else
        match parse_acme_server_state current_app_state.[session_index] with
        | Success (UserAccount _ _ ua_account_url) -> (
            if (eq_url account_url ua_account_url) then (
              let Success (UserAccount _ _ ua_account_url) = parse_acme_server_state current_app_state.[session_index] in
              assert(eq_url account_url ua_account_url);
              Some session_index
            ) else (
              retrieve_account_session_id_containing_account_url
                trace_index
                server
                account_url
                (session_index + 1)
                current_version_vec
                current_app_state
            )
          )
        | _ -> retrieve_account_session_id_containing_account_url
                trace_index
                server
                account_url
                (session_index + 1)
                current_version_vec
                current_app_state
#pop-options

(**
    Search for an acme account with the given account_url in server's state and return the account and its session index if found.
*)
val retrieve_account_session_containing_account_url_from_server_st
  (trace_index:nat)
  (server:principal)
  (account_url:url)
  : LA.DYL (option
      (ass:acme_server_state{
        valid_acme_server_st app_preds trace_index server ass /\ (
        match ass with
        | (UserAccount account acc_pub_key acc_url) -> eq_url account_url acc_url
        | _ -> False
      )}
      * nat))
  (requires (fun h0 -> trace_index = trace_len h0))
  (ensures (fun h0 _ h1 -> h0 == h1 ))



let rec check_if_all_acme_authorizations_are_valid_for_order
  (trace_index:nat)
  (#server:principal)
  (order_sessionid:nat)
  (current_session_id:nat)
  (current_version_vec:version_vec)
  (current_app_state:app_state trace_index server current_version_vec)
  : Tot (r:bool{
    r <==> (
      forall si. si >= current_session_id ==> (
        match parse_acme_server_state current_app_state.[si] with
        | Success st -> (
          match st with
          | Authorization authorization_url authorization order_sessionid' -> (
              order_sessionid = order_sessionid' ==> authorization.acme_authorization_status = Valid
            )
          | _ -> True
          )
        | _ -> True
        )
      )
    })
  (decreases ((Seq.length current_version_vec) - current_session_id))
  =
  if Seq.length current_version_vec <= current_session_id then
    true
  else (
    match parse_acme_server_state (current_app_state.[current_session_id]) with
    | Success st -> (
      match st with
      | Authorization authorization_url authorization order_sessionid' -> (
        if order_sessionid = order_sessionid' then (
          if authorization.acme_authorization_status = Valid then
            check_if_all_acme_authorizations_are_valid_for_order trace_index order_sessionid (current_session_id + 1) current_version_vec current_app_state
          else
            false
        ) else
          check_if_all_acme_authorizations_are_valid_for_order trace_index order_sessionid (current_session_id + 1) current_version_vec current_app_state
        )
        | _ -> check_if_all_acme_authorizations_are_valid_for_order trace_index order_sessionid (current_session_id + 1) current_version_vec current_app_state
      )
    | _ -> check_if_all_acme_authorizations_are_valid_for_order trace_index order_sessionid (current_session_id + 1) current_version_vec current_app_state
  )


let rec get_acme_challenge_processing_from_sequence
  (challenges:Seq.seq acme_challenge)
  (current_index:nat)
  : Tot
  (r:(option (
     idx:nat{idx < Seq.length challenges} &
     challenge:acme_challenge{((Seq.index challenges idx) == challenge) /\
                              challenge.acme_challenge_status = Processing})
     ){None? r ==> (forall i. i >= current_index ==> ((Seq.index challenges i).acme_challenge_status <> Processing))}
  )
  (decreases ((Seq.length challenges) - current_index))
  =
  if Seq.length challenges <= current_index then
    None
  else (
    let c = Seq.index challenges current_index in
    if c.acme_challenge_status = Processing then (
      Some (|current_index, c|)
    ) else get_acme_challenge_processing_from_sequence challenges (current_index + 1)
  )

let rec check_if_acme_challenge_processing_has_sent_out_verification_request
      (trace_index:nat)
      (server:principal)
      (authorization_sessionid:nat)
      (challenge_idx:nat)
      (current_session_id:nat)
      (current_version_vec:version_vec)
      (current_app_state:app_state trace_index server current_version_vec)
    : Tot bool
      (decreases ((Seq.length current_version_vec) - current_session_id))
    =
      if Seq.length current_version_vec <= current_session_id then
        false
      else
      ( match parse_acme_server_state (current_app_state.[current_session_id]) with
        | Success st ->
          ( match st with
            | ProcessingChallenge authorization_sessionid' challenge_idx' _ ->
              if authorization_sessionid = authorization_sessionid' && challenge_idx = challenge_idx' then
                true
              else
                check_if_acme_challenge_processing_has_sent_out_verification_request trace_index server authorization_sessionid challenge_idx (current_session_id + 1) current_version_vec current_app_state
            | _ -> check_if_acme_challenge_processing_has_sent_out_verification_request trace_index server authorization_sessionid challenge_idx (current_session_id + 1) current_version_vec current_app_state
          )
        | _ -> check_if_acme_challenge_processing_has_sent_out_verification_request trace_index server authorization_sessionid challenge_idx (current_session_id + 1) current_version_vec current_app_state
      )

#push-options "--max_ifuel 8 --max_fuel 8"
(** Search for an acme_authorization with the given authorization_url in server's
state and return it if found (together with the authz object's session index) *)
let rec retrieve_authz_by_authorization_url_from_server_st
  (trace_index:nat)
  (server:principal)
  (authorization_url:url)
  (session_index:nat)
  (current_version_vec:version_vec)
  (current_app_state:app_state trace_index server current_version_vec)
  : Pure (option (acme_authorization * nat))
       (requires True)
       (ensures (fun result ->
         match result with
         | None -> True
         | Some (authz, authz_sess) -> (
             // Returned indices are "small enough"
             authz_sess < Seq.length current_app_state /\
             // The authz_sess index really points to an Authorization session
             Success? (parse_acme_server_state current_app_state.[authz_sess]) /\
             Authorization? (Success?.v (parse_acme_server_state current_app_state.[authz_sess])) /\
             authz == Authorization?.authorization (Success?.v (parse_acme_server_state current_app_state.[authz_sess]))
           )
       ))
       (decreases (Seq.length current_version_vec - session_index))
  =
      if Seq.length current_version_vec <= session_index then
        None
      else
        match parse_acme_server_state current_app_state.[session_index] with
        | Success (Authorization authorization_url' authorization order_sess_idx) -> (
            if eq_url authorization_url' authorization_url then
              Some (authorization, session_index)
            else
              retrieve_authz_by_authorization_url_from_server_st trace_index server authorization_url (session_index + 1) current_version_vec current_app_state
          )
        | _ -> retrieve_authz_by_authorization_url_from_server_st trace_index server authorization_url (session_index + 1) current_version_vec current_app_state
#pop-options


let rec find_challenge_in_seq_by_url
    (haystack:Seq.seq acme_challenge)
    (needle:url)
    (current_index:nat)
  : Tot (r:option (acme_challenge * nat){Some? r ==> snd(Some?.v r) < Seq.length haystack})
    (decreases (Seq.length haystack - current_index))
  =
    if Seq.length haystack <= current_index then None else
    let current_element = haystack.[current_index] in
    if eq_url current_element.acme_challenge_url needle then (
      Some (current_element, current_index)
    ) else
      find_challenge_in_seq_by_url haystack needle (current_index + 1)


#push-options "--max_ifuel 8 --max_fuel 8"
(** Search for an acme_authorization containing a challenge with the given challenge_url in server's
state and return it if found (together with the authz object's session index and the challenge's
index in the authz object's challenge list) *)
let rec retrieve_authz_by_challenge_url_from_server_st
  (trace_index:nat)
  (server:principal)
  (challenge_url:url)
  (session_index:nat)
  (current_version_vec:version_vec)
  (current_app_state:app_state trace_index server current_version_vec)
  : Pure (option (acme_authorization * nat * nat))
       (requires True)
       (ensures (fun result ->
         match result with
         | None -> True
         | Some (authz, authz_sess, chall_idx) -> (
             // Returned indices are "small enough"
             chall_idx < Seq.length authz.acme_authorization_challenges /\
             authz_sess < Seq.length current_app_state /\
             // The authz_sess index really points to an Authorization session
             Success? (parse_acme_server_state current_app_state.[authz_sess]) /\
             Authorization? (Success?.v (parse_acme_server_state current_app_state.[authz_sess])) /\
             // The authz_sess index points to the authorization session that is returned
             (let Success (Authorization authorization_url azo order_sess_idx) = parse_acme_server_state current_app_state.[authz_sess] in
               authz == azo
             )
           )
       ))
       (decreases (Seq.length current_version_vec - session_index))
  =
      if Seq.length current_version_vec <= session_index then
        None
      else
        match parse_acme_server_state current_app_state.[session_index] with
        | Success (Authorization authorization_url authorization order_sess_idx) -> (
            // Look through the authorization's challenges
            match find_challenge_in_seq_by_url authorization.acme_authorization_challenges challenge_url 0 with
            | None -> retrieve_authz_by_challenge_url_from_server_st trace_index server challenge_url (session_index + 1) current_version_vec current_app_state
            | Some (challenge, challenge_idx) -> Some (authorization, session_index, challenge_idx)
          )
        | _ -> retrieve_authz_by_challenge_url_from_server_st trace_index server challenge_url (session_index + 1) current_version_vec current_app_state
#pop-options


(**
 this function updates the status of the identifer in seq_authz_info to Valid
*)
val set_valid_for_identifier_in_order:
   (trace_index:nat) ->
   order:acme_order ->
   seq_authz_info: Seq.seq authorization_info ->
   acc_pub_key:DC.bytes{
     is_valid_Order_session app_preds trace_index order seq_authz_info acc_pub_key
   } ->
   identifier:domain{
     Seq.mem identifier order.acme_order_identifiers  /\
     owner_of_domain_owns_public_key_or_corrupted app_preds trace_index identifier acc_pub_key
   } ->
   updated_seq_authz_info:Seq.seq authorization_info{
     is_valid_Order_session app_preds trace_index order updated_seq_authz_info acc_pub_key
   }

(**
this function checks if all status in seq_authz_info are valid, if yes, then it set the status of order to Ready
*)
val check_valid_and_set_ready_for_order:
   (trace_index:nat) ->
   order:acme_order{LC.is_publishable_p app_preds trace_index (serialize_acme_order order)} ->
   seq_authz_info: Seq.seq authorization_info ->
   acc_pub_key:DC.bytes{
     is_valid_Order_session app_preds trace_index order seq_authz_info acc_pub_key
   } ->
   updated_order:acme_order{
     LC.is_publishable_p app_preds trace_index (serialize_acme_order updated_order) /\
     is_valid_Order_session app_preds trace_index updated_order seq_authz_info acc_pub_key
   }

(**
this (FAULTY) function checks if ONE status in seq_authz_info are valid, if yes, then it set the status of order to Ready.
This replicates the bug in Let's Encrypt where the server only considers ONE domain in the order instead of ALL domain
*)
val check_valid_and_set_ready_for_order_faulty:
   (trace_index:nat) ->
   order:acme_order{LC.is_publishable_p app_preds trace_index (serialize_acme_order order)} ->
   seq_authz_info: Seq.seq authorization_info ->
   acc_pub_key:DC.bytes{
     is_valid_Order_session app_preds trace_index order seq_authz_info acc_pub_key
   } ->
   updated_order:acme_order{
     LC.is_publishable_p app_preds trace_index (serialize_acme_order updated_order) /\
     is_valid_Order_session app_preds trace_index updated_order seq_authz_info acc_pub_key
   }


(**
- generate a sequence of authorization_info for Order session
- all authz_info_status are Pending
*)
val generate_sequence_of_authorization_info_for_order:
   (trace_index:nat) ->
   order:acme_order{order.acme_order_status <> Some Ready} ->
   acc_pub_key:DC.bytes ->
   seq_authz_info: Seq.seq authorization_info{
     is_valid_Order_session app_preds trace_index order seq_authz_info acc_pub_key
   }
