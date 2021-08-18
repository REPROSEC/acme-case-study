/// ACME.Client.HelperFunctions (implementation)
/// =============================================
module ACME.Client.HelperFunctions

open Helpers
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.Monad
open DY.Labels
open Labeled.ApplicationAPI
open Labeled.Crypto
open Web.Messages
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open Application.Predicates
open FStar.Seq.Base
friend Application.Predicates
open SerializationHelpers
open FStar.String
open ACME.Data.Predicates
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open ACME.Client.HelperLemmas
module DC = DY.Crypto

#set-options "--max_fuel 2 --max_ifuel 0 --z3rlimit 50"

val find_pending_request_for_response_iterate:
  http_resp: http_response ->
  current_state: principal_state ->
  idx:nat ->
  Tot (result (sess_st:acme_client_state{HTTPSPendingRequest? sess_st}))
  (decreases (Seq.length current_state - idx))


let rec find_pending_request_for_response_iterate http_resp current_state idx =
  if idx >= Seq.length current_state then Error "no pending request" else(
    let sess_idx = current_state.[idx] in
    match parse_acme_client_state sess_idx with
    |Success (HTTPSPendingRequest req_nonce  ref_sessid serv_dom) ->
       if eq_bytes req_nonce http_resp.resp_req_id then
         Success (HTTPSPendingRequest req_nonce ref_sessid serv_dom)
       else
         find_pending_request_for_response_iterate http_resp current_state (idx+1)
    |_ -> find_pending_request_for_response_iterate http_resp current_state (idx+1)
  )

let find_pending_request_for_response http_resp current_state =
  find_pending_request_for_response_iterate http_resp current_state 0


let find_server_domain_of_pending_request_for_response http_resp  current_state =
  match find_pending_request_for_response http_resp current_state with
  |Success (HTTPSPendingRequest _ _ serv_dom) -> Success serv_dom
  |_ -> Error "no server domain for response"

let find_reference_sessionid_of_pending_request_for_response  http_resp  current_state =
  match find_pending_request_for_response http_resp current_state with
  |Success (HTTPSPendingRequest req_nonce ref_sessid _) -> Success ref_sessid
  |_ -> Error "no reference session id of pending request"


val find_ACMEAuthorization_session_state_by_domain_and_token_iterate:
  current_state: principal_state ->
  doms:domain ->
  token:bytes ->
  idx:nat ->
  Tot (result (authz_sess_idx:nat * authz_sess:acme_client_state))
  (decreases (Seq.length current_state - idx))

let rec find_ACMEAuthorization_session_state_by_domain_and_token_iterate current_state dom token idx =
   if idx >= Seq.length current_state then Error "no ACMEAuthorziation session" else(
    let sess_idx = current_state.[idx] in
    match parse_acme_client_state sess_idx with
    |Success (ACMEAuthorziation authorization order_sessionid) ->
       if dom = authorization.acme_authorization_identifier &&
          is_token_of_acme_authorization token authorization
       then(
         Success (idx, ACMEAuthorziation authorization order_sessionid)
       )else
         find_ACMEAuthorization_session_state_by_domain_and_token_iterate current_state dom token (idx+1)
    |_ -> find_ACMEAuthorization_session_state_by_domain_and_token_iterate current_state dom token (idx+1)
  )

let find_ACMEAuthorization_session_state_by_domain_and_token current_state dom token =
 find_ACMEAuthorization_session_state_by_domain_and_token_iterate current_state dom token 0

let find_ACMEOrder_and_Account_session_index_from_CSR_session_index current_state csr_idx =
 if csr_idx < Seq.length current_state then (
      match parse_acme_client_state (current_state.[csr_idx]) with
      |Success (CSR _ identifiers order_idx _) -> (
              if order_idx < Seq.length current_state then(
                match parse_acme_client_state (current_state.[order_idx]) with
                |Success (ACMEOrder _ account_idx _) -> Success (order_idx, account_idx)
                |_ -> Error "no ACMEOrder and Account session for CSR"
              )else Error "no ACMEOrder and Account session for CSR"

       )
      |_ -> Error "no ACMEOrder and Account session for CSR"
  )else Error "no ACMEOrder and Account session for CSR"





//#push-options "--z3refresh"
//#push-options "--max_ifuel 16 --max_fuel 8 --z3rlimit 100"
let gen_http_request_with_server_domain_in_header tr_idx server req_nonce serv_dom request_uri request_body =
  let req_header = Seq.create 1 (DY.Crypto.string_to_bytes "Host", (serialize_domain serv_dom)) in
  let http_req:http_request = {
              req_id = req_nonce;
              req_method = HTTP_METHOD_POST;
              req_uri = request_uri;
              req_headers = req_header;
              req_body = request_body
  }in http_req


let gen_http_request_with_server_domain_in_header_lemma tr_idx server req_nonce serv_dom request_uri request_body =
  let req = gen_http_request_with_server_domain_in_header tr_idx server req_nonce serv_dom request_uri request_body in
  get_header_from_headers_singleton "Host" (serialize_domain serv_dom);
  assert( http_request_header_contains_domain_of_server req server);
  assert(req.req_headers ==  generate_request_header_host_domain serv_dom);
  request_header_host_domain_is_publishable tr_idx serv_dom






let receive_http_response client msg_idx =
  let (|tr_idx, _, msg|) = receive_i msg_idx client in
    (
     match parse_http_response msg with
      |Success resp ->
        serialize_parse_http_response_publishablity_lemma app_preds tr_idx msg;
        resp
      | _ -> error "fail to receive http response"
    )

let receive_http_request client msg_idx =
  let (|tr_idx, p, msg|) = receive_i msg_idx client in
    (match parse_http_request msg with
      |Success req ->
        serialize_parse_http_request_publishablity_lemma app_preds tr_idx msg;
        (req, p)
      | _ -> error "fail to receive http request"
    )


#push-options "--max_ifuel 2"
let get_authorization_url_i_from_order order i =
   let authz_urls = Some?.v (order.acme_order_authorizations) in
   let authz_url =  authz_urls.[i] in
   FStar.Seq.contains_intro authz_urls i authz_url;
   authz_url
#pop-options

let get_challenge_i_from_authorization authz i =
  let challenge = authz.acme_authorization_challenges.[i] in
  FStar.Seq.contains_intro authz.acme_authorization_challenges i challenge;
  challenge


let get_challenge_i_from_authorization_lemma authz i = ()


let is_replay_nonce_in_http_response_headers (replay_nonce:bytes) (headers:Seq.seq http_header) =
  exists (i:nat). i < Seq.length headers /\ eq_bytes (snd (headers.[i])) replay_nonce /\  
  DC.bytes_to_string (fst (headers.[i])) == Success "Replay-Nonce"


let is_replay_nonce_in_http_response replay_nonce resp =
  is_replay_nonce_in_http_response_headers replay_nonce resp.resp_headers



let rec find_replay_nonce_in_http_response_headers (headers:Seq.seq http_header) (idx:nat): Tot (result (nonce:bytes {is_replay_nonce_in_http_response_headers nonce headers})) 
 (decreases (Seq.length headers - idx)) =
 if idx >= Seq.length headers then Error "cannot find replay nonce" else(
   let (name_bytes, value_bytes) = headers.[idx] in
   match DC.bytes_to_string name_bytes with
   |Success "Replay-Nonce" -> Success value_bytes
   |_ -> find_replay_nonce_in_http_response_headers headers (idx+1)
 )


let find_replay_nonce_in_http_response resp =
   find_replay_nonce_in_http_response_headers resp.resp_headers 0


let http_response_is_publishable_implies_replay_nonce_in_headers_is_publishable tr_idx nonce resp = 
 http_response_is_publishable_implies_headers_are_publishable app_preds tr_idx resp
 

(**
  Returns true iff the sequence of http headers contains a Location header with the value
  [location_bytes].
*)
let is_location_header_in_http_response_headers (location_bytes:bytes) (headers:Seq.seq http_header) =
  exists (i:nat). i < Seq.length headers /\ eq_bytes (snd (headers.[i])) location_bytes /\
  DC.bytes_to_string (fst (headers.[i])) == Success "Location"


let is_location_header_in_http_response (location_bytes:bytes) resp =
  is_location_header_in_http_response_headers location_bytes resp.resp_headers


let rec find_location_header_in_http_response_headers
    (headers:Seq.seq http_header)
    (idx:nat)
  : Tot (result (location_bytes:bytes {is_location_header_in_http_response_headers location_bytes headers}))
    (decreases (Seq.length headers - idx))
  =
    if idx >= Seq.length headers then Error "cannot find Location header"
    else (
      let (name_bytes, value_bytes) = headers.[idx] in
      match DC.bytes_to_string name_bytes with
      |Success "Location" -> Success value_bytes
      |_ -> find_location_header_in_http_response_headers headers (idx+1)
    )


let find_location_header_in_http_response resp =
  find_location_header_in_http_response_headers resp.resp_headers 0


let find_location_header_url_in_http_response_option tr_idx resp =
  match find_location_header_in_http_response resp with
  | Success location_value -> (
    match parse_url location_value with
    | Success location_header_url ->(
      http_response_is_publishable_implies_headers_are_publishable app_preds tr_idx resp;
      serialize_parse_url_publishablity_lemma app_preds tr_idx location_value;
      Some location_header_url
    )
    | _ -> None
  )
  | _ -> None


let http_response_is_publishable_implies_location_in_headers_is_publishable tr_idx location_bytes resp =
  http_response_is_publishable_implies_headers_are_publishable app_preds tr_idx resp


let rec find_valid_replay_nonce_session_for_domain_iterate (state:principal_state) (server_dom:domain) (idx:nat): 
Tot (result (sessionid:nat{
    sessionid < Seq.length state /\
    (
      match parse_acme_client_state (state.[sessionid]) with
      |Success (ReplayNonce nonce valid dom) ->
        dom = server_dom /\
        valid
      |_ -> False
    )
  }))
(decreases (Seq.length state - idx))
=
 if idx >= Seq.length state then Error "no valid replay nonce for the domain" else(
   match parse_acme_client_state (state.[idx]) with
   |Success (ReplayNonce nonce valid dom) ->
        if (dom = server_dom && valid) then
          Success idx
        else
          find_valid_replay_nonce_session_for_domain_iterate state server_dom (idx+1)
   |_ -> find_valid_replay_nonce_session_for_domain_iterate state server_dom (idx+1)
 )


let find_valid_replay_nonce_session_for_domain state server_dom =
  find_valid_replay_nonce_session_for_domain_iterate state server_dom 0


let rec find_valid_replay_nonce_session_iterate (state:principal_state) (nonce:bytes) (idx:nat): 
Tot (result (sessionid:nat{
    sessionid < Seq.length state /\
    (
      match parse_acme_client_state (state.[sessionid]) with
      |Success (ReplayNonce replay_nonce valid dom) ->
        eq_bytes nonce replay_nonce  /\
        valid
      |_ -> False
    )
  }))
(decreases (Seq.length state - idx))
=
 if idx >= Seq.length state then Error "no session for the replay nonce" else(
   match parse_acme_client_state (state.[idx]) with
   |Success (ReplayNonce replay_nonce valid dom) ->
        if (eq_bytes nonce replay_nonce && valid) then
          Success idx
        else
          find_valid_replay_nonce_session_iterate state nonce (idx+1)
   |_ -> find_valid_replay_nonce_session_iterate state nonce (idx+1)
 )

let find_valid_replay_nonce_session state nonce =
  find_valid_replay_nonce_session_iterate state nonce 0
  

let client_finds_valid_replay_nonce tr_idx client current_version_vec state server_dom =
  match find_valid_replay_nonce_session_for_domain state server_dom with
  | Success (nonce_idx) -> 
     let Success (ReplayNonce nonce valid dom) = parse_acme_client_state (state.[nonce_idx]) in
     Success nonce
  | _ -> Error "cannot find valid replay nonce for the domain"


val client_sets_replay_nonce_invalid_iterate:
  client: principal ->
  tr_idx: nat ->
  v:version_vec ->
  state:principal_state{state_inv tr_idx client v state /\ is_principal_state_readable tr_idx client v state} ->
  replay_nonce:bytes ->
  idx:nat{idx<=Seq.length v} ->
  Pure (principal_state) (decreases (Seq.length v - idx))
  (requires True)
  (ensures fun (state_out) -> state_inv tr_idx client v state_out /\ is_principal_state_readable tr_idx client v state_out)
  

let rec client_sets_replay_nonce_invalid_iterate client tr_idx v state replay_nonce idx =
  if (idx >= Seq.length v) then (
    (state)
  )else(
    match  parse_acme_client_state (state.[idx]) with
    |Success (ReplayNonce nonce valid dom) ->(
      if(eq_bytes replay_nonce nonce) then (
        let invalid_nonce_ss = ReplayNonce nonce false dom in
        let ss_invalid_nonce = serialize_acme_client_state invalid_nonce_ss in
        let updated_state = state.[idx] <- ss_invalid_nonce in
        update_valid_ReplayNonce_session_state_preserves_state_inv tr_idx client v state idx invalid_nonce_ss;
        client_sets_replay_nonce_invalid_iterate client tr_idx v updated_state replay_nonce (idx+1)
      )else(
        client_sets_replay_nonce_invalid_iterate client tr_idx v state replay_nonce (idx+1)
      )
    )
    |_ -> client_sets_replay_nonce_invalid_iterate client tr_idx v state replay_nonce (idx+1)
  )


let client_deactivates_replay_nonce client replay_nonce =
  let (|i, v, state|) = get_last_state client in
  let updated_state = client_sets_replay_nonce_invalid_iterate client i v state replay_nonce 0 in
  set_state client v updated_state
