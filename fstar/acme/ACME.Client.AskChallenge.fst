/// ACME.Client.AskChallenge (implementation)
/// ==========================================
module ACME.Client.AskChallenge

open Helpers
open DY.Monad
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.Labels
open DY.Entry
open Labeled.ApplicationAPI
open Labeled.Crypto
open Web.Messages
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open Application.Predicates
friend Application.Predicates
open FStar.Seq.Base

open SerializationHelpers
open SerializationLemmas
open FStar.String
open ACME.Data.Predicates
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open ACME.Client.HelperLemmas
open ACME.Client.HelperFunctions

let convert_type_app_state
 (tr_idx:nat)
 (p:principal)
 (v:version_vec)
 (s:principal_state{is_principal_state_readable tr_idx p v s})
 :s':app_state tr_idx p v{s'==s}
 =
 s


#set-options "--max_fuel 4 --initial_fuel 2 --max_ifuel 1 --z3rlimit 250"

val update_valid_ACMEOrder_session_state_preserves_state_inv:
  tr_idx: nat ->
  client:principal ->
  current_version_vec: version_vec ->
  current_state:app_state tr_idx client current_version_vec ->
  sess_idx:nat {sess_idx < Seq.length current_state /\ is_ACMEOrder_session current_state.[sess_idx]} ->
  acme_order_ss:acme_client_state{ACMEOrder? acme_order_ss /\ valid_acme_client_st current_state tr_idx app_preds client acme_order_ss} ->
  Lemma
  (requires state_inv tr_idx client current_version_vec current_state)
  (ensures (
    let updated_state = current_state.[sess_idx] <- (serialize_acme_client_state acme_order_ss) in
    state_inv tr_idx client current_version_vec updated_state /\
    is_principal_state_readable tr_idx client current_version_vec updated_state
  ))

let update_valid_ACMEOrder_session_state_preserves_state_inv tr_idx client v state idx_order acme_order_ss =
  let updated_state = state.[idx_order] <- (serialize_acme_client_state acme_order_ss) in
  valid_serialize_acme_client_st_lemma state tr_idx client idx_order acme_order_ss;
  parse_acme_client_state_lemma acme_order_ss;
  parse_acme_server_st_of_client_st_returns_none acme_order_ss;
  assert(state_inv tr_idx client v updated_state);
  state_inv_implies_principal_state_readable tr_idx client v updated_state


let _acme_client_receive_order_response_save_state client order idx_order opt_current_order_url =
  let (|i, v, state|) = get_last_state client in
    if idx_order < Seq.length state then (
      let ss_order_st = state.[idx_order] in
      match parse_acme_client_state ss_order_st with
      | Success (ACMEOrder old_order acc_idx _) -> (
         if is_init_and_updated_order old_order order then(
            let acme_order_ss = ACMEOrder order acc_idx opt_current_order_url in
            let ss_new_order = (serialize_acme_client_state acme_order_ss) in
            let st_new_order = state.[idx_order] <- ss_new_order in
            let len_now = current_trace_len () in
            //assert(valid_acme_client_st st_new_order len_now app_preds client acme_order_ss);
            update_valid_ACMEOrder_session_state_preserves_state_inv len_now client v state idx_order acme_order_ss;
            set_state client v st_new_order;
            let num_of_authz_urls = Seq.length (Some?.v (order.acme_order_authorizations)) in
            (idx_order, num_of_authz_urls)
         )else error "fail to save state"
       )
      | _ -> error "fail to save state"
    ) else error "fail to save state"


val _acme_client_asks_for_authorization_save_state_helper:
  client: principal ->
  order_sessionid:nat ->
  authz_url_idx:nat ->
  DYL (
          idx_order: nat *
          request_nonce: bytes *
          request_body:bytes *
          authz_dom: domain *
          req_uri: request_uri *
          replay_nonce:bytes
      )
  (requires fun h0 -> True)
  (ensures fun h0 (idx_order, request_nonce, request_body, authz_dom, req_uri, _) h1 ->
     later (trace_len h0) (trace_len h1) /\
     is_publishable_p app_preds (trace_len h1) request_nonce /\
     is_publishable_p app_preds (trace_len h1) request_body /\
     is_publishable_p app_preds (trace_len h1) (serialize_request_uri req_uri)
  )

#push-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 400"
let _acme_client_asks_for_authorization_save_state_helper client idx_order authz_url_idx =
  let (|idx, request_nonce|) = guid_gen () in
  assert(is_publishable_p app_preds idx request_nonce); 
  let (|len_now, v, state|) =  get_last_state client in
    assert(later idx len_now);
    if idx_order < Seq.length state then (
      match parse_acme_client_state state.[idx_order] with
      | Success (ACMEOrder order idx_acc _) -> (
          if idx_acc < Seq.length state &&
             is_updated_order order &&
             authz_url_idx < Seq.length (Some?.v order.acme_order_authorizations)
          then (
            match parse_acme_client_state state.[idx_acc] with
            | Success (Account acc_priv_key acc_url order_url) -> ( 
                let authz_url =   get_authorization_url_i_from_order order authz_url_idx in
                assert(is_authorization_url_of_acme_order order authz_url);
                authorization_url_of_publishable_acme_order_is_publishable len_now order authz_url;
                let authz_dom = authz_url.url_domain in
                match client_finds_valid_replay_nonce len_now client v state authz_dom with
                |Success replay_nonce -> (
                let server = domain_principal_mapping authz_dom in
                let payload =  string_to_bytes app_preds len_now "" in
                assert(is_sign_key_p app_preds len_now acc_priv_key (readable_by (readers [any client])) (acme_sig_key_usage (readers [any client]) app_preds));

                generate_message_for_jws_signature_structure app_preds acc_url authz_url replay_nonce payload;

                assert(
                  match DY.Crypto.split (generate_message_for_jws_signature acc_url authz_url replay_nonce payload) with
                  | Success (nonce_bytes, snd_part) -> (
                    match  DY.Crypto.split snd_part with
                  | Success (keyID_bytes, snd_part) -> (
                    match DY.Crypto.split snd_part with
                    | Success (url_bytes, payload_bytes) -> (
                      match parse_acme_csr payload_bytes with
                      | Success csr ->  False
                      | _ -> True //other signing cases
                      )
                    | _ -> True
                    )
                  | _ -> True
                  )
                  | _ -> True
                );

                assert(acme_sign_pred  (readers [any client]) app_preds len_now (generate_message_for_jws_signature acc_url authz_url replay_nonce payload));

                let jws_req = generate_jws_acme_request app_preds len_now (acme_sig_key_usage (readers [any client]) app_preds) acc_url authz_url replay_nonce payload acc_priv_key (readable_by (readers [any client])) in 
                assert(is_publishable_p app_preds len_now payload); 
                elements_of_jws_acme_request_are_publishable_implies_jws_request_is_publishable app_preds len_now acc_url authz_url replay_nonce payload acc_priv_key (readers [any client]) ;
                let req_body = serialize_jws_acme_request jws_req in
                assert(is_publishable_p app_preds len_now req_body); 
                // url_is_publishable_implies_request_uri_is_publishable app_preds len_now authz_url;
                assert(is_publishable_p app_preds len_now (serialize_request_uri authz_url.url_request_uri));
                
                (idx_order, request_nonce, req_body, authz_dom,  authz_url.url_request_uri, replay_nonce)
                )
                | _ -> error "there is no replay nonce to send request"
               )
            | _ -> error "fail to send request asking for challenge"
          )else error "fail to send request asking for challenge"
        )
      | _ -> error "fail to send request asking for challenge"
    )else error "fail to send request asking for challenge"

#pop-options


#push-options "--max_fuel 6 --max_ifuel 4 --z3rlimit 400"

let _acme_client_asks_for_authorization_save_state client idx_order authz_url_idx =
  let (idx_order, request_nonce, req_body, authz_dom,  req_uri, replay_nonce) = _acme_client_asks_for_authorization_save_state_helper client idx_order authz_url_idx in
  let (|len_now, v, state|) =  get_last_state client in
  let server = domain_principal_mapping authz_dom in
  let req_header = generate_request_header_host_domain authz_dom in
  request_header_host_domain_is_publishable len_now authz_dom;
  assert(is_publishable_p app_preds len_now  (serialize_sequence_of_bytes_tuples req_header ) );
  (*       save the new state session HTTPSPendingRequest   *)
  let pen_req_ss = HTTPSPendingRequest request_nonce idx_order authz_dom in //the reference points to the session ACMEOrder added above
  let v_req_ss = Seq.snoc v 0 in
  let st_pen_req = Seq.snoc state (serialize_acme_client_state pen_req_ss) in             
  assert(can_label_of_bytes_flow_to app_preds len_now request_nonce public ); 
  flows_to_public_can_flow (app_preds.model.corrupt_at len_now) (get_label request_nonce) (readable_by (readers [any client]));
  assert(valid_acme_client_st state len_now app_preds client pen_req_ss); 
  assert(state_inv len_now client v state);
  add_valid_client_session_state_preserves_state_inv len_now client v state pen_req_ss; 
  let st' = convert_type_app_state len_now client v_req_ss st_pen_req in
  set_state client v_req_ss st'; 
  let len_now1 = current_trace_len () in               
  let http_req:http_request = {
      req_id = request_nonce;
      req_method = HTTP_METHOD_POST;
      req_uri = req_uri;
      req_headers = req_header;
      req_body = req_body
  } in
  assert(later len_now len_now1);
  assert(can_label_of_bytes_flow_to app_preds len_now1 (serialize_request_uri req_uri) public);
  assert(can_label_of_bytes_flow_to app_preds len_now1 request_nonce public);
  assert(can_label_of_bytes_flow_to app_preds len_now1 (serialize_sequence_of_bytes_tuples req_header ) public);
  assert(can_label_of_bytes_flow_to app_preds len_now1 req_body public);
  assert(all_elements_of_http_request_are_publishable app_preds len_now1 http_req);
  ( http_req, server, replay_nonce)


#pop-options


