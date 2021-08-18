/// ACME.Client.HelperFunctions
/// =============================================
module ACME.Client.HelperFunctions

open Helpers
open DY.Monad
open DY.Entry
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.Labels
open Labeled.ApplicationAPI
open Labeled.Crypto
open Web.Messages
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open Application.Predicates
open FStar.Seq.Base
open SerializationHelpers
open FStar.String
open ACME.Data.Predicates
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open SerializationLemmas



val find_pending_request_for_response:
  http_resp: http_response ->
  current_state:principal_state ->
  Tot (result (sess_st:acme_client_state{HTTPSPendingRequest? sess_st}))

(*
returns the server domain stored in the corresponding pending request of the incomming response 
*)
val find_server_domain_of_pending_request_for_response:
   http_resp: http_response ->
  current_state:principal_state ->
  Tot (result domain)

val find_reference_sessionid_of_pending_request_for_response:
  http_resp: http_response ->
  current_state:principal_state ->
  result (reference_sessionid:nat)




val find_ACMEAuthorization_session_state_by_domain_and_token:
  current_state: principal_state ->
  doms:domain ->
  token:bytes ->
  Tot (result (authz_sess_idx:nat * authz_sess:acme_client_state))


val find_ACMEOrder_and_Account_session_index_from_CSR_session_index:
  current_state: principal_state ->
  csr_idx:nat ->
  Tot (result (
        acme_order_idx:nat {acme_order_idx < Seq.length current_state}*
        account_idx: nat
      )
  )



val gen_http_request_with_server_domain_in_header:
  tr_idx:nat ->
  server:principal ->
  request_nonce:bytes{is_publishable_p app_preds tr_idx request_nonce} ->
  serv_dom:domain{domain_principal_mapping serv_dom = server} ->
  request_uri:request_uri{is_publishable_p app_preds tr_idx (serialize_request_uri request_uri)} ->
  request_body: bytes{is_publishable_p app_preds tr_idx request_body} ->
  request:http_request{
     request.req_body == request_body /\
     request.req_id == request_nonce /\
     request.req_uri == request_uri
  }

val gen_http_request_with_server_domain_in_header_lemma:
  tr_idx:nat ->
  server:principal ->
  request_nonce:bytes{is_publishable_p app_preds tr_idx request_nonce} ->
  serv_dom:domain{domain_principal_mapping serv_dom = server} ->
  request_uri:request_uri{is_publishable_p app_preds tr_idx (serialize_request_uri request_uri)} ->
  request_body: bytes{is_publishable_p app_preds tr_idx request_body} ->
  Lemma
  (ensures
   (let req = gen_http_request_with_server_domain_in_header tr_idx server request_nonce serv_dom request_uri request_body in
    http_request_header_contains_domain_of_server req server /\
    all_elements_of_http_request_are_publishable app_preds tr_idx req
   )
  )
  [SMTPat (gen_http_request_with_server_domain_in_header tr_idx server request_nonce serv_dom request_uri request_body)]

val receive_http_response:
  receiver:principal ->
  msg_idx:nat ->
  DYL  (resp:http_response)
  (requires fun h -> True)
  (ensures fun h0 resp h1 -> h0 == h1 /\ is_publishable_p app_preds (trace_len h1) (serialize_http_response resp) )


val receive_http_request:
  receiver:principal ->
  msg_idx:nat ->
  DYL ( req:http_request * sender:principal)
  (requires fun h -> True)
  (ensures fun h0 (req, _) h1 -> h0 == h1 /\ is_publishable_p app_preds (trace_len h1) (serialize_http_request req) )


val get_authorization_url_i_from_order:
  order:acme_order{ Some?  order.acme_order_authorizations /\
                    Seq.length (Some?.v order.acme_order_authorizations) > 0
  } ->
  i:nat{i < Seq.length (Some?.v order.acme_order_authorizations)} ->
  authz_url:url{is_authorization_url_of_acme_order order authz_url}


val get_challenge_i_from_authorization:
  authz:acme_authorization ->
  i:nat{i< Seq.length authz.acme_authorization_challenges} ->
  challenge:acme_challenge{is_challenge_of_acme_authorization authz challenge}

val get_challenge_i_from_authorization_lemma:
  authz:acme_authorization ->
  i:nat{i< Seq.length authz.acme_authorization_challenges} ->
  Lemma
  (ensures
    get_challenge_i_from_authorization authz i  == (authz.acme_authorization_challenges).[i]
  )

val is_replay_nonce_in_http_response:
  replay_nonce:bytes ->
  resp:http_response ->
  Type0


val find_replay_nonce_in_http_response:
  resp:http_response ->
  result (replay_nonce:bytes{
    is_replay_nonce_in_http_response replay_nonce resp
  })


val http_response_is_publishable_implies_replay_nonce_in_headers_is_publishable:
  tr_idx:nat ->
  replay_nonce:bytes ->
  resp:http_response ->
  Lemma
  (requires 
    is_publishable_p app_preds tr_idx (serialize_http_response resp) /\
    is_replay_nonce_in_http_response replay_nonce resp
  )
  (ensures is_publishable_p app_preds tr_idx replay_nonce)
  


(**
  Returns true iff the http response [resp] contains a Location header with the value
  [location_bytes].
*)
val is_location_header_in_http_response:
  location_bytes:bytes ->
  resp:http_response ->
  Type0


(**
  Returns the value of the Location header contained in the http response [resp], if possible.
*)
val find_location_header_in_http_response:
  resp:http_response ->
  result (location_bytes:bytes{is_location_header_in_http_response location_bytes resp})


(**
  Returns the url of the Location header contained in the http response [resp], if possible.

  Similar [find_location_header_in_http_response], but returns an optional value of the (parsed)
  url.
*)
val find_location_header_url_in_http_response_option:
  tr_idx:nat ->
  resp:http_response{is_publishable_p app_preds tr_idx (serialize_http_response resp)} ->
  location_bytes:option url{
      is_publishable_p app_preds tr_idx (serialize_opt_url location_bytes)
  }



(**
  Lemma stating that the value of a Location header of a http response is publishable if the
  (serialized) http response is publishable.
*)
val http_response_is_publishable_implies_location_in_headers_is_publishable:
  tr_idx:nat ->
  location_bytes:bytes ->
  resp:http_response ->
  Lemma
  (requires
    is_publishable_p app_preds tr_idx (serialize_http_response resp) /\
    is_location_header_in_http_response location_bytes resp
  )
  (ensures is_publishable_p app_preds tr_idx location_bytes)


(**
returns a session containing a valid replay nonce that can be used to send a request to the server domain
*)
val find_valid_replay_nonce_session_for_domain: 
  state: principal_state ->
  server_dom: domain ->
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

val find_valid_replay_nonce_session: 
  state: principal_state ->
  nonce: bytes ->
  Tot (result (sessionid:nat{
    sessionid < Seq.length state /\
    (
      match parse_acme_client_state (state.[sessionid]) with
      |Success (ReplayNonce replay_nonce valid dom) ->
        eq_bytes nonce replay_nonce /\
        valid
      |_ -> False
    )
  }))

val client_finds_valid_replay_nonce:
  tr_idx: nat ->
  client:principal -> 
  current_version_vec: version_vec ->
  state: principal_state{state_inv tr_idx client current_version_vec state} ->
  server_dom: domain ->
  Tot (result (replay_nonce:bytes{
   is_publishable_p app_preds tr_idx replay_nonce
  }))


val client_deactivates_replay_nonce:
  client: principal ->
  replay_nonce:bytes ->
  DYL unit
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> later (trace_len t0) (trace_len t1))


