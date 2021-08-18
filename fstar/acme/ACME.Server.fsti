/// ACME.Server
/// ================
module ACME.Server

open DY.Entry
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Monad
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open Application.Predicates
open HelperFunctions
open ACME.Data.Predicates
open ACME.Data
open SerializationHelpers

(*** Web Server Endpoints ***)

(**
  RFC8555 7.4 Applying for Certificate Issuance
  
  The issuance process starts here. The client sends a POST request containing an ACME order.
  Upon receiving this request, the server sends an ACME order containing an updated status, the same identifiers,
  and URLs for the authorization and finalize endpoints.
*)
val acme_server_new_order:
  acme_server_principal:principal ->
                       // the host header value is a domain of [acme_server_principal]
  request:http_request{http_request_header_contains_domain_of_server request acme_server_principal} ->
  DYL http_response
  (requires (fun t0 ->
    is_publishable_p app_preds (trace_len t0) (serialize_http_request request)
  ))
  (ensures (fun t0 resp t1 ->
    resp.resp_status == HTTP_STATUS_201_CREATED /\
    acme_order_in_http_response_is_publishable app_preds (trace_len t1) resp /\
    is_publishable_p app_preds (trace_len t1) (serialize_http_response resp)
  ))

(**
  Wrapper function for [acme_server_new_order] handling communication over the network.
*)
val acme_server_new_order_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http request
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))

(**
 RFC8555 7.5 Identifier Authorization: returns acme_authorization
 
*)
val acme_server_identifier_authz:
  acme_server_principal:principal ->
  request:http_request ->
  DYL http_response
  (requires (fun t0 -> is_publishable_p app_preds (trace_len t0) (serialize_http_request request)))
  (ensures (fun t0 response t1 ->
    t0 == t1 /\
    acme_authorization_in_http_response_is_publishable app_preds (trace_len t1) response /\
    is_publishable_p app_preds (trace_len t1) (serialize_http_response response)
  ))


(**
  Wrapper function for [acme_server_identifier_authz] handling communication over the network.
*)
val acme_server_identifier_authz_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http request
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))

(**
 RFC8555 7.5.1 Responding to Challenges (trigger challenge validation)
*)
val acme_server_challenge_response:
  acme_server_principal:principal ->
  request:http_request ->
  DYL http_response
  (requires (fun t0 -> is_publishable_p app_preds (trace_len t0) (serialize_http_request request)))
  (ensures (fun t0 resp t1 ->
    is_publishable_p app_preds (trace_len t1) (serialize_http_response resp)
  ))


(**
  Wrapper function for [acme_server_challenge_response] handling communication over the network.
*)
val acme_server_challenge_response_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http request
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))


(**
RFC8555 8.3. HTTP Challenge

The server send an HTTP request to the HTTP server for the domain (identifier)
*)
val acme_server_trigger_challenge_verification:
  server:principal ->
  DYL http_request
  (requires (fun t0 -> True))
  (ensures (fun t0 req t1 -> is_publishable_p app_preds (trace_len t1) (serialize_http_request req)))

(**
  Wrapper function for [acme_server_trigger_challenge_verification] handling communication over the
  network.
*)
val acme_server_trigger_challenge_verification_nw:
  acme_server_principal:principal ->
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))

(**
 RFC8555 8.3. HTTP Challenge: receive and validate the challenge verification

The server receives the challenge verification via an HTTP response from the HTTP server 
for the domain owned by the client. The response is assumed to be sent over an authenticated channel 
to exclude the trivial attack in which the attacker can make up the response to prove the ownership for any domain.

*)
val acme_server_receive_challenge_verification:
  server:principal ->
  response:http_response ->
  sender_of_response:principal ->
  index_of_send_event:nat{
    authenticated_send_pred index_of_send_event sender_of_response server (serialize_http_response response) \/
    is_principal_corrupted_before index_of_send_event sender_of_response
  } ->
  DYL unit
  (requires (fun t0 ->
    index_of_send_event < trace_len t0 /\
    is_publishable_p app_preds (trace_len t0) (serialize_http_response response) /\
    is_publishable_p app_preds index_of_send_event (serialize_http_response response)
  ))
  (ensures (fun t0 _ t1 -> True))


(**
  Wrapper function for [acme_server_receive_challenge_verification] handling communication over the
  network.
*)
val acme_server_receive_challenge_verification_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http response
  DYL unit
  (requires (fun t0 -> True))
  (ensures (fun t0 _ t1 -> True))

(**
 RFC8555 7.4. Applying for Certificate Issuance: finalize an order
*)
val acme_server_finalize_order:
  acme_server_principal:principal ->
  request:http_request ->
  DYL http_response
  (requires (fun t0 -> is_publishable_p app_preds (trace_len t0) (serialize_http_request request)))
  (ensures (fun t0 response t1 -> is_publishable_p app_preds (trace_len t1) (serialize_http_response response)))


(**
  Wrapper function for [acme_server_finalize_order] handling communication over the network.
*)
val acme_server_finalize_order_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http request
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))




(**
 RFC8555 7.4.2 Downloading the Certificate

 Note: certificates are addressed by their "certificate URL"
*)
val acme_server_retrieve_cert:
  acme_server_principal:principal ->
  request:http_request ->
  DYL http_response
  (requires (fun t0 -> is_publishable_p app_preds (trace_len t0) (serialize_http_request request)))
  (ensures (fun t0 response t1 ->
    certificate_of_http_response_is_publishable app_preds (trace_len t0) response /\
    is_publishable_p app_preds (trace_len t0) (serialize_http_response response) /\
    trace_len t1 >= trace_len t0
  ))


(**
  Wrapper function for [acme_server_retrieve_cert] handling communication over the network.
*)
val acme_server_retrieve_cert_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http request
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))


(**
  Buggy function that could lead to attacks
  Wrapper function for [acme_server_receive_challenge_verification] handling communication over the
  network.
  FAULTY version: acme server only checks the authorization status for one domain instead of ALL domains in the order
*)
val acme_server_receive_challenge_verification_nw_faulty:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http response
  DYL unit
  (requires (fun t0 -> True))
  (ensures (fun t0 _ t1 -> True))

(** 
RFC8555 7.2 Getting a Nonce

The server issues a replay nonce for the client 
*)
val acme_server_new_nonce: 
  acme_server_principal:principal -> 
  request:http_request{request.req_method == HTTP_METHOD_HEAD /\ eq_path request.req_uri.uri_path (init_seq_bytes_with_list [string_to_bytes "acme"; string_to_bytes "new-nonce"])} -> 
  DYL (response:http_response{response.resp_status == HTTP_STATUS_200_OK})
  (requires (fun t0 -> is_publishable_p app_preds (trace_len t0) (serialize_http_request request)))
  (ensures (fun t0 resp t1 -> is_publishable_p app_preds (trace_len t1) (serialize_http_response resp)))

(**
  Wrapper function for [acme_server_new_nonce] handling communication over the network.
*)
val acme_server_new_nonce_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http request
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))

(**
RFC8555 7.3.5. Account Key Rollover 
*)
val acme_server_update_account_key:
    acme_server_principal:principal ->
    request:http_request ->
  DYL (http_response)
    (requires (fun h0 ->
      http_request_header_contains_domain_of_server request acme_server_principal /\
      is_publishable_p app_preds (trace_len h0) (serialize_http_request request)
    ))
    (ensures (fun h0 response h1 ->
      response.resp_status == HTTP_STATUS_200_OK /\
      is_publishable_p app_preds (trace_len h1) (serialize_http_response response)
    ))

(**
  Wrapper function for [acme_server_update_account_key] handling communication over the network.
*)
val acme_server_update_account_key_nw:
  acme_server_principal:principal ->
  msg_idx:nat -> //index of the http request
  DYL nat
  (requires (fun t0 -> True))
  (ensures (fun t0 result t1 -> True))
