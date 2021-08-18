/// ACME.Client
/// ================
module ACME.Client

open Helpers
open Web.Messages
open DY.Monad
open DY.Labels
open DY.Crypto
open DY.Trace
open DY.Principals
open Labeled.Crypto
open Labeled.ApplicationAPI
open ACME.Data
open Application.Predicates
open ACME.Data.Predicates
open SerializationHelpers
open SerializationLemmas
open Application.Predicates.Helpers

(** 
RFC8555 7.4 Applying for Certificate Issuance

the body of the http request is described at RFC8555 7.1.3 Oder Objects
- NOTE: account id IS account url
*)
val acme_client_orders_certificate_http:
  client: principal ->
  doms: Seq.seq domain{Seq.length doms > 0} ->
  idx_account: nat ->
  DYL (
       server: principal &
       req: http_request{
         http_request_header_contains_domain_of_server req server
       } &
       replay_nonce: bytes
     )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let (|server, req, replay_nonce|) = r in
    is_publishable_p app_preds (trace_len h1) (serialize_http_request req)
  )

(**
Wrapper function for [acme_client_orders_certificate_http] handling communication over the network
*)
val acme_client_orders_certificate_nw:
  client: principal ->
  doms: Seq.seq domain{Seq.length doms > 0} ->
  idx_account: nat ->
  DYL nat
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)


(**
RFC8555 7.4 Applying for Certificate Issuance
client receives the response for the order request and save the updated
acme order object into the state
*)
val acme_client_receive_order_response_http:
  client: principal ->
  http_resp: http_response ->
  DYL (order_sessionid:nat * number_of_authorization_urls:nat)
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_response http_resp))
  (ensures fun h0 r h1 -> True)

(**
Wrapper function for [acme_client_receive_order_response_http:] handling communication over the network
*)
val acme_client_receive_order_response_nw:
  client: principal ->
  msg_idx: nat ->
  DYL (order_sessionid:nat * number_of_authorization_urls:nat )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)


(**
RFC8555 7.5 Identifier Authorization

  client send post-as-get request to an authorization url to get authorization object
  - acme_order_sessionid: session id of ACMEOrder session containing the sequence of authorization urls for the identifiers (domains)
  - authz_url_idx: index of the authorization url in the sequence
*)
val acme_client_send_authorization_request_i_http:
  client: principal ->
  acme_order_sessionid: nat ->
  authz_url_idx: nat ->
  DYL ( http_request * principal * bytes ) //return the replay nonce used in the http request, so that the client can deactivate it
  (requires fun h0 -> True)
  (ensures fun h0 (req, _, _) h1 -> is_publishable_p app_preds (trace_len h1) (serialize_http_request req))

(**
Wrapper function for [acme_client_send_authorization_request_i_http] handling communication over the network
*)
val acme_client_send_authorization_request_i_nw:
  client: principal ->
  acme_order_sessionid: nat ->
  authz_url_idx: nat ->
  DYL nat
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)



(**
RFC8555 7.5 Identifier Authorization

The client receives the authorization resource from the server and saves the resource into its state
*)
val acme_client_receive_authorization_response_http:
  client: principal ->
  http_resp: http_response ->
 DYL (authz_sessionid:nat * number_of_challenges: nat)
  (requires fun h0 ->  is_publishable_p app_preds (trace_len h0) (serialize_http_response http_resp))
  (ensures fun h0 r h1 -> True)

(**
Wrapper function for [acme_client_receive_authorization_response_http] handling communication over the network
*)
val acme_client_receive_authorization_response_nw:
  client: principal ->
  msg_idx:nat ->
  DYL (authz_sessionid:nat * number_of_challenges: nat)
  (requires fun h0 ->True)
  (ensures fun h0 r h1 -> True)

(**
RFC8555 7.5.1 Responding to Challenges

The client indicates to the server that it is ready for the challenge validation
*)
val acme_client_triggers_challenge_i_http:
  client: principal ->
  authz_sessionid: nat ->
  challenge_idx: nat ->
 DYL ( http_request * principal * bytes) //return the replay nonce used in the http request, so that the client can deactivate it
  (requires fun h0 -> True)
  (ensures fun h0 (req, _, _) h1 -> is_publishable_p app_preds (trace_len h1) (serialize_http_request req))

(**
Wrapper function for [acme_client_triggers_challenge_i_http] handling communication over the network
*)
val acme_client_triggers_challenge_i_nw:
  client: principal ->
  authz_sessionid: nat ->
  challenge_idx: nat ->
  DYL nat
  (requires fun h0 ->True)
  (ensures fun h0 r h1 -> True)


(**
RFC8555 8.3. HTTP Challenge

The HTTP Server for the domain owned by the client sends an HTTP response for the 
challenge request sent by the ACME server
*)
val acme_client_challenge_response_http:
  client: principal ->
  http_req: http_request  ->
  DYL (resp:http_response * send_event_idx:nat)
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_request http_req))
  (ensures fun h0 (resp, send_ev_idx) h1 ->
    is_publishable_p app_preds (trace_len h1) (serialize_http_response resp) /\
    (
        match DY.Crypto.split resp.resp_body with
         | Success (token, account_pubkey) ->(
            client_has_account_public_key client account_pubkey send_ev_idx /\
            send_ev_idx <= trace_len h1
           )
         | _ -> False
    )
  )

(**
Wrapper function for [acme_client_challenge_response_http] handling communication over the network
*)
val acme_client_challenge_response_nw:
  client: principal ->
  msg_idx:nat ->
  DYL nat
  (requires fun h0 ->True)
  (ensures fun h0 r h1 -> True)

(**
 RFC8555 7.4. Applying for Certificate Issuance: send CSR to finalize an order
*)
val acme_client_sends_CSR_http:
  client: principal ->
  order_sessionid: nat ->
  DYL
  (
      req:http_request *
      server:principal *
      replay_nonce: bytes //replay nonce used in the http request
  )
  (requires fun h0 -> True)
  (ensures fun h0 (req, _, _) h1 -> is_publishable_p app_preds (trace_len h1) (serialize_http_request req)
  )

(**
Wrapper function for [acme_client_sends_CSR_http] handling communication over the network
*)
val acme_client_sends_CSR_nw:
  client: principal ->
  order_sessionid: nat ->
  DYL nat
  (requires fun h0 ->True)
  (ensures fun h0 r h1 -> True)



(**
 RFC8555 7.4.2 Downloading the Certificate
 
   This function expects an http response from the finalize endpoint or an http response from the
   order endpoint (where the client needs to poll until the server responds with an order that has
   the status [Valid]).

  It either creates an http request for the certificate endpoint (in this case, the [polling_flag]
  is false), or an http request for the order endpoint (contained in the headers of the http
  response; in this case, the [polling_flag] is true).
*)
val acme_client_retrieves_certificate_http:
 client:principal ->
 http_resp:http_response ->
 DYL ( http_request * principal * bytes * polling_flag:bool ) //return the replay nonce used in the http request, so that the client can deactivate it
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_response http_resp))
  (ensures fun h0 (req,_, _,_) h1 -> is_publishable_p app_preds (trace_len h1) (serialize_http_request req))

(**
Wrapper function for [acme_client_retrieves_certificate_http] handling communication over the network
*)
val acme_client_retrieves_certificate_nw:
  client: principal ->
  msg_idx:nat ->
  DYL (nat * is_polling_at_order_endpoint:bool)
  (requires fun h0 ->True)
  (ensures fun h0 r h1 -> True)

(**
 RFC8555 7.4.2 Downloading the Certificate
*)
val acme_client_receives_and_saves_certificate:
  client:principal ->
  http_resp:http_response ->
  DYL nat
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_response http_resp))
  (ensures fun h0 r h1 -> True)

(**
Wrapper function for [acme_client_receives_and_saves_certificate] handling communication over the network
*)
val acme_client_receives_and_saves_certificate_nw:
  client: principal ->
  msg_idx:nat ->
   DYL nat
  (requires fun h0 ->True)
  (ensures fun h0 r h1 -> True)

(**
RFC8555 7.2 Getting a Nonce
*)
val acme_client_request_replay_nonce_nw:
  client: principal ->
  newNonce_url: url ->
   DYL nat
  (requires fun t0 -> 
    is_publishable_p app_preds (trace_len t0) (serialize_url newNonce_url)
  )
  (ensures fun t0 _ t1 -> 
     True
  )

(**
RFC8555 7.2 Getting a Nonce
*)
val acme_client_receives_and_saves_replay_nonce_nw:
  client: principal ->
  msg_idx: nat ->
  DYL nat
  (requires fun h0 ->True)
  (ensures fun h0 r h1 -> True)


(**
RFC8555 7.5.1. Responding to Challenges

   Creates the http request for polling at the order endpoint.

   This endpoint was contained in the Location header of a previous response.
*)
val acme_client_poll_order_create_http_request:
 client:principal ->
 acme_order_sessionid: nat ->
 DYL ( req:http_request * principal * bytes )
  (requires fun h0 -> True)
  (ensures fun h0 (req,_,_) h1 -> is_publishable_p app_preds (trace_len h1) (serialize_http_request req))


(**
   Returns true iff the response contains an acme order with the status 'Ready'.
*)
val acme_client_polling_response_is_ready:
 client:principal ->
 http_resp:http_response ->
 DYL ( bool )
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)


(**
   This function should be used for determining if the client needs to poll at the order endpoint,
   e.g., with the response to the csr request.
*)
val acme_client_poll_at_order_endpoint:
 client:principal ->
 http_resp:http_response ->
 DYL (bool)
  (requires fun h0 -> is_publishable_p app_preds (trace_len h0) (serialize_http_response http_resp))
  (ensures fun h0 _ h1 -> True)
