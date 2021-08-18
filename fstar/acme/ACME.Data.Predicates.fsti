/// ACME.Data.Predicates
/// ==============================
module ACME.Data.Predicates
(**
 - To write/typecheck a protocol runs, we need that the input (which is the output of another function) satisfy some properties.
   For example: the authorization (generated by the server that then processed as the input of the client) must satisfy that the tokens embedded in it are publishable.
 - This module contains predicates used to refine the types in ACME.Client.* and ACME.Server.*
*)

module DC = DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Web.Messages
module LC = Labeled.Crypto
open ACME.Data
open ACME.Data.SerializationHelpers
open SerializationLemmas
open SerializationHelpers
open Helpers



(**
    Predicate that is true iff the label of the token inside the challenge can flow to public and if
    [is_url_publishable] is true for the url inside the challenge.
*)
let acme_challenge_contains_no_secrets (pr:LC.preds) (trace_index:nat) (challenge:acme_challenge) : Type0 =
  let challenge_url = challenge.acme_challenge_url in
  let challenge_token = challenge.acme_challenge_token in
  (is_url_publishable pr trace_index challenge_url) /\
  (LC.can_label_of_bytes_flow_to pr trace_index challenge_token public)

(**
    Extension of [acme_challenge_contains_no_secrets] to a sequence of acme challenges.
*)
let sequence_of_acme_challenges_contains_no_secrets (pr:LC.preds) (trace_index:nat) (challenge_seq:Seq.seq acme_challenge) =
  forall challenge. Seq.contains challenge_seq challenge ==> acme_challenge_contains_no_secrets pr trace_index challenge


let acme_authorization_is_publishable  (pr:LC.preds) (trace_index:nat) (authorization:acme_authorization): Type0 =
   LC.can_label_of_bytes_flow_to pr trace_index (serialize_acme_authorization authorization) public

let acme_authorization_in_http_response_is_publishable (pr:LC.preds) (trace_index:nat) (http_resp: http_response): Type0 =
   match parse_acme_authorization (http_resp.resp_body) with
   | Success authorization -> acme_authorization_is_publishable pr trace_index authorization
   | _ -> True

(** label of serialized certificate can flow to public*)
let certificate_is_publishable (pr:LC.preds) (trace_index:nat) (certificate:acme_certificate): Type0 =
  LC.can_label_of_bytes_flow_to pr trace_index (serialize_acme_certificate certificate) public

let certificate_of_http_response_is_publishable (pr:LC.preds) (trace_index:nat) (http_resp: http_response): Type0 =
  match parse_acme_certificate (http_resp.resp_body) with
   | Success certificate -> certificate_is_publishable pr trace_index certificate
   | _ -> True

let acme_order_contains_only_domain (trace_index:nat) (order:acme_order): Type0 =
 None? order.acme_order_status /\
 None? order.acme_order_authorizations /\
 None? order.acme_order_finalize /\
 None? order.acme_order_certificate


let acme_order_is_publishable (pr:LC.preds) (trace_index:nat) (order:acme_order): Type0 =
 LC.can_label_of_bytes_flow_to pr trace_index (serialize_acme_order order) public

let acme_order_in_http_response_is_publishable (pr:LC.preds) (trace_index:nat) (http_resp: http_response): Type0 =
  match parse_acme_order http_resp.resp_body with
  | Success order -> acme_order_is_publishable pr trace_index order
  |_ -> True

(**
    Predicate on http requests. True, if the request contains either no jws object, or a jws object
    with a publishable payload.
*)
let payload_of_jws_in_http_request_is_publishable (pr:LC.preds) (trace_index:nat) (http_req:http_request): Type0 =
  match parse_jws_acme_request http_req.req_body with
  | Error _ -> True
  | Success jws_acme_request_object -> (
    let payload = jws_acme_request_object.payload in
    LC.is_publishable_p pr trace_index payload
  )

let http_request_header_contains_domain_of_server (req:http_request) (server:principal): bool =
   match get_header_from_headers "Host" req.req_headers 0 with
       | None -> false
       | Some (host_header_key, host_header_value) -> (
         match parse_domain host_header_value with
         | Error _ -> false
         | Success domain_from_req ->
           domain_principal_mapping domain_from_req = server
     )

let http_request_header_contains_domain_of_server_lemma
  (http_req:http_request)
  (server:principal)
: Lemma
  (requires(
   match get_header_from_headers "Host" http_req.req_headers 0 with
     | None -> False
     | Some (host_header_key, host_header_value) -> (
       match parse_domain host_header_value with
       | Error _ -> False
       | Success domain_from_req ->
         domain_principal_mapping domain_from_req = server
  )))
  (ensures(
    http_request_header_contains_domain_of_server http_req server
  )) = ()


let is_ACMEOrder_session
  (sess:DY.Entry.session_state)
 : Type0
 =
 match parse_acme_client_state sess with
 | Success st -> ACMEOrder? st
 | _ -> False

let is_Order_session
  (sess:DY.Entry.session_state)
 : Type0
 =
 match parse_acme_server_state sess with
 | Success st -> Order? st
 | _ -> False

let is_ReplayNonce_session
 (sess:DY.Entry.session_state)
 : Type0
 =
 match parse_acme_client_state sess with
 | Success st -> ReplayNonce? st
 | _ -> False


let is_authorization_url_of_acme_order
 (order:acme_order)
 (_url:url)
 :Type0
 =
 Some? order.acme_order_authorizations /\
 ( let authz_urls = Some?.v order.acme_order_authorizations in
   Seq.contains authz_urls _url
 )


let is_challenge_of_acme_authorization
 (authz: acme_authorization)
 (challenge:acme_challenge)
 :Type0 =
 Seq.contains authz.acme_authorization_challenges challenge


(**
an acme_order object is an init order iff:
 - all option fields have None value
*)
//val is_init_order: init_order:acme_order -> bool
let is_init_order (order:acme_order) : bool =
  None? order.acme_order_status &&
  None? order.acme_order_authorizations &&
  None? order.acme_order_finalize &&
  None? order.acme_order_certificate

(**
an acme_order object is an updated order (the order generated and sent by the server after receiving the init order iff:
 - the field acme_order_certificate has None value
 - all other option fields have Some value
 - the sequence Some?.v [acme_order_authorizations] has at least one element
 - acme_order_status = Some Pending
*)
//val is_updated_order: acme_order -> bool
let is_updated_order (order:acme_order) : bool =
  order.acme_order_status = Some Pending &&
  Some? order.acme_order_authorizations &&
  Seq.length (Some?.v order.acme_order_authorizations) > 0 &&
  Some? order.acme_order_finalize &&
  None? order.acme_order_certificate
(**
an acme_order object is a finalize order (the order generated and sent by the server after ALL challenge has been solved sucessfully) iff:
 - all option fields have Some value
 - acme_order_status = Some Valid
*)
//val is_finalize_order: acme_order -> bool
let is_finalize_order (order:acme_order) : bool =
  order.acme_order_status = Some Valid &&
  Some? order.acme_order_authorizations &&
  Seq.length (Some?.v order.acme_order_authorizations) > 0 &&
  Some? order.acme_order_finalize &&
  Some? order.acme_order_certificate


(**

  An acme_order object is a finalize order with status Processing (the order generated and sent by
  the server at the finalize endpoint) iff:
 - acme_order_status = Some Processing
 - except for the certificate field, all option fields have Some value
*)
let is_finalize_processing_order (order:acme_order) : bool =
  order.acme_order_status = Some Processing &&
  Some? order.acme_order_authorizations &&
  Seq.length (Some?.v order.acme_order_authorizations) > 0 &&
  Some? order.acme_order_finalize &&
  None? order.acme_order_certificate


(**
[updated_order] is the updated order of the init order [init_order] iff:
  - [init_order] is an init order
  - [updated_order] is an updated_order
  - they have the same acme_order_identifiers
*)
//val is_init_and_updated_order: init_order: acme_order -> updated_order: acme_order -> bool
let is_init_and_updated_order (init_order:acme_order) (updated_order:acme_order) : bool =
  is_init_order init_order &&
  is_updated_order updated_order &&
  //init_order.acme_order_identifiers = updated_order.acme_order_identifiers
  is_same_set init_order.acme_order_identifiers updated_order.acme_order_identifiers

(**
[finalize_order] is the finalize version of [updated_order] iff:
 - [updated_order] is an updated_order
 - [finalize_order] is a finalize order
 - they have the same values on fields: acme_order_identifiers, acme_order_authorizations, acme_order_finalize
 - the return value cannot be bool because the type url is noeq
*)
//val is_updated_and_finalize_order: updated_order: acme_order -> finalize_order:acme_order -> Type0
let is_updated_and_finalize_order (updated_order:acme_order) (finalize_order:acme_order) : bool =
  is_updated_order updated_order &&
  is_finalize_order finalize_order &&
  //updated_order.acme_order_identifiers = finalize_order.acme_order_identifiers &&
  is_same_set updated_order.acme_order_identifiers finalize_order.acme_order_identifiers &&
  eq_url (Some?.v updated_order.acme_order_finalize) (Some?.v finalize_order.acme_order_finalize) &&
  //eq_sequence_url (Some?.v updated_order.acme_order_authorizations) (Some?.v finalize_order.acme_order_authorizations)
  is_same_set_of_urls (Some?.v updated_order.acme_order_authorizations) (Some?.v finalize_order.acme_order_authorizations)


(**
  [finalize_order] is the finalize version of [updated_order] with the status Processing iff:
 - [updated_order] is an updated_order
 - [finalize_order] is a finalize order with the status Processing
 - they have the same values on fields: acme_order_identifiers, acme_order_authorizations, acme_order_finalize
*)
let is_updated_and_finalize_processing_order (updated_order:acme_order) (finalize_order:acme_order) : bool =
  is_updated_order updated_order &&
  is_finalize_processing_order finalize_order &&
  is_same_set updated_order.acme_order_identifiers finalize_order.acme_order_identifiers &&
  eq_url (Some?.v updated_order.acme_order_finalize) (Some?.v finalize_order.acme_order_finalize) &&
  is_same_set_of_urls (Some?.v updated_order.acme_order_authorizations) (Some?.v finalize_order.acme_order_authorizations)
