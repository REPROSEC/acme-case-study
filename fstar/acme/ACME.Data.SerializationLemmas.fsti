/// ACME.Data.SerializationLemmas
/// ==============================
module ACME.Data.SerializationLemmas

module LC = Labeled.Crypto
open Web.Messages
module DC = DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Labeled.Crypto
open Labeled.ApplicationAPI
open Application.Predicates
open ACME.Data.Predicates

open SerializationHelpers
open SerializationLemmas
open Helpers
module APH = Application.Predicates.Helpers

open ACME.Data
open ACME.Data.SerializationHelpers

open FStar.Seq
// We need this interface to be able to friend Application.Predicates in the fst file...

#set-options "--z3rlimit 0 --max_fuel 0 --max_ifuel 0"

(** Lemma stating that the label of a serialized acme status flows to public. *)
val serialized_acme_status_label_flows_to_public:
  (trace_index:nat) ->
  (status:acme_status) ->
  Lemma
  (ensures (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_status status) public))


(** Lemma stating that the label of a serialized acme status flows to public. *)
val serialized_option_acme_order_status_label_flows_to_public:
  (trace_index:nat) ->
  status:option (s:acme_status{s=Pending \/ s=Ready \/ s=Processing \/ s=Valid \/ s=Invalid}) ->
  Lemma
  (ensures (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_opt_acme_order_status status) public))


(** Lemma stating that the label of a serialized acme order flows to public. *)
val serialized_acme_order_flows_to_public:
  (trace_index:nat) ->
  (order:acme_order) ->
  Lemma
  (requires (
    Some? order.acme_order_authorizations /\
    Some? order.acme_order_finalize /\ (
      let authorizations_seq = Some?.v order.acme_order_authorizations in (
      forall authz_url. Seq.contains authorizations_seq authz_url ==> is_url_publishable app_preds trace_index authz_url) /\ (
        is_url_publishable app_preds trace_index (Some?.v order.acme_order_finalize) /\ (
          None? order.acme_order_certificate \/ (
            Some? order.acme_order_certificate /\
            is_url_publishable app_preds trace_index (Some?.v order.acme_order_certificate)
          )
        )
      )
    )
  ))
  (ensures (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_order order) public))


val serialize_acme_server_st_issuedvalidnonce_lemma:
  t:DC.bytes ->
  s:string ->
  Lemma
  (ensures (
    match (snd (serialize_acme_server_state (IssuedValidNonce t))) s with
    | None -> True
    | Some t' -> (
      DC.eq_bytes t t' \/
      DC.eq_bytes t' (DY.Crypto.string_to_bytes "IssuedValidNonce") \/
      DC.eq_bytes t' (DY.Crypto.string_to_bytes "acme_server")
    )))
  [SMTPat ((snd (serialize_acme_server_state (IssuedValidNonce t))) s)]


val parse_acme_server_st_of_client_st_returns_none:
  st:acme_client_state ->
  Lemma (ensures Error? (parse_acme_server_state (serialize_acme_client_state st)))


(** Lemma stating that parsing a serialized server state via [parse_acme_client_state] returns None. *)
val parse_acme_client_st_of_server_st_returns_none:
  st:acme_server_state ->
  Lemma (ensures Error? (parse_acme_client_state (serialize_acme_server_state st)))


(**
   Lemma stating that if an acme order can flow to public, then the serialized (optional)
   authorizations, finalize, and certificate urls contained in the order can also flow to public.
*)
val serialized_acme_order_flows_to_public_implies_components_flow_to_public:
  (trace_index:nat) ->
  (order:acme_order) ->
  Lemma
  (requires (
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_order order) public)
  ))
  (ensures (
    let opt_authorizations = order.acme_order_authorizations in
    let opt_finalize = order.acme_order_finalize in
    let opt_cert = order.acme_order_certificate in
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_opt_seq_of_urls opt_authorizations) public) /\
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_opt_url opt_finalize) public) /\
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_opt_url opt_cert) public)
  ))

(**
   Lemma stating that if an acme authorization can flow to public, then the serialized identifier,
   status, and challenges contained in the authorization can also flow to public.
*)
val serialized_acme_authorization_flows_to_public_implies_components_flow_to_public:
  (trace_index:nat) ->
  (authz:acme_authorization) ->
  Lemma
  (requires (
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_authorization authz) public)
  ))
  (ensures (
    let identifier = authz.acme_authorization_identifier in
    let status = authz.acme_authorization_status in
    let challenges = authz.acme_authorization_challenges in
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_domain identifier) public) /\
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_status status) public) /\
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_sequence_of_acme_challenges challenges) public)
  ))

(**
   Lemma stating that an acme order can still flow to public if the status is updated.
*)
val serialized_updated_acme_order_flows_to_public_status:
  (trace_index:nat) ->
  (order:acme_order) ->
  Lemma
  (requires (
    LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_order order) public
  ))
  (ensures (
    forall (status:acme_status{status = Pending \/ status = Processing \/ status = Valid \/ status = Invalid \/ status = Ready}).
    let updated_order:acme_order = {
      order with
      acme_order_status = Some status;
    } in
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_order updated_order) public)
  ))

(**
   Lemma stating that an acme order can still flow to public if the certificate url and status are
   updated.

   This is currently tailored to [acme_server_finalize_order].
*)
val serialized_updated_acme_order_flows_to_public:
  (trace_index:nat) ->
  (order:acme_order) ->
  (cert_url:url) ->
  Lemma
  (requires (
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_order order) public) /\
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_url cert_url) public)
  ))
  (ensures (
    let updated_order:acme_order = {
      order with
      acme_order_status = Some Valid;
      acme_order_certificate = Some cert_url
    } in
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_order updated_order) public)
  ))

(**
   Lemma stating that an acme challenge can still flow to public after updating its status.
*)
val serialized_updated_acme_challenge_flow_to_public:
  (trace_index:nat) ->
  (challenge:acme_challenge) ->
     Lemma
      (requires (
        LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_challenge challenge) public
      ))
      (ensures (
       forall (status:acme_status{status = Pending \/ status = Processing \/ status = Valid \/ status = Invalid}).
       let new_challenge = {challenge with acme_challenge_status = status} in
       LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_challenge new_challenge) public
      ))

(**
   Lemma stating that a sequence of acme challenges can still flow to public if the status of the
   challenge at the given index is updated.
*)
val serialized_updated_acme_challenges_flow_to_public:
  (trace_index:nat) ->
  (challenges:Seq.seq acme_challenge) ->
  (challenge_index:nat) ->
  Lemma
    (requires (
      (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_sequence_of_acme_challenges challenges) public) /\
      challenge_index < Seq.length challenges
    ))
    (ensures (
     forall (status:acme_status{status = Pending \/ status = Processing \/ status = Valid \/ status = Invalid}). (
       let old_challenge = challenges.[challenge_index] in
       let new_challenge = {old_challenge with acme_challenge_status = status} in
       let updated_challenges = challenges.[challenge_index] <- new_challenge in
       LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_sequence_of_acme_challenges updated_challenges) public
    )))
    (decreases (challenge_index))

(**
   Lemma stating that if a sequence of acme challenges can flow to public, then the challenge at the
   given index can also flow to public.
*)
val sequence_of_challenges_publishable_implies_single_challenge_publishable:
  (trace_index:nat) ->
  (challenge_sequence:seq acme_challenge) ->
  (idx:nat{idx < Seq.length challenge_sequence}) ->
  Lemma
    (requires(LC.is_publishable_p app_preds trace_index (serialize_sequence_of_acme_challenges challenge_sequence)))
    (ensures(LC.is_publishable_p app_preds trace_index (serialize_acme_challenge challenge_sequence.[idx])))
    (decreases (idx))

(**
   Lemma stating that an acme authorization can still flow to public if the status of one of the
   challenges is updated.
*)
val serialized_updated_acme_authorization_flows_to_public:
  (trace_index:nat) ->
  (authz:acme_authorization) ->
  (challenge_index:nat) ->
  Lemma
  (requires (
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_authorization authz) public) /\
    challenge_index < Seq.length authz.acme_authorization_challenges
  ))
  (ensures (
    forall (status:acme_status{status = Pending \/ status = Processing \/ status = Valid \/ status = Invalid}). (
    let old_challenge = authz.acme_authorization_challenges.[challenge_index] in
    let new_challenge = {old_challenge with acme_challenge_status = Processing} in
    let updated_authz = {
      authz with
      acme_authorization_challenges = authz.acme_authorization_challenges.[challenge_index] <- new_challenge
    } in
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_authorization updated_authz) public)
  )))

(**
   Lemma stating that an acme authorization can still flow to public if the status of one of the
   challenges and of the authorization is set to Valid.
*)
val serialized_updated_acme_authorization_flows_to_public_challenge_and_authorization:
  (trace_index:nat) ->
  (authz:acme_authorization) ->
  (challenge_index:nat) ->
  Lemma
  (requires (
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_authorization authz) public) /\
    challenge_index < Seq.length authz.acme_authorization_challenges
  ))
  (ensures (
    let challenge = Seq.index (authz.acme_authorization_challenges) challenge_index in
    let challenge' = {challenge with acme_challenge_status = Valid} in
    let authorization' = {authz with acme_authorization_challenges = authz.acme_authorization_challenges.[challenge_index] <- challenge'} in
    let authorization'' = {authorization' with acme_authorization_status = Valid} in
    (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_authorization authorization'') public)
  ))


(**
    Lemma stating that the label of a serialized acme challenge can flow to public if
    [acme_challenge_contains_no_secrets] is true.
*)
val acme_challenge_contains_no_secrets_implies_flow_to_public:
    (trace_index:nat) ->
    (challenge:acme_challenge) ->
    Lemma
      (requires (acme_challenge_contains_no_secrets app_preds trace_index challenge))
      (ensures (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_challenge challenge) public))

(**
    Basically an extension of [acme_challenge_contains_no_secrets_implies_flow_to_public].

    Lemma stating that the label of a serialized sequence of acme challenge can flow to public if
    [sequence_of_acme_challenges_contains_no_secrets] is true.
*)
val sequence_of_acme_challenges_contains_no_secrets_implies_flow_to_public:
  (trace_index:nat) ->
  (challenge_seq:Seq.seq acme_challenge) ->
  Lemma
    (requires (sequence_of_acme_challenges_contains_no_secrets app_preds trace_index challenge_seq))
    (ensures (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_sequence_of_acme_challenges challenge_seq) public))
    (decreases (Seq.length challenge_seq))

(**
    Lemma stating that given an acme authorization, if
    [sequence_of_acme_challenges_contains_no_secrets] is true for the challenges of the
    authorization, then the label of the serialized authorization can flow to public.
*)
val serialized_acme_authorization_can_flow_to_public:
  (trace_index:nat) ->
  (authz:acme_authorization) ->
  Lemma
    (requires (sequence_of_acme_challenges_contains_no_secrets app_preds trace_index authz.acme_authorization_challenges))
    (ensures (LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_authorization authz) public))




val acme_order_containing_only_domain_is_publishable: (trace_index:nat) -> order: acme_order -> Lemma
 (requires acme_order_contains_only_domain trace_index order)
 (ensures acme_order_is_publishable app_preds trace_index order)
 [SMTPat (acme_order_contains_only_domain trace_index order)]



val http_response_is_publishable_implies_acme_order_in_http_response_is_publishable: pr:LC.preds -> (trace_index:nat) -> http_resp:http_response ->
 Lemma
 (requires LC.is_publishable_p pr trace_index (serialize_http_response http_resp))
 (ensures acme_order_in_http_response_is_publishable pr trace_index http_resp)


val http_response_is_publishable_implies_acme_authorization_in_http_response_is_publishable: pr:LC.preds -> (trace_index:nat) -> http_resp:http_response ->
 Lemma
 (requires LC.is_publishable_p pr trace_index (serialize_http_response http_resp))
 (ensures acme_authorization_in_http_response_is_publishable pr trace_index http_resp)

val http_response_is_publishable_implies_certificate_of_http_response_is_publishable: pr:LC.preds -> (trace_index:nat) -> http_resp:http_response ->
 Lemma
 (requires LC.is_publishable_p pr trace_index (serialize_http_response http_resp))
 (ensures certificate_of_http_response_is_publishable pr trace_index http_resp)

val elements_of_jws_acme_request_are_publishable_implies_jws_request_is_publishable:
  pr:LC.preds ->
  (trace_index:nat) ->
  _keyId:url ->
  _url: url ->
  _replayNonce: DC.bytes -> 
  _payload:DC.bytes ->
  _sign_key:DC.bytes ->
  reader:secret_intendees{
    LC.is_sign_key_p pr trace_index _sign_key (readable_by reader) (APH.acme_sig_key_usage reader pr) /\
    (APH.acme_sign_pred reader pr trace_index (generate_message_for_jws_signature _keyId _url _replayNonce _payload))} ->
  Lemma
  (requires LC.is_publishable_p pr trace_index (serialize_url _keyId) /\
            LC.is_publishable_p pr trace_index (serialize_url _url) /\
            LC.is_publishable_p pr trace_index _payload /\
            LC.is_publishable_p pr trace_index _replayNonce
  )
  (ensures (
    let jws_req = generate_jws_acme_request pr trace_index (APH.acme_sig_key_usage reader pr) _keyId _url _replayNonce _payload  _sign_key (readable_by reader) in
    LC.is_publishable_p pr trace_index (serialize_jws_acme_request jws_req)
  ))

val authorization_url_of_publishable_acme_order_is_publishable:
 (trace_index:nat) ->
 (order:acme_order) ->
 (_url:url) ->
 Lemma
 ( requires is_authorization_url_of_acme_order order _url /\
            LC.is_publishable_p app_preds trace_index (serialize_acme_order order)
 )
 ( ensures LC.is_publishable_p app_preds trace_index (serialize_url _url)
 )


val request_header_host_domain_is_publishable:
  (trace_index:nat) ->
  dom:domain ->
  Lemma
  (
    let req_header = generate_request_header_host_domain dom in
    LC.is_publishable_p app_preds trace_index (serialize_sequence_of_bytes_tuples req_header )
  )

val challenge_of_publishable_acme_authorization_is_publishable:
  (trace_index:nat) ->
  (authz: acme_authorization) ->
  (challenge:acme_challenge) ->
  Lemma
  (requires LC.is_publishable_p app_preds trace_index (serialize_acme_authorization authz) /\ is_challenge_of_acme_authorization authz challenge)
  (ensures LC.is_publishable_p app_preds trace_index (serialize_acme_challenge challenge))

val url_and_token_of_publishable_challenge_are_publishable:
  (trace_index:nat) ->
  (challenge:acme_challenge) ->
  Lemma
  (requires LC.is_publishable_p app_preds trace_index (serialize_acme_challenge challenge))
  (ensures
    LC.is_publishable_p app_preds trace_index (serialize_url (challenge.acme_challenge_url)) /\
    LC.is_publishable_p app_preds trace_index challenge.acme_challenge_token
  )

val acme_order_is_publishable_implies_certificate_url_is_publishable:
  (trace_index:nat) ->
  order:acme_order ->
  Lemma
  (requires
    LC.is_publishable_p app_preds trace_index (serialize_acme_order order) /\
    Some? order.acme_order_certificate
  )
  (ensures
    ( let cert_url = Some?.v order.acme_order_certificate in
      LC.is_publishable_p app_preds trace_index (serialize_url cert_url)
    )
  )

val token_of_publishable_challenge_is_publishable:
  (trace_index:nat) ->
  challenge: acme_challenge ->
  Lemma
  (requires LC.is_publishable_p app_preds trace_index (serialize_acme_challenge challenge))
  (ensures LC.is_publishable_p app_preds trace_index challenge.acme_challenge_token)

val acme_order_is_publishable_implies_finalize_url_is_publishable:
  (trace_index:nat) ->
  order:acme_order ->
  Lemma
  (requires
    LC.is_publishable_p app_preds trace_index (serialize_acme_order order) /\
    Some? order.acme_order_finalize
  )
  (ensures
    ( let finalize_url = Some?.v order.acme_order_finalize in
      LC.is_publishable_p app_preds trace_index (serialize_url finalize_url)
    )
  )

val csr_is_publishable_with_publishable_public_key: (trace_index:nat) -> csr:acme_csr -> Lemma
 (requires LC.is_publishable_p app_preds trace_index csr.acme_csr_pub_key)
 (ensures LC.is_publishable_p app_preds trace_index (serialize_acme_csr csr))


(**
  If bytes (that is a csr object) is publishable, then all components of the csr object are also
  publishable.
*)
val parse_acme_csr_publishablity_lemma:
  (pr:LC.preds) ->
  (trace_index:nat) ->
  (t:DC.bytes) ->
  Lemma
  (requires (
    LC.is_publishable_p pr trace_index t /\
    Success? (parse_acme_csr t)
  ))
  (ensures (
    let csr_object = Success?.v (parse_acme_csr t) in
    LC.is_publishable_p pr trace_index csr_object.acme_csr_pub_key /\
    LC.is_publishable_p pr trace_index (serialize_sequence_of_domains csr_object.acme_csr_identifiers)
  ))


(**
  If bytes (that is a jws_acme_request) is publishable, then all components of the jws object are
  also publishable.
*)
val parse_jws_acme_request_lemma_publishablity:
    (pr:LC.preds) ->
    (trace_index:nat) ->
    (t:DC.bytes) ->
    Lemma
      (requires (
        LC.is_publishable_p pr trace_index t /\
        Success? (parse_jws_acme_request t)
      ))
      (ensures (
        let jws_acme_request_object = Success?.v (parse_jws_acme_request t) in
        let key_id = jws_acme_request_object.key_id in
        let url = jws_acme_request_object.url in
        let payload = jws_acme_request_object.payload in
        let signature = jws_acme_request_object.signature in
        LC.is_publishable_p pr trace_index (serialize_url key_id) /\
        LC.is_publishable_p pr trace_index (serialize_url url) /\
        LC.is_publishable_p pr trace_index payload /\
        LC.is_publishable_p pr trace_index signature
      ))


val parse_acme_new_key_inner_jws_lemma_publishablity:
    (pr:LC.preds) ->
    (trace_index:nat) ->
    (t:DC.bytes) ->
    Lemma
      (requires (
        LC.is_publishable_p pr trace_index t /\
        Success? (parse_acme_new_key_inner_jws t)
      ))
      (ensures (
        let jws = Success?.v (parse_acme_new_key_inner_jws t) in
        let alg = string_to_bytes jws.alg in
        let jwk = jws.jwk in
        let url = serialize_url jws.inner_url in
        let account = serialize_url jws.inner_payload_account in
        let old_key = jws.inner_payload_old_key in
        let signature = jws.inner_signature in
        LC.is_publishable_p pr trace_index alg /\
        LC.is_publishable_p pr trace_index jwk /\
        LC.is_publishable_p pr trace_index url /\
        LC.is_publishable_p pr trace_index account /\
        LC.is_publishable_p pr trace_index old_key /\
        LC.is_publishable_p pr trace_index signature
      ))


(**
  If bytes (that is a [jws_acme_request]) is publishable, then the bytes resulting from
  first parsing the jws, and again serializing it, is still publishable.
*)
val serialize_parse_jws_acme_request_publishability_lemma:
  (pr:LC.preds) ->
  (trace_index:nat) ->
  (t:DC.bytes) ->
  Lemma
  (requires
    Success? (parse_jws_acme_request t) /\
    LC.is_publishable_p pr trace_index t)
  (ensures
    LC.is_publishable_p pr trace_index (serialize_jws_acme_request (Success?.v (parse_jws_acme_request t)))
  )


(**
  If an http request is publishable, then the payload of the jws object is also publishable.
*)
val http_request_publishable_implies_payload_of_jws_publishable:
    (pr:LC.preds) ->
    (trace_index:nat) ->
    (http_req:http_request) ->
    Lemma
      (requires LC.is_publishable_p pr trace_index (serialize_http_request http_req))
      (ensures payload_of_jws_in_http_request_is_publishable pr trace_index http_req)


val sequence_of_authorization_info_is_publishable
  (pr:LC.preds)
  (trace_index:nat)
  (seq_authz_info:Seq.seq authorization_info)
 :Lemma
  (ensures (LC.is_publishable_p pr trace_index (serialize_sequence_of_authorization_info seq_authz_info)))
  (decreases (Seq.length seq_authz_info))

