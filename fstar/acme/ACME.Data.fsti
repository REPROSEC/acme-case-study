/// ACME.Data
/// ===============================
module ACME.Data

open DY.Principals
module DC = DY.Crypto
open Web.Messages
open HelperFunctions

open SerializationHelpers

open SerializationLemmas

open Labeled.Crypto
module LC = Labeled.Crypto

(**
Modeling artifact: We model DNS using a simple domain - principal mapping.
This mapping is injective: one domain cannot be owned by two different principals,
however, two differents domains can be owned by one pricipal.
*)
val domain_principal_mapping: domain -> principal

(**
This lemma is supposed to be used only for ACME.Test module.
To typheck testing modules, we must verify whether a domain belongs to a principal.
Basically, the lemma only exposes the (simple) implementation of the mapping:
- A root domain is owned by a principal having the same name
- A sub domain is owned by the principal owing the corresponding root domain
*)
val domain_principal_mapping_lemma: (dom:domain)-> Lemma
  (ensures(
    match dom with
    |Root str -> str = domain_principal_mapping dom
    |Sub sub dom1 -> domain_principal_mapping dom1 =  domain_principal_mapping dom
  ))

(**
Status of all kind of objects in ACME.
See RFC8555 7.1.6
*)
type acme_status =
  | Pending: acme_status
  | Deactivated: acme_status
  | Revoked: acme_status
  | Valid: acme_status
  | Invalid: acme_status
  | Ready: acme_status
  | Processing: acme_status
  | Expired: acme_status



(**
Account is model as a record 
RFC8555 7.1.2

*)
type acme_account = {
  status: s:acme_status{s = Valid \/ s = Deactivated \/ s = Revoked};
  // contact: option (list url);
  // bytesOfServiceAgreed: option bool;
  // externalAccountBinding: option external_account;
}


(** ACME order object type - see RFC8555 Section 7.1.3 *)
noeq type acme_order = {
  acme_order_status: option (s:acme_status{s= Pending \/ s= Ready \/ s= Processing \/ s= Valid \/ s=Invalid}); // can be pending, ready, processing, valid, and invalid - Note that this is required in the order object definition in Section 7.1.3, but for a new-order message (as defined in Section 7.4), status is left out.
  // expires: bytes; // expiration timestamp of order
  acme_order_identifiers: doms:(Seq.seq domain){Seq.length doms > 0}; // list of domains for certificate -- this is a bit simplified as the standard also allows other identifiers than domains
  // notBefore: bytes; // validitiy time range of certificate
  // notAfter: bytes; // validity time range of certificate
  // error: bytes; // error information
  acme_order_authorizations: option (Seq.seq url); // list of pending authorizations/challenges (URLs/identifiers, not the actual authorization objects themselves) that the client needs to prove in pending orders
  acme_order_finalize: option url; // url for finalizing a order, i.e., sending a CSR to
  acme_order_certificate: option url; // the issued certificate
}





type acme_challenge_type =
  | HTTP01: acme_challenge_type
  | DNS01: acme_challenge_type



(** ACME challenge object type. Note that there is no global definition of this object type. In the specification, the structure of this object depends on the actual challenge type. For dns-01 and http-01, however, the structure is the same. We simplify here, by just using one structural type - see RFC8555 Section 7.1.5 as well as Section 8 *)
noeq type acme_challenge = {
  acme_challenge_challenge_type: acme_challenge_type; // can be http-01 or dns-01
  acme_challenge_url: url; // url for client to trigger verification of this challenge
  acme_challenge_status: s:acme_status{s = Pending \/ s = Processing \/ s = Valid \/ s = Invalid};
  acme_challenge_token: DC.bytes; // issued by a server s for a domain d
}


let eq_acme_challenge a b =
  a.acme_challenge_challenge_type = b.acme_challenge_challenge_type /\
  eq_url a.acme_challenge_url b.acme_challenge_url /\
  a.acme_challenge_status = b.acme_challenge_status /\
  DC.eq_bytes a.acme_challenge_token b.acme_challenge_token

val eq_acme_challenge_reflexive_lemma:
  a:acme_challenge ->
  Lemma (ensures (eq_acme_challenge a a))
  [SMTPat (eq_acme_challenge a a)]


(** ACME authorization object type - see RFC8555 Section 7.1.4 *)
noeq type acme_authorization = {
  acme_authorization_identifier: domain; // a domain
  acme_authorization_status: s:acme_status{s = Pending \/ s = Valid \/ s = Invalid \/ s = Deactivated \/ s = Expired \/ s = Revoked}; // if a server stores a valid authorization in its state, the challenge has been successfully solved by the client
  // expires: bytes;
  acme_authorization_challenges: Seq.seq acme_challenge;
  // wildcard: option boolean;
}


let eq_acme_authorization a b =
  a.acme_authorization_identifier = b.acme_authorization_identifier /\
  a.acme_authorization_status = b.acme_authorization_status /\
  Seq.length a.acme_authorization_challenges = Seq.length b.acme_authorization_challenges /\
  (forall i . eq_acme_challenge (Seq.index a.acme_authorization_challenges i) (Seq.index b.acme_authorization_challenges i))

val eq_acme_authorization_reflexive_lemma:
  a:acme_authorization ->
  Lemma (ensures (eq_acme_authorization a a))


noeq type acme_certificate = {
  acme_certificate_pub_key: DC.bytes;
  acme_certificate_identifiers: ids:Seq.seq domain{Seq.length ids > 0};
  acme_certificate_issuer: domain; //domain of the CA that created the certificate
  acme_certificate_signature: DC.bytes; //signature over the public key, identifiers, and the issuer
}


noeq type acme_csr = {
  acme_csr_identifiers: ids:Seq.seq domain{Seq.length ids > 0};
  acme_csr_pub_key:DC.bytes
}

(**
store the authorization information necessary for proof
*)
type authorization_info ={
  authz_info_identifier:domain;
  authz_info_status: acme_status;
}

noeq type acme_server_state =
  | IssuedValidNonce: DC.bytes -> acme_server_state //nonce has been issued 
  | UserAccount: account: acme_account -> public_key: DC.bytes -> account_url: url -> acme_server_state 
  | Order: order: acme_order -> user_account_sessionid: nat -> acc_url:url -> acc_pub_key:DC.bytes -> seq_authz_info:Seq.seq authorization_info -> acme_server_state
  | Authorization: authorization_url: url -> authorization: acme_authorization -> order_sessionid: nat -> acme_server_state
  | PrivateCAKey: private_ca_key:DC.bytes -> acme_server_state
  | Certificate: set_cert_idx: nat -> cert:acme_certificate -> certificate_url:url -> account_pub_key:DC.bytes -> acme_server_state
  | ProcessingChallenge: authorization_sessionid:nat -> challenge_idx:nat -> http_request_id:DC.bytes -> acme_server_state


noeq type client_account =
  {
     private_key:DC.bytes;
     server:principal;
     account_url: url //it should be option url if we take account management (creation, deletion , etc.) into account
  }

/// Objects for key rollover (Sec. 7.3.5)
/// -------------------------------------
///
/// ACME clients can change the (public) key associated with an account by sending a special request
/// to the ACME server's ``key-change`` endpoint.  See `Section 7.3.5 of the ACME RFC
/// <https://tools.ietf.org/html/rfc8555#section-7.3.5>` for details.
///
/// Such a key rollover request consists of two nested JWS, i.e., the inner JWS is the payload of
/// the outer JWS. The outer JWS is a "regular" JWS as used in many other places in ACME.
///
/// Inner JWS for a key rollover request, note the absence of the ``nonce`` and ``kid`` headers, the
/// latter is "replaced" by a ``jwk`` field containing the new account public key.
noeq type acme_new_key_inner_jws =
  {
    alg: string; // Signature algorithm used to sign this JWS
    jwk: DC.bytes; // The new (public) account key
    inner_url: url; // The same url as in the "outer" JWS
    inner_payload_account: url; // Account URL, a.k.a. kid
    inner_payload_old_key: DC.bytes; // Old public key
    inner_signature: DC.bytes
  }

val generate_message_for_new_key_inner_jws_signature:
  _alg: string ->
  _jwk: DC.bytes ->
  _url: url ->
  _inner_payload_account: url ->
  _inner_payload_old_key: DC.bytes ->
  DC.bytes

val generate_message_for_new_key_inner_jws_signature_preserves_publishability:
    pr: LC.preds ->
    trace_idx:nat ->
    _alg: string ->
    _jwk: DC.bytes ->
    _url: url ->
    _inner_payload_account: url ->
    _inner_payload_old_key: DC.bytes ->
  Lemma
  (requires (
    LC.is_publishable_p pr trace_idx (DC.string_to_bytes _alg) /\
    LC.is_publishable_p pr trace_idx _jwk /\
    LC.is_publishable_p pr trace_idx (serialize_url _url) /\
    LC.is_publishable_p pr trace_idx (serialize_url _inner_payload_account) /\
    LC.is_publishable_p pr trace_idx _inner_payload_old_key
    )
  )
  (ensures (
    let msg = generate_message_for_new_key_inner_jws_signature _alg _jwk _url _inner_payload_account _inner_payload_old_key in
    (LC.is_publishable_p pr trace_idx msg)
  ))


/// Generic JWS object (Sec. 6.2)
/// -----------------------------
///
/// Note that we don't consider the case where a JWS contains a ``jwk`` instead of a ``kid`` header
/// field.
(** a generic data type to encapsulate jws messages in http bodies *)
noeq type jws_acme_request = {
  key_id: url; // same as account_url
  replay_nonce: DC.bytes;
  url: url;
  payload: DC.bytes;
  signature: DC.bytes;
}

val eq_jws_acme_request: a:jws_acme_request -> b:jws_acme_request -> Type0

let is_jws_acme_request_publishable
  (#pr: LC.preds)
  (trace_idx:nat)
  (r:jws_acme_request) =
    is_url_publishable pr trace_idx r.key_id /\
    is_url_publishable pr trace_idx r.url /\
    LC.is_publishable_p pr trace_idx r.payload /\
    LC.is_publishable_p pr trace_idx r.signature /\
    LC.is_publishable_p pr trace_idx r.replay_nonce

val generate_message_for_jws_signature:
  _keyId: url ->
  _url: url ->
  _replayNonce:DC.bytes ->
  _payload: DC.bytes ->
  DC.bytes

val generate_message_for_jws_signature_returns_concat:
  _keyId: url ->
  _url: url ->
  _replayNonce:DC.bytes ->
  _payload: DC.bytes ->
  Lemma
  ( generate_message_for_jws_signature _keyId _url _replayNonce _payload == DC.concat _replayNonce (DC.concat (serialize_url _keyId) (DC.concat (serialize_url _url) _payload))
  )

val generate_message_for_jws_signature_preserves_publishability:
    pr: LC.preds ->
    trace_idx:nat ->
    _keyId: url ->
    _url: url ->
    _replayNonce:DC.bytes ->
    _payload: DC.bytes ->
  Lemma
  (requires (
    LC.is_publishable_p pr trace_idx (serialize_url _keyId) /\
    LC.is_publishable_p pr trace_idx (serialize_url _url) /\
    LC.is_publishable_p pr trace_idx _payload /\
    LC.is_publishable_p pr trace_idx _replayNonce
    )
  )
  (ensures (
    let msg = generate_message_for_jws_signature _keyId _url _replayNonce _payload in
    (LC.is_publishable_p pr trace_idx msg)
  ))


(**
   Lemma showing that [generate_message_for_jws_signature] generates the concatenation of its inputs.
*)
val generate_message_for_jws_signature_structure:
    pr: LC.preds ->
    _keyId: url ->
    _url: url ->
    _replayNonce:DC.bytes ->
    _payload: DC.bytes ->
    Lemma
    (ensures (
      let msg = generate_message_for_jws_signature _keyId _url _replayNonce _payload in
      msg ==  DC.concat _replayNonce (DY.Crypto.concat (serialize_url _keyId) (DY.Crypto.concat (serialize_url _url) _payload)
    )))


(**
  Generates the signature for the jws request. The [secret_intendees] of the signing key must be
  given explicitly, and [pr.sign_pred] must hold true.
*)
val generate_signature_for_jws_acme_request:
   pr:LC.preds ->
   trace_idx:nat ->
   up:DC.usage_pred DC.sig_key_usage ->
   _keyId:url{LC.is_publishable_p pr trace_idx (serialize_url _keyId)} ->
  _url: url{LC.is_publishable_p pr trace_idx (serialize_url _url)} ->
  _replayNonce:DC.bytes{LC.is_publishable_p pr trace_idx _replayNonce} ->
  _payload:DC.bytes{LC.is_publishable_p pr trace_idx _payload} ->
  _sign_key:DC.bytes ->
  reader:DY.Labels.label{
    LC.is_sign_key_p pr trace_idx _sign_key reader up /\
    (DC.sign_pred up trace_idx (generate_message_for_jws_signature _keyId _url _replayNonce _payload))} ->
  signature:DC.bytes{LC.is_publishable_p pr trace_idx signature}


(**
  Generates the jws request. The [secret_intendees] of the signing key must be given explicitly, and
  [pr.sign_pred] must hold true.
*)
val generate_jws_acme_request:
  pr:LC.preds ->
  trace_idx:nat ->
  up:DC.usage_pred DC.sig_key_usage ->
  _keyId:url{LC.is_publishable_p pr trace_idx (serialize_url _keyId)} ->
  _url: url{LC.is_publishable_p pr trace_idx (serialize_url _url)} ->
  _replayNonce:DC.bytes{LC.is_publishable_p pr trace_idx _replayNonce} ->
  _payload:DC.bytes{LC.is_publishable_p pr trace_idx _payload} ->
  _sign_key:DC.bytes ->
  reader:DY.Labels.label{
    LC.is_sign_key_p pr trace_idx _sign_key reader up /\
    (DC.sign_pred up trace_idx (generate_message_for_jws_signature _keyId _url _replayNonce _payload))} ->
  jws_acme_request


(**
   Lemma relating the jws object created by [generate_jws_acme_request] to its input values.
*)
val generate_jws_acme_request_properties:
  pr:LC.preds ->
  trace_idx:nat ->
  acme_sign_pred:DC.usage_pred DC.sig_key_usage ->
  _keyId:url{LC.is_publishable_p pr trace_idx (serialize_url _keyId)} ->
  _url: url{LC.is_publishable_p pr trace_idx (serialize_url _url)} ->
  _replayNonce:DC.bytes{LC.is_publishable_p pr trace_idx _replayNonce} ->
  _payload:DC.bytes{LC.is_publishable_p pr trace_idx _payload} ->
  _sign_key:DC.bytes ->
  reader:DY.Labels.label{
    LC.is_sign_key_p pr  trace_idx _sign_key reader acme_sign_pred /\
    (DC.sign_pred acme_sign_pred trace_idx (generate_message_for_jws_signature _keyId _url _replayNonce _payload))} ->
  Lemma (ensures (
    let jws_req = generate_jws_acme_request pr trace_idx acme_sign_pred _keyId _url _replayNonce _payload _sign_key reader in
    jws_req.key_id == _keyId /\
    jws_req.url == _url /\
    jws_req.payload == _payload /\
    jws_req.signature == generate_signature_for_jws_acme_request pr trace_idx acme_sign_pred _keyId _url _replayNonce _payload _sign_key reader
  ))
  [SMTPat (generate_jws_acme_request pr trace_idx acme_sign_pred _keyId _url _replayNonce _payload _sign_key reader)]


noeq type acme_client_state =
  |Account: private_key:DC.bytes -> account_url: url -> order_url:url -> acme_client_state
  |HTTPSPendingRequest: request_nonce:DC.bytes -> reference_sessionid:nat -> server_domain:domain -> acme_client_state
  |ACMEOrder: acme_order_object:acme_order -> account_sessionid:nat -> opt_current_order_url:option url -> acme_client_state
  |ACMEAuthorziation: acme_authorization_object: acme_authorization -> acme_order_sessionid: nat -> acme_client_state
  |CSR: cert_private_key:DC.bytes -> identifiers: Seq.seq domain -> acme_order_sessionid:nat -> csr_set_state_idx:nat -> acme_client_state
  |RetrieveCertificate: csr_sessionid:nat -> acme_client_state
  |ReceivedCertificate: certificate: acme_certificate -> retrieve_cert_sessionid:nat -> set_state_idx:nat -> acme_client_state
  |ChallengeResponse: authz_sessionid: nat -> request_id:DC.bytes -> acme_client_state
  |ReplayNonce: nonce:DC.bytes -> valid:bool -> server_domain:domain -> acme_client_state  //the replay nonce that can be used to send request. valid: if the nonce has been used then valid is false, otherwise true
  |ReplayNonceRequest: server_domain:domain -> acme_client_state //waiting for the replay nonce sent by server owning server_domain



(*
let token_of_authorization_is_publishable (pr:preds) (acme_authorization_object: acme_authorization) : Type0 =
 (forall (i:nat). i<Seq.length (acme_authorization_object.acme_authorization_challenges) ==> is_publishable pr (( acme_authorization_object.acme_authorization_challenges).[i]).acme_challenge_token)
*)

(**
return a request header [("Host", dom)]
*)
val generate_request_header_host_domain:
  dom:domain ->
  req_header:Seq.seq http_header{
    req_header == Seq.create 1 (DY.Crypto.string_to_bytes "Host", (serialize_domain dom))
  }

val is_token_of_sequence_challenges:
 token:DC.bytes ->
 challenges: Seq.seq acme_challenge ->
 Tot bool
 (decreases (Seq.length challenges))

val is_token_of_acme_authorization:
  token: DC.bytes ->
  authorization: acme_authorization ->
  bool
