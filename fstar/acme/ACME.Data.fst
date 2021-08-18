/// ACME.Data (implementation)
/// ===============================
module ACME.Data

open DY.Principals
module DC = DY.Crypto
open Web.Messages
open HelperFunctions

open SerializationHelpers

open Labeled.Crypto
module LC = Labeled.Crypto


(**
Domain-principal mapping can be implemented in various way. 
As long as the mapping is injective, its implementation does not affect the security properties of ACME.

Here we provide a simple implementation of the domain - principal mapping satisfying injectivity:
- A root domain is owned by a principal having the same name
- A sub domain is owned by the principal owing the corresponding root domain
*)
let rec domain_principal_mapping domain =
 match domain with
 |Root str -> str
 |Sub sub dom -> domain_principal_mapping dom // We want to have multiple domains for the same principal - so we just assume that all subdomains of root belong to the same principal

let domain_principal_mapping_lemma dom = ()



let eq_acme_challenge_reflexive_lemma a = ()


let eq_acme_authorization_reflexive_lemma a = ()

let generate_message_for_new_key_inner_jws_signature _alg _jwk _url _inner_payload_account _inner_payload_old_key =
  DC.concat (DC.string_to_bytes _alg) (
    DC.concat _jwk (
      DC.concat (serialize_url _url) (
        DC.concat (serialize_url _inner_payload_account) _inner_payload_old_key
      )
    )
  )

let generate_message_for_new_key_inner_jws_signature_preserves_publishability pr trace_idx _alg _jwk _url _inner_payload_account _inner_payload_old_key = ()


let eq_jws_acme_request a b = (a.key_id == b.key_id) (*/\ (a.nonce == b.nonce)*) /\ (a.url == b.url) /\ (a.payload == b.payload) /\ (a.signature == b.signature)

let generate_message_for_jws_signature _keyId _url _replayNonce _payload =
  let skid = serialize_url _keyId in
  let surl = serialize_url _url in
  let p2 = DC.concat surl _payload in
  DC.concat _replayNonce (DC.concat skid p2)
let generate_message_for_jws_signature_returns_concat _keyId _url _replayNonce _payload = ()

let generate_message_for_jws_signature_preserves_publishability pr trace_idx _keyId _url _replayNonce _payload =
  let skid = serialize_url _keyId in
  let surl = serialize_url _url in
  let p2 = DC.concat surl _payload in
  let p3 = DC.concat skid p2 in
  LC.concatenation_of_publishable_bytes_is_publishable_forall_under_any_preds surl _payload;
  LC.concatenation_of_publishable_bytes_is_publishable_forall_under_any_preds skid p2;
  LC.concatenation_of_publishable_bytes_is_publishable_forall_under_any_preds _replayNonce p3
  

let generate_message_for_jws_signature_structure pr _keyId _url _replayNonce _payload = ()


let generate_signature_for_jws_acme_request pr trace_idx acme_sign_pred _keyId _url _replayNonce _payload  _sign_key reader =
  let msg = generate_message_for_jws_signature _keyId _url _replayNonce _payload in
  assert(LC.is_publishable_p pr trace_idx (serialize_url _keyId));
  assert(LC.is_publishable_p pr trace_idx (serialize_url _url));
  assert(LC.is_publishable_p pr trace_idx _payload);
  assert(LC.is_publishable_p pr trace_idx _replayNonce);
  generate_message_for_jws_signature_preserves_publishability pr trace_idx _keyId _url _replayNonce _payload;
  assert(LC.can_label_of_bytes_flow_to pr trace_idx msg DY.Labels.public);
  let sig_label = LC.get_label msg in
  assert(can_flow (pr.model.corrupt_at trace_idx) sig_label DY.Labels.public);
  let public_msg = LC.restrict #pr #trace_idx #sig_label msg DY.Labels.public in
  assert(LC.is_sign_key_p pr trace_idx _sign_key reader acme_sign_pred);
  assert(DC.sign_pred acme_sign_pred trace_idx (generate_message_for_jws_signature _keyId _url _replayNonce _payload));
  assert(DC.sign_pred acme_sign_pred trace_idx public_msg);
  let signature = LC.sign #pr #trace_idx #reader #acme_sign_pred #DY.Labels.public _sign_key public_msg in
  assert(LC.is_publishable_p pr trace_idx signature);
  signature


let generate_jws_acme_request pr trace_idx acme_sign_pred _keyId _url _replayNonce _payload  _sign_key reader =
  {
   key_id = _keyId;
   url = _url;
   replay_nonce = _replayNonce;
   payload = _payload;
   signature = generate_signature_for_jws_acme_request pr trace_idx acme_sign_pred  _keyId _url _replayNonce _payload  _sign_key reader
  }


let generate_jws_acme_request_properties _ _ _ _ _ _ _ _ _= ()


let generate_request_header_host_domain dom =
   let req_header = (DC.string_to_bytes  "Host", serialize_domain dom) in
   Seq.create 1  req_header

let rec is_token_of_sequence_challenges token challenges =
 if Seq.length challenges > 0 then(
   if DC.eq_bytes token (Seq.head challenges).acme_challenge_token then
     true
   else
     is_token_of_sequence_challenges token (Seq.tail challenges)
 )else false

let is_token_of_acme_authorization token authorization =
  is_token_of_sequence_challenges token authorization.acme_authorization_challenges

