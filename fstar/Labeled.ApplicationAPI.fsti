/// Labeled.ApplicationAPI
/// ======================
///
/// This module defines an API to be used by applications to implement "their" protocol. The
/// functions are intended to be called by the principals and some of them are stateful as they
/// modify or read the trace.

module Labeled.ApplicationAPI

open Helpers
open DY.Principals
open DY.Labels
open DY.Crypto
module C = DY.Crypto
open DY.Entry
open DY.Monad
open DY.Trace
module L = Labeled.Crypto
open Application.Predicates

/// .. _general_valid_trace:
/// 
/// General valid trace predicate
/// -----------------------------
///
/// This predicate defines some general properties which should always be fulfilled by the trace.
///
/// Specifically, this predicate is true iff:
///
/// - All published bytes (i.e., sent messages/bytes) are labeled with a publishable label (one that
///   can flow to public).
/// - All internal states of principals are readable by the respective principal (more precisely: By
///   the respective version and session of that principal).
/// - All key derivations respect the labeling (i.e., the label on some key ``k`` before key
///   derivation can flow to the label of the derived key ``k'`` after key derivation).
///
/// Note that it does **not** contain any application-specific properties (like, e.g., privacy or
/// integrity properties related to a specific protocol).
(** General predicate on global state (all sent messages are labeled "publishable", all session
states can be read by the owner and key derivation respects the labeling) *)
val valid_trace: trace -> Type0

val valid_trace_event_lemma: t:trace -> i:nat -> s:principal -> e:event ->
  Lemma ((valid_trace t /\
	  i < trace_len t /\
	  did_event_occur_at i s e) ==>
	  event_pred i s e)
	  [SMTPat (valid_trace t); SMTPat (did_event_occur_at i s e)]

let valid_trace_event_lemma_forall (t:trace) :
  Lemma (forall i s e. (valid_trace t /\
		   i < trace_len t /\
		   did_event_occur_at i s e) ==>
		   event_pred i s e) = ()

val valid_trace_respects_state_inv: (trace:trace) -> (i:nat) -> (p:principal) -> (v:version_vec)-> (s:principal_state) ->
  Lemma (requires (valid_trace trace /\  i < trace_len trace /\  is_set_state_at i p v s))
        (ensures (state_inv i p v s))
        [SMTPat (valid_trace trace); SMTPat (is_set_state_at i p v s)]


/// An effect abbreviation for DY functions that preserve trace validity

effect DYL0 (a:Type) (pre:pre_t) (post:trace -> result a -> trace -> Type0) =
  DYERROR a (fun p s0 ->
    valid_trace s0 /\ pre s0 /\
    (forall (x:result a) (s1:trace). (valid_trace s1 /\ post s0 x s1) ==> p x s1))

effect DYL (a:Type) (pre:pre_t) (post:trace -> a -> trace -> Type0) =
  DYL0 a pre (fun s0 r s1 ->
    (Error? r ==> True) /\
    (Success? r ==> post s0 (Success?.v r) s1))


/// Some special subtypes of bytes
/// ------------------------------
///
/// Here, we instantiate some restricted subtypes of ``bytes`` which allow us to handle labels with
/// more or less "precision", depending on what the bytes are used for: E.g., for "data", we usually
/// don't care about the exact label, we only care about whether the label on the data, aka bytes,
/// can flow to wherever we send it. For keys on the other hand, we *do* care about the exact label
/// when using them to encrypt/decrypt stuff (to determine the label of the resulting
/// cipher-/plaintext).
///
/// Note that these types are mostly just instantiated from the parametric (in `app_preds`) types in
/// :ref:`Labeled.Crypto <labeled_crypto_lbytes_p>`, as we now have the actual `app_preds`.
///
/// Also note that the names "secret" and "msg" are taken from the pi calculus conventions.

(** Type for regular bytes with a valid label equal to [l]. *)
type lbytes_at (i:nat) (l:label) = t:C.bytes{L.is_labeled_p app_preds i t l}

(** A predicate for valid bytes *)
let is_valid_at (i:nat) (t:bytes) = L.is_valid_p app_preds i t

(** A predicate for public bytes *)
let is_labeled_at (i:nat) (t:bytes) (l:label) = L.is_labeled_p app_preds i t l

(** A predicate for public bytes *)
let is_publishable_at (i:nat) (t:bytes) = L.is_publishable_p app_preds i t

(** A predicate for secret bytes *)
let is_secret_at (i:nat) (t:bytes) (l:label) (u:usage) (up:usage_pred u) =
  L.is_secret_p app_preds i t l u up

(** Type for bytes whose label is (exactly) [ReadableBy allowed_knowers] and whose usage is
(exactly) [u]. Intended for secrets like keys for which we need the exact labeling information when
using them (as opposed to "data", for which we usually only care about "where can this label flow
to?"). *)
type secret_at (i:nat) (l:label) (u:usage) (up:C.usage_pred u) =
  t:bytes{is_secret_at i t l u up}


(** Type for bytes whose label is (exactly) [ReadableBy allowed_knowers] and whose usage is
(exactly) [u] OR that have been issued by a corrupt principal...
this one is "bigger", it also contains publishable (has a label that can flow to public) bytes issued by a corrupt principal. *)
type issued_secret_at (i:nat) (l:label) (u:usage) (up:C.usage_pred u) =
  t:bytes{L.issued_secret_p app_preds i l u up}

(** Type for bytes whose label can flow to [l]. Intended to be used for everything that is
considered "data" (as opposed to keys). These values might still have to be kept secret, but on a
technical level, we're not interested in its exact label, we just want to know where it can flow
to. *)
type msg_at (i:nat) (l:label) =
  t:bytes{L.can_label_of_bytes_flow_to app_preds i t l}

(** Type for bytes which represent private keys for decryption. *)
let is_private_dec_key_at (i:nat) (t:C.bytes) (l:label) (up:C.usage_pred C.pke_key_usage) =
  L.is_private_dec_key_p app_preds i t l up
type private_dec_key_at (i:nat) (l:label) up =
  t:bytes{is_private_dec_key_at i t l up}

(** Type for bytes which represent (publishable) public keys for encryption. *)
let is_public_enc_key_at (i:nat) (t:C.bytes) (l:label) (up:C.usage_pred C.pke_key_usage) =
  L.is_public_enc_key_p app_preds i t l up
type public_enc_key_at (i:nat) (l:label) up =
  t:bytes{is_public_enc_key_at i t l up}

(** Type for bytes which represent keys for symmetric de-/encryption. *)
let is_ae_key_at (i:nat) (t:C.bytes) (l:label) (up:C.usage_pred C.ae_key_usage) =
  L.is_ae_key_p app_preds i t l up
type ae_key_at (i:nat) (l:label) up =
  t:bytes{is_ae_key_at i t l up}

(** Type for bytes which represent private keys for signing. *)
let is_sign_key_at (i:nat) (t:C.bytes) (l:label) (up:C.usage_pred C.sig_key_usage) =
  L.is_sign_key_p app_preds i t l up
type sign_key_at (i:nat) (l:label) up =
  t:bytes{is_sign_key_at i t l up}

(** Type for bytes which represent (publishable) public keys for signature verification. *)
let is_verify_key_at (i:nat) (t:C.bytes) (l:label) (up:C.usage_pred C.sig_key_usage) =
  L.is_verify_key_p app_preds i t l up
type verify_key_at (i:nat) (l:label) up =
  t:bytes{is_verify_key_at i t l up}

(** Type for bytes which represent key material from which new keys can be derived (via HKDF, which
is also where extract/expand come from). *)
let is_kdf_key_at
    (i:nat)
    (t:C.bytes)
    (l:label)
    (ext_l:label)
    (ext_u:usage)
    (exp_u:usage)
    (up1:usage_pred ext_u)
    (up2:usage_pred exp_u) =
    L.is_secret_p app_preds i t l (C.kdf_usage (ext_l,ext_u) exp_u) (C.kdf_usage_pred ext_l ext_u exp_u up1 up2)

type kdf_key_at
    (i:nat)
    (l:label)
    (ext_l:label)
    (ext_u:usage)
    (exp_u:usage)
    (up1:usage_pred ext_u)
    (up2:usage_pred exp_u)
  =
    t:bytes{is_kdf_key_at i t l ext_l ext_u exp_u up1 up2}

(** Type for bytes which represent private keys for MAC verification. *)
let is_mac_key_at i t l up =
  L.is_mac_key_p app_preds i t l up
type mac_key_at i (l:label) up =
  t:bytes{is_mac_key_at i t l up}
type verify_mac_key_at i (l:label) up = mac_key_at i l up

(** Type for bytes which represent private keys for generating DH shared secret *)
let is_dh_private_key_at (i:nat) (t:C.bytes) (l:label) (u:usage) (up:C.usage_pred u) =
  L.is_dh_private_key_p app_preds i t l u up
type dh_private_key_at i (l:label) u up =
  t:bytes{is_dh_private_key_at i t l u up}

(** Type for bytes which represent publishable (public) keys for generating DH shared secret *)
let is_dh_public_key_at (i:nat) (t:C.bytes) (l:label) (u:usage) (up:C.usage_pred u) =
  L.is_dh_public_key_p app_preds i t l u up
type dh_public_key_at i (l:label) u up =
  t:bytes{is_dh_public_key_at i t l u up}

(** Type for bytes which represent a DH shared secret *)
let is_dh_shared_secret_at i (t:C.bytes) (l:label) (u:usage) (up:C.usage_pred u) =
  L.is_secret_p app_preds i t l u up
type dh_shared_secret_at i (l:label) u up =
  t:bytes{is_dh_shared_secret_at i t l u up}

let can_flow_at i l1 l2 = L.can_flow (corrupt_at i) l1 l2
let can_label_of_bytes_flow_at i t l = L.can_label_of_bytes_flow_to app_preds i t l

let pke_pred_at i up t = C.pke_pred up i t
let sign_pred_at i up t = C.sign_pred up i t
let mac_pred_at i up t = C.mac_pred up i t
let ae_pred_at i up t ad = C.ae_pred up i t ad

/// Lemmas about publishability
/// ---------------------------


val corrupt_principals_have_publishable_state_at: t:trace -> trace_index:nat ->
  Lemma (requires (valid_trace t /\ trace_index <= trace_len t))
        (ensures (
          forall j prin version_vector s session_index (key_in_session:string) (value:bytes).
          (
            Seq.length version_vector > session_index /\
            corrupt_at trace_index (sess_ver prin session_index (Seq.index version_vector session_index)) /\
            j < trace_index /\
            is_set_state_at j prin version_vector s /\
            is_some (lookup s.[session_index] key_in_session) value
          )
          ==>
          is_publishable_at trace_index value
        ))


val published_value_is_publishable: tr:trace -> i:nat -> t:bytes ->
  Lemma (requires (valid_trace tr /\ trace_len tr > i /\ is_published_before i t))
        (ensures (is_publishable_at (trace_len tr) t))
        [SMTPat (valid_trace tr); SMTPat(is_published_before i t)]

val auth_published_value_at_is_publishable: tr:trace -> i:nat -> t:bytes ->
  Lemma (requires (valid_trace tr /\ trace_len tr > i /\ is_auth_published_at i t))
        (ensures (is_publishable_at (trace_len tr) t))
        [SMTPat (valid_trace tr); SMTPat(is_auth_published_at i t)]

val auth_published_value_is_publishable: tr:trace -> i:nat -> t:bytes ->
  Lemma (requires (valid_trace tr /\ trace_len tr > i /\ is_auth_published_before i t))
        (ensures (is_publishable_at (trace_len tr) t))
        [SMTPat (valid_trace tr); SMTPat(is_auth_published_before i t)]

/// Constructors for usages
/// -----------------------

let pke_key_usage = pke_key_usage
let ae_key_usage = ae_key_usage
let mac_key_usage = mac_key_usage
let sig_key_usage = sig_key_usage
let kdf_key_usage = kdf_usage
let nonce_key_usage = nonce_usage
let dh_key_usage u = dh_key_usage u


/// Predicates to distinguish key types
/// -----------------------------------



/// Cryptographic API

/// Construct bytes from literals
/// -----------------------------

val literal_to_bytes: s:C.literal -> msg_at 0 public
val literal_to_bytes_lemma: s:C.literal ->
  Lemma (ensures (literal_to_bytes s == C.literal_to_bytes s))
        [SMTPat (literal_to_bytes s)]
val bytes_to_literal: #i:nat -> #l:label -> t:msg_at i l -> Err C.literal
  (ensures (fun r -> match r with
		  | Success s -> C.bytes_to_literal t == Success s
		  | Error e -> C.bytes_to_literal t == Error e))


let string_to_bytes s = literal_to_bytes (String s)
val bytes_to_string: #i:nat -> #l:label -> t:msg_at i l -> Err string
  (ensures (fun r -> match r with
		  | Success s -> C.bytes_to_string t == Success s
		  | Error e -> C.bytes_to_string t == Error e))

let nat_to_bytes s = literal_to_bytes (Nat s)
val bytes_to_nat: #i:nat -> #l:label -> t:msg_at i l -> Err nat
  (ensures (fun r -> match r with
		  | Success s -> C.bytes_to_nat t == Success s
		  | Error e -> C.bytes_to_nat t == Error e))


/// (De)Construct labeled tuples
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

val concat: #i:nat -> #l:label -> msg_at i l -> msg_at i l -> msg_at i l

val concat_lemma: #i:nat -> #l:label -> t1:msg_at i l -> t2:msg_at i l ->
    Lemma (ensures (concat #i #l t1 t2 == C.concat t1 t2))
          [SMTPat (concat #i #l t1 t2)]

val split: #i:nat -> #l:label -> t:msg_at i l -> Err (msg_at i l & msg_at i l)
		      (ensures (fun r -> match r with
				      | Error x -> C.split t == Error x
				      | Success (x,y) -> C.split t == Success (x,y)))

/// Asymmetric cryptographic primitives
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// Creating public keys
/// ....................

(** Create a public key (intended for asymmetric encryption) from a private (decryption) key. *)
val pk: #i:nat -> #l:label -> #up:C.usage_pred C.pke_key_usage ->
	private_dec_key_at i l up -> public_enc_key_at i l up
val pk_lemma: #i:nat -> #l:label -> #up:C.usage_pred C.pke_key_usage ->
	s:private_dec_key_at i l up ->
  Lemma (ensures (pk s == C.pk s))
        [SMTPat (pk s)]

(** Get label of corresponding private key, or return Public if it is not a public key *)
let get_label_of_private_dec_key t = L.get_label_of_private_dec_key t

(** Create a public key (intended for signature verification) from a private (signing) key. *)
val vk: #i:nat -> #l:label -> #up:C.usage_pred C.sig_key_usage ->
	sign_key_at i l up -> verify_key_at i l up
val vk_lemma: #i:nat -> #l:label -> #up:C.usage_pred C.sig_key_usage ->
	 s:sign_key_at i l up ->
  Lemma (ensures (vk s == C.pk s))
        [SMTPat (vk s)]

(** Create a DH public key (intended for asymmetric encryption) from a private (decryption) key. *)
val dh_pk: #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u ->
	   dh_private_key_at i l u up -> dh_public_key_at i l u up
val dh_pk_lemma: #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u ->
	  s:dh_private_key_at i l u up -> 
  Lemma (ensures (dh_pk s == C.pk s))
        [SMTPat (dh_pk s)]

(** Get label of corresponding DH private key, or return Public if it is not a DH public key *)
let get_label_of_dh_public_key t u = L.get_label_of_dh_public_key t u

/// Encryption
/// ..........

(** Asymmetric encryption of bytes [message] using a public (encryption) key [public_key]. *)
val pke_enc:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    public_key:public_enc_key_at i l up ->
    message:msg_at i l{pke_pred_at i up message} ->
    msg_at i public
val pke_enc_lemma:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    p:public_enc_key_at i l up ->
    m:msg_at i l ->
  Lemma (ensures (pke_pred_at i up m ==> pke_enc #i #l p m == C.pke_enc p m))
        [SMTPat (pke_enc p m)]


/// Decryption
/// ..........

(**
Asymmetric decryption of a ciphertext using a private (decryption) key. This is modeled such that
decryption is only possible using the (one unique) private key matching the public key used to
encrypt. If the ciphertext was encrypted using a different private key or is not a PKE ciphertext at
all, this function returns None.

If decryption succeeds and the plaintext is not publishable, the returned plaintext is guaranteed to
satisfy [pke_pred].
*)
val pke_dec:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    private_key:private_dec_key_at i l up ->
    ciphertext:msg_at i public ->
    Err (msg_at i l)
    (ensures (fun r -> match r with
         | Success p -> C.pke_dec private_key ciphertext == Success p /\
		       (is_publishable_at i p \/ (pke_pred_at i up p) \/ pke_un_pred l p)
         | Error x -> C.pke_dec private_key ciphertext == Error x))

/// Signing
/// .......

(**
Create a signature (just the tag) for a message [m] using a signing key [k]. The tag itself does not
reveal the signed message, but carries the same label as the message.
*)
val sign:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l':label ->
    k:sign_key_at i l up ->
    m:msg_at i l'{sign_pred_at i up m} ->
    msg_at i l'
val sign_lemma:
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l2:label ->
    k:sign_key_at i l1 up ->
    m:msg_at i l2 ->
  Lemma (ensures (sign_pred_at i up m ==> sign k m == C.sign k m))
        [SMTPat (sign k m)]

/// Verification of signatures
/// ..........................

(**
Verify a signature tag [s] for a message [m] using the verification key [p]. If verification
succeeds and the signing key (i.e., the private key corresponding to the verification key [p]) is
not known to any corrupted parties, this function guarantees that [m] satisfies [up].
*)
val verify:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l2:label ->
    p:verify_key_at i l up ->
    m:msg_at i l2 ->
    s:msg_at i l2 ->
    bool
val verify_lemma:
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l2:label ->
    p:verify_key_at i l1 up ->
    m:msg_at i l2 ->
    s:msg_at i l2 ->
  Lemma (ensures (
	 if verify p m s then
            C.verify p m s /\ (can_flow_at i l1 public \/ sign_pred_at i up m) 
         else (C.verify p m s = false)))
        [SMTPat (verify p m s)]

/// Authenticated Encryption with (optional) Associated Data
/// ........................................................

/// Encryption
/// ..........

let to_opt_bytes (#i:nat) (ad:option (msg_at i public)): option bytes =
  match ad with
  | Some x -> Some x
  | None -> None

(** Symmetric (authenticated) encryption of a message [m] under an encryption
key [k] with associated data [ad]. *)
val aead_enc:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:ae_key_at i l up ->
    m:msg_at i l ->
    ad:option (msg_at i public){ae_pred_at i up m (to_opt_bytes ad)} ->
    msg_at i public
val aead_enc_lemma:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:ae_key_at i l up ->
    m:msg_at i l ->
    ad:option (msg_at i public) ->
  Lemma (ensures (ae_pred_at i up m (to_opt_bytes ad) ==>
		  aead_enc #i #l k m ad == C.aead_enc k m (to_opt_bytes ad)))
        [SMTPat (aead_enc k m ad)]


/// Decryption
/// ..........

(**
Symmetric decryption of a ciphertext using (de-/encryption) key [k]. This is modeled such that
decryption is only possible using the same key as was used to encrypt. If the ciphertext was
encrypted using a different key, is not an AEnc ciphertext at all, or the associated data attached
to the ciphertext is different from [ad], this function returns None.

If decryption succeeds and the plaintext is not publishable, the returned plaintext is guaranteed to
satisfy [pr.aead_pred].
*)
val aead_dec:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:ae_key_at i l up ->
    c:msg_at i public ->
    ad:option (msg_at i public) ->
    Err (msg_at i l)
    (ensures (fun r -> match r with
         | Success p -> C.aead_dec k c (to_opt_bytes ad) == Success p /\
			 (is_publishable_at i k \/
			  ae_pred_at i up p (to_opt_bytes ad))
         | Error s -> C.aead_dec k c (to_opt_bytes ad) == Error s))



/// MAC
/// .......

(**
Create a MAC (just the tag) for a message [m] using a signing key [k]. The tag itself does not
reveal the  message, but carries the same label as the message.
*)
val mac:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l':label ->
    k:mac_key_at i l up ->
    m:msg_at i l'{mac_pred_at i up m} ->
    msg_at i l'
val mac_lemma:
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l2:label ->
    k:mac_key_at i l1 up ->
    m:msg_at i l2 ->
  Lemma (ensures (mac_pred_at i up m ==> mac k m == C.mac k m))
        [SMTPat (mac k m)]

/// Verification of MACs
/// ..........................

(**
Verify a MAC tag [s] for a message [m] using the verification key [k]. If verification
succeeds and the key [k] is not known to any corrupted parties, this function guarantees that [m] satisfies [pr.mac_pred]. 
*)
val verify_mac:
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l2:label ->
    k:mac_key_at i l up ->
    m:msg_at i l2 ->
    s:msg_at i l2 ->
    bool
val verify_mac_lemma:
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l2:label ->
    k:mac_key_at i l1 up ->
    m:msg_at i l2 ->
    s:msg_at i l2 ->
  Lemma (ensures (if verify_mac k m s then
            C.verify_mac k m s /\ (can_flow_at i l1 public \/ mac_pred_at i up m) 
         else (C.verify_mac k m s = false)))
        [SMTPat (verify_mac k m s)]

/// Creating DH keys
/// ....................

(** Create a DH shared secret from a DH private and public key *)
val dh: #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> #l':label -> 
	dh_private_key_at i l u up ->
	dh_public_key_at i l' u up ->
	dh_shared_secret_at i (join l l') u up

val dh_lemma: #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> #l':label ->
	      k:dh_private_key_at i l u up ->
	      pk:dh_public_key_at i l' u up ->
  Lemma (ensures (dh #i #l #u #up #l' k pk == C.dh k pk)) [SMTPat (dh k pk)]

(** Create a DH shared secret from a DH private and untrusted public key *)
val dh_un: #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> 
	   k:dh_private_key_at i l u up ->
	   pk:msg_at i public -> 
	   Err (lbytes_at i (L.get_label (C.dh k pk))) 
	   (ensures (fun r -> match r with
			   | Success c -> (C.is_pk pk /\ c == C.dh k pk /\ L.can_label_of_bytes_flow_to app_preds i c l /\ 
					 (match L.get_label_of_secret c with 
					   | Some l' -> l' == (L.get_label c) 
					   | None -> L.get_label c == public) /\
					 (match L.get_label_and_usage_of_private_key pk with 
					   | Some (l', u') -> if C.eq_usage u' (C.dh_key_usage u) then 
								(L.get_usage_of_secret c == Some u \/ 
								  L.get_usage_of_secret c == C.get_dh_usage u') /\ 
								(eq_label (L.get_label c) (join l l'))
							     else True 
					   | None -> True))
			   | Error x -> True))

/// Hashing

val hash:
    #i:nat ->
    #l:label ->
    m:msg_at i l ->
    msg_at i l


/// Key derivation
/// ~~~~~~~~~~~~~~

val kdf_extract:
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_at i l1 l2 u1 u2 up1 up2 ->
    context:msg_at i public ->
    secret_at i l2 u1 up1

val kdf_expand:
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_at i l1 l2 u1 u2 up1 up2 ->
    context:msg_at i public ->
    secret_at i l1 u2 up2

val kdf_extract_lemma:
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_at i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_at i public ->
    Lemma (ensures (kdf_extract k ctx == C.kdf k ctx true))
    [SMTPat (kdf_extract k ctx)]

val kdf_expand_lemma:
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_at i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_at i public ->
    Lemma (ensures (kdf_expand k ctx == C.kdf k ctx false))
    [SMTPat (kdf_expand k ctx)]

val kdf_extract_usage_lemma:
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_at i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_at i public ->
    Lemma (ensures (L.get_usage_of_secret (kdf_extract k ctx) == Some u1))
          [SMTPat (L.get_usage_of_secret (kdf_extract k ctx))]

val kdf_expand_usage_lemma:
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_at i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_at i public ->
    Lemma (ensures (L.get_usage_of_secret (kdf_expand k ctx) == Some u2))
          [SMTPat (L.get_usage_of_secret (kdf_expand k ctx))]

/// Stateful application API
/// ------------------------

(** Generate a fresh nonce with the given issuers/readers and usage. *)
val secret_gen: l:label -> u:usage -> up:usage_pred u -> DYL (i:nat & secret_at i l u up)
    (requires (fun t0 -> L.are_kdf_labels_increasing (corrupt_at (trace_len t0)) l u))
    (ensures (fun t0 (|i,s|) t1 ->
	i == trace_len t0 /\
	trace_len t1 = trace_len t0 + 1 /\
        is_nonce_generated_at (trace_len t0) s l u up /\
        is_labeled_at (trace_len t0) s l))

(** Generate a fresh unique identifier. Such an identifier is guaranteed to be unique
(but it is a public value). *)
val guid_gen: unit -> DYL (i:nat & lbytes_at i public)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|i,s|) t1 ->
	 i == trace_len t0 /\
	 trace_len t1 = trace_len t0 + 2 /\
         is_nonce_generated_at (trace_len t0) s public guid_usage (default_usage_pred guid_usage) /\
         is_published_at (trace_len t0 + 1) s /\
         is_labeled_at (trace_len t0) s public))

(** Record an application-specific event to the trace with the given principal as "sender". *)
val trigger_event: p:principal -> ev:event -> DYL unit
    (requires (fun t0 -> event_pred (trace_len t0) p ev))
    (ensures (fun t0 (s) t1 ->
         trace_len t1 = trace_len t0 + 1 /\
         did_event_occur_at (trace_len t0) p ev))

(** Send a message (or, to be precise: Record the sending to the trace). Returns the index of the
send event in the trace (needed to receive that message later). *)
val send: #i:nat -> sender:principal -> receiver:principal ->
	  message:msg_at i public -> DYL nat
    (requires (fun t0 -> i <= trace_len t0))
    (ensures (fun t0 r t1 ->
	  r == trace_len t0 /\
          trace_len t1 = trace_len t0 + 1 /\
          is_published_at (trace_len t0) message /\
          is_message_sent_at (trace_len t0) sender receiver message))


(** Authenticated message sent on the network *)
val authenticated_send: #i:nat -> sender:principal -> receiver:principal ->
			message:msg_at i public -> DYL nat
    (requires (fun t0 -> i <= trace_len t0 /\
          authenticated_send_pred (trace_len t0) sender receiver message))
    (ensures (fun t0 r t1 ->
	  r == trace_len t0 /\
	  trace_len t1 = trace_len t0 + 1 /\
	  is_auth_published_at (trace_len t0) message /\
          is_authenticated_message_sent_at (trace_len t0) sender receiver message))


(** Receive a message for [receiver] sent at the given index. If the event at the given index is not
a send event or the receiver does not match the intended receiver (as recorded in the send event),
this function returns None. *)
val receive_i: index_of_send_event:nat -> receiver:principal ->
     DYL (now:nat & sender:principal & msg_at now public)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,t|) t1 ->  t0 == t1 /\
	  now = trace_len t0 /\
	  index_of_send_event < trace_len t0 /\
	  is_published_at index_of_send_event t /\
          (exists sender recv. is_message_sent_at index_of_send_event sender recv t)))


(** Authenticate message received on the network *)
val authenticated_receive_i:
    index_of_send_event:nat ->
    receiver:principal ->
    DYL (now:nat & sender:principal & msg_at now public)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,message|) t1 -> t0 == t1 /\
	  now = trace_len t0 /\
	  index_of_send_event < trace_len t0 /\
          is_publishable_at index_of_send_event message /\
	  (exists recv.
	    is_authenticated_message_sent_at index_of_send_event sender recv message /\
	    (corrupt_at index_of_send_event (any sender) \/
	     authenticated_send_pred index_of_send_event sender recv message))))

(** Set the internal state of principal p. *)
val set_state: p:principal -> v:version_vec -> s:principal_state -> DYL unit
    (requires (fun t0 -> is_principal_state_readable (trace_len t0) p v s /\
		      state_inv (trace_len t0) p v s))
    (ensures (fun t0 r t1 -> trace_len t1 = trace_len t0 + 1 /\
			  is_set_state_at (trace_len t0) p v s))

(** Get the state set at trace index [i] of principal p. If the event at index [i] is not a set
state event or the event is a set state for another principal, this function returns None. *)
val get_state_i: i:nat -> p:principal ->
		 DYL (now:nat & v:version_vec & principal_state)
     (requires (fun t0 -> True))
     (ensures (fun t0 (|now,v,s|) t1 -> t0 == t1 /\
	      i < trace_len t0 /\
	      now = trace_len t0 /\
	      is_set_state_at i p v s /\
	      state_inv now p v s /\
	      is_principal_state_readable now p v s))

(** Returns the "current" state of principal p, i.e., the last state that was set for p. Together
with the state, this function also returns the "current" time (the length of the trace) *)
val get_last_state: p:principal -> DYL (now:nat & v:version_vec & principal_state)
     (requires (fun t0 -> True)) 
     (ensures (fun t0 (|now,v,s|) t1 ->  t0 == t1 /\
	      (exists i. i < now /\ is_set_state_at i p v s) /\
	      now = trace_len t0 /\
	      state_inv now p v s /\
	      is_principal_state_readable now p v s))

(** Checks whether a principal's state has been set before. *)
val has_state_set:
  p:principal ->
  DYL bool
  (requires fun _ -> True)
  (ensures fun t0 b t1 ->
    (b2t(b) <==> (exists i v s. i < trace_len t0 /\ is_set_state_at i p v s)) /\
    t1 == t0
  )


val publishable_of_secret_implies_corruption:
  #i:nat ->
  #l:label ->
  #u:C.usage ->
  #up:C.usage_pred u ->
  s:secret_at i l u up ->
  Lemma
  (ensures (forall allowed_knowers. (l == readable_by allowed_knowers /\ is_publishable_at i s) ==> (L.contains_corrupt_principal (corrupt_at i) allowed_knowers)))

val restrict: #i:nat -> #l1:label -> t:msg_at i l1 -> l2:label{forall i. can_flow_at i l1 l2} -> t':msg_at i l2{t' == t}

val is_set_state_at_implies_set_state_before_now: i:nat -> p:principal -> v:version_vec -> st:principal_state ->
 DY unit
 (requires fun h -> is_set_state_at i p v st)
 ( ensures fun h0 _ h1 -> h0 == h1 /\ //modifies_trace h0 h1 /\
     i < trace_len h0  
 )
