/// DY.Crypto
/// =========
///
/// This module defines a classic Dolev-Yao model of bytes.  For this, it defines literals (see
/// :ref:`literal_label`) and bytes (see :ref:`bytes_label`), along with an explicit definition of
/// the equational theory.
///
/// .. fst::
///  :class: hidden

module DY.Crypto

open Helpers

/// .. _literal_label:
///
/// Literals
/// --------
///
/// A literal can be either a sequence of bytes, a string, or a natural number.
///
type literal =
 | ByteSeq of FStar.Seq.seq FStar.UInt8.t
 | String of string
 | Nat of nat
 | Bool of bool

(** An empty ByteSeq literal. *)
let empty_byte_seq: literal = ByteSeq Seq.empty

/// .. _usage_label:
///
/// Usage
/// --------
///
/// Here, the usage just indicates the usage of a secret, but this is not enforced (the usage will be enforced at the labeling layer).
///

(** Abstract type to describe the intended usage of nonces and keys. *)
val usage: Type0

(** Indicates that bytes should be used as a private key for public key cryptography. Public keys
have a [None] usage (see Labeled.Crypto.get_usage_of_secret). *)
val pke_key_usage: usage

(** Indicates that bytes should be used as a key for authenticated encryption. *)
val ae_key_usage: usage

(** Indicates that bytes should be used as a key for creating MACs. *)
val mac_key_usage: usage

(** Indicates that bytes should be used as a private key for creating signatures. Public keys
have a [None] usage (see Labeled.Crypto.get_usage_of_secret). *)
val sig_key_usage: usage

(**
Indicates that bytes can be used for deriving a new secret. A new secret can be derived by
either doing an 'expand' or an 'extract'. The kdf_usage contains the new label if an extract was
done, together with the new usage after doing an 'extract', and the new usage if an 'expand' was
done (in this order). In case of an 'expand', the label of the secret does not change.
*)
val kdf_usage: ( (*extract_label*) DY.Labels.label & (*extract_usage*) usage) -> (*expand_usage*) usage -> usage

(** Indicates that bytes should be used as a nonce. *)
val nonce_usage: usage

(**
Indicates that bytes should be used as globally unique identifier. Note that other than nonces,
GUIDs are considered to be public values.
*)
val guid_usage: usage

(** Indicates that bytes should be used as a key for creating DH shared secrets. *)
val dh_key_usage: usage -> usage

val get_dh_usage: u:usage -> u':(option usage){match u' with | Some u' -> dh_key_usage u' == u | None -> True}

(** Pretty-printer for usage *)
val sprint_usage: usage -> string

(**
This is mainly used for checking values created by the attacker, as values created by the attacker have
to be public (as well as every derived value).

Precondition for pub_gen.

Returns true if the usage is not KDF. In the case of KDF, the predicate is true if:
1) the extract_label is public
2) the predicate holds true recursively for both KDF usages
*)
val is_pub_usage: usage -> Type0
// If you derive from a public nonce, the result has a public label (label inside the usage is <= label outside usage - you can only go from less public to more public)
// Attacker can only generate public nonces (and thus everything derived from that must still be public)


/// .. _bytes_label:
///
/// Bytes
/// --------
///
/// * **Literal l** (where l is a literal as defined above)
/// * **Concat t1 t2** (where t1, t2 are bytes)
/// * **Nonce nat label usage** (with given label and usage, where nat is a natural number)
/// * **PK t** (where t is bytes)
/// * **PKEnc t1 t2** (where t1 is the public key and t2 the plaintext bytes)
/// * **Derive key context bool** (key derivation using a key, context and a flag that indicates whether an extract (True) or expand (False) was done)
/// * **AEnc t1 t2 ad** (where t1 is a symmetric key, t2 is the plaintext bytes, and ad is the optional associated data)
/// * **Sig t1 t2** (where t1 is a private key and t2 is the bytes for which the signature is created)
/// * **Mac t1 t2** (where t1 is a shared secret key and t2 is the bytes which has to be tagged)
///

(** Abstract type for bytes. *)
val bytes : Type0

(** Pretty-printer for bytes. *)
val sprint_bytes: bytes -> string

(** Pretty-printer for nonce generation events. *)
val sprint_generated_nonce: bytes -> string


/// .. _eq_bytes_label_usage:
///
/// Equational Theory
/// -----------------
///
/// Checks for identity, except for KDF and DH usage.

val eq_usage : u:usage -> u':usage -> bool

val eq_usage_reflexive_lemma : u:usage -> u':usage ->
    Lemma (ensures (u == u' ==> eq_usage u u'))
    [SMTPat (eq_usage u u')]

val eq_usage_symmetric_lemma : u:usage -> u':usage ->
    Lemma (ensures (eq_usage u u' ==> eq_usage u' u))
    [SMTPat (eq_usage u u')]

val eq_usage_transitive_lemma : u:usage -> u':usage -> u'':usage ->
    Lemma (ensures (eq_usage u u' /\ eq_usage u' u'' ==> eq_usage u u''))
    [SMTPat (eq_usage u u'); SMTPat (eq_usage u' u'')]

/// The equality of bytes is defined by eq_bytes. Two bytes t1 and t2 are equal, if:
///
/// * t1, t2 are both the **same literal**
/// * t1 and t2 are both **conatenation** of bytes, and both components are equal
/// * t1 and t2 are both **nonces** with the same value and same label
/// * t1 and t2 are both **public keys**, where the corresponding private keys are equal
/// * t1 and t2 are both **ciphertexts**, where the corresponding keys and messages are equal
///   (and if in the case of authenticated encryption, the associated data is equal)
/// * t1 and t2 are both **tags (signatures)**, over the same keys and data
/// * t1 and t2 are both **derived keys** using equal keys, equal contexts and the same flag
///
/// Note that having a "custom" equality function allows us to modify parts of the equational theory
/// without changing the basic bytes type.

(**
Instead of using has_eq, we use eq_bytes for defining equality of bytes. By this approach, we can
also define the equational theory of the model.

eq_bytes should be primarily used within the model, as its usage by principals and the
attacker could leak information, e.g., whether two secrets are the same.
*)
val eq_bytes: bytes -> bytes -> bool

val eq_bytes_is_reflexive: t1:bytes -> t2:bytes ->
  Lemma (ensures (t1 == t2 ==> eq_bytes t1 t2))
        [SMTPat (eq_bytes t1 t2)]

val eq_bytes_is_symmetric: t1:bytes -> t2:bytes ->
  Lemma (ensures (eq_bytes t1 t2 ==> eq_bytes t2 t1))
        [SMTPat (eq_bytes t1 t2)]

val eq_bytes_is_transitive: t1:bytes -> t2:bytes -> t3:bytes ->
  Lemma (ensures (eq_bytes t1 t2 /\ eq_bytes t2 t3 ==> eq_bytes t1 t3))

val eq_bytes_is_equal : t1:bytes -> t2:bytes -> Lemma (eq_bytes t1 t2 <==> t1 == t2) [SMTPat (eq_bytes t1 t2)]

let (=~=) t1 t2 = eq_bytes t1 t2

/// Some convenience functions/lemmas for eq_bytes users

let eq_opt_bytes t1 t2 : bool =
  match t1,t2 with
  | None, None -> true
  | Some t1', Some t2' -> eq_bytes t1' t2'
  | _ -> false

let rec eq_list_bytes tl1 tl2 : bool =
  match tl1,tl2 with
  | [],[] -> true
  | h1::t1,h2::t2 -> eq_bytes h1 h2 && eq_list_bytes t1 t2
  | _ -> false

let eq_list_bytes_lemma1 (a a' : bytes) : 
  Lemma (eq_list_bytes [a] [a'] = (eq_bytes a a'))
  [SMTPat (eq_list_bytes [a] [a'])]  = ()

let eq_list_bytes_lemma2 (a1 a1' a2 a2' : bytes) : 
  Lemma (eq_list_bytes [a1;a2] [a1';a2'] = (eq_bytes a1 a1' && eq_bytes a2 a2'))
  [SMTPat (eq_list_bytes [a1;a2] [a1';a2'])]  = ()

let eq_list_bytes_lemma3 (a1 a1' a2 a2' a3 a3' : bytes) : 
  Lemma (eq_list_bytes [a1;a2;a3] [a1';a2';a3'] = (eq_bytes a1 a1' && eq_bytes a2 a2' && eq_bytes a3 a3'))
   [SMTPat (eq_list_bytes [a1;a2;a3] [a1';a2';a3'])]  = ()

let eq_list_bytes_lemma4 (a1 a1' a2 a2' a3 a3' a4 a4': bytes) : 
  Lemma (eq_list_bytes [a1;a2;a3;a4] [a1';a2';a3';a4'] = (eq_bytes a1 a1' && eq_bytes a2 a2' && eq_bytes a3 a3' && eq_bytes a4 a4'))
  [SMTPat (eq_list_bytes [a1;a2;a3;a4] [a1';a2';a3';a4'])]  = ()
  
let rec eq_list_bytes_is_reflexive (tl:list bytes) :
  Lemma (ensures (eq_list_bytes tl tl))
  [SMTPat (eq_list_bytes tl tl)] =
  match tl with
  | h::t -> eq_list_bytes_is_reflexive t
  | _ -> ()

let rec eq_list_bytes_is_symmetric (tl1:list bytes) (tl2:list bytes) :
  Lemma (ensures (eq_list_bytes tl1 tl2 ==> eq_list_bytes tl2 tl1))
  [SMTPat (eq_list_bytes tl1 tl2)] =
  match tl1, tl2 with
  | h1::t1, h2::t2 -> eq_list_bytes_is_symmetric t1 t2
  | _ -> ()

let rec eq_list_bytes_is_transitive (tl1:list bytes) (tl2:list bytes) (tl3:list bytes):
  Lemma (ensures ((eq_list_bytes tl1 tl2 /\ eq_list_bytes tl2 tl3) ==> eq_list_bytes tl1 tl3))
  [SMTPat (eq_list_bytes tl1 tl2);SMTPat (eq_list_bytes tl2 tl3)] =
  match tl1, tl2, tl3 with
  | h1::t1, h2::t2, h3::t3 -> eq_bytes_is_transitive h1 h2 h3;eq_list_bytes_is_transitive t1 t2 t3
  | _ -> ()

/// Usage predicates
/// ----------------

(** Abstract type of predicate that enforces the intended usage of nonces and keys. *)
val usage_pred_: Type u#1

(* Validity matches a usage pred to a usage;
   future: maybe require that each usage pred should be preserved under equality? *)
let is_payload_pred (p:(nat -> payload:bytes -> Type0)) =
  forall i t1. (forall t2. eq_bytes t1 t2 ==> (p i t1 <==> p i t2))
let is_payload_ad_pred (p:(payload:nat -> bytes -> ad:option bytes -> Type0)) =
  forall i t1 ad1 t2 ad2. eq_bytes t1 t2 /\ eq_opt_bytes ad1 ad2 ==> (p i t1 ad1 <==> p i t2 ad2)

// Used to "decide" whether some cryptographic operation on message m is "permitted" at trace index i
type payload_pred = p:(trace_index:nat -> message:bytes -> Type0){is_payload_pred p}
type payload_ad_pred = p:(trace_index:nat -> message:bytes -> associated_data:option bytes -> Type0){is_payload_ad_pred p}

val is_valid_usage_pred: usage -> usage_pred_ -> Type0
val is_valid_usage_pred_eq: u1:usage -> up:usage_pred_ -> u2:usage ->
    Lemma ((is_valid_usage_pred u1 up /\ eq_usage u1 u2) ==> is_valid_usage_pred u2 up)
    [SMTPat (is_valid_usage_pred u1 up); SMTPat (eq_usage u1 u2)]

type usage_pred (u:usage) = up:usage_pred_{is_valid_usage_pred u up}


(* Usage predicates: should they take trace indexes?
   Ideally, each pred is preserved under equality, and is monotonic over indexes *)
// Functions to construct instances of usage_pred
val pke_key_usage_pred: payload_pred -> usage_pred (pke_key_usage)
val ae_key_usage_pred: payload_ad_pred -> usage_pred (ae_key_usage)
val mac_key_usage_pred: payload_pred -> usage_pred (mac_key_usage)
val sig_key_usage_pred: payload_pred -> usage_pred (sig_key_usage)
val kdf_usage_pred: l:DY.Labels.label -> u:usage -> u':usage -> usage_pred u -> usage_pred u' -> usage_pred (kdf_usage (l,u) u')
val dh_usage_pred: u:usage -> usage_pred u -> usage_pred (dh_key_usage u)
val default_usage_pred: u:usage -> usage_pred u

val pke_pred: up:usage_pred pke_key_usage -> nat -> bytes -> Type0
val ae_pred: up:usage_pred ae_key_usage -> nat -> bytes -> option bytes -> Type0
val mac_pred: up:usage_pred mac_key_usage -> nat -> bytes -> Type0
val sign_pred: up:usage_pred sig_key_usage -> nat ->  bytes -> Type0

val pke_pred_default: idx:nat -> t:bytes ->
  Lemma (pke_pred (default_usage_pred pke_key_usage) idx t)
	[SMTPat (pke_pred (default_usage_pred pke_key_usage) idx t)]

val ae_pred_default: idx:nat -> t:bytes -> to:option bytes ->
  Lemma (ae_pred (default_usage_pred ae_key_usage) idx t to)
	[SMTPat (ae_pred (default_usage_pred ae_key_usage) idx t to)]

val mac_pred_default: idx:nat -> t:bytes ->
  Lemma (mac_pred (default_usage_pred mac_key_usage) idx t)
	[SMTPat (mac_pred (default_usage_pred mac_key_usage) idx t)]

val sign_pred_default: idx:nat -> t:bytes ->
  Lemma (sign_pred (default_usage_pred sig_key_usage) idx t)
	[SMTPat (sign_pred (default_usage_pred sig_key_usage) idx t)]


val pke_key_usage_pred_lemma: idx:nat -> up:payload_pred -> t:bytes ->
  Lemma ((exists j. j <= idx /\ up j t) <==> pke_pred (pke_key_usage_pred up) idx t)
	[SMTPat (pke_pred (pke_key_usage_pred up) idx t)]

val pke_key_usage_pred_monotonic_lemma: idx:nat -> up:payload_pred -> t:bytes ->
  Lemma (pke_pred (pke_key_usage_pred up) idx t ==>
	      (exists j. j <= idx /\ up j t))
	[SMTPat (pke_pred (pke_key_usage_pred up) idx t)]

val ae_key_usage_pred_lemma: idx:nat -> up:payload_ad_pred -> t:bytes -> ad:option bytes ->
  Lemma ((exists j. j <= idx /\ up j t ad) <==> ae_pred (ae_key_usage_pred up) idx t ad)
	[SMTPat (ae_pred (ae_key_usage_pred up) idx t ad)]

val ae_key_usage_pred_monotonic_lemma: idx:nat -> up:payload_ad_pred -> t:bytes -> ad:option bytes ->
  Lemma (ae_pred (ae_key_usage_pred up) idx t ad ==>
	      (exists j. j <= idx /\ up j t ad))
	[SMTPat (ae_pred (ae_key_usage_pred up) idx t ad)]

val mac_key_usage_pred_lemma: idx:nat -> up:payload_pred -> t:bytes ->
  Lemma ((exists j. j <= idx /\ up j t) <==> mac_pred (mac_key_usage_pred up) idx t)
	[SMTPat (mac_pred (mac_key_usage_pred up) idx t)]

val mac_key_usage_pred_monotonic_lemma: idx:nat -> up:payload_pred -> t:bytes ->
  Lemma (mac_pred (mac_key_usage_pred up) idx t ==>
	      (exists j. j <= idx /\ up j t))
	[SMTPat (mac_pred (mac_key_usage_pred up) idx t)]

val sig_key_usage_pred_lemma: idx:nat -> up:payload_pred -> t:bytes ->
  Lemma ((exists j. j <= idx /\ up j t) <==> sign_pred (sig_key_usage_pred up) idx t)
	[SMTPat (sign_pred (sig_key_usage_pred up) idx t)]

val sig_key_usage_pred_monotonic_lemma: idx:nat -> up:payload_pred -> t:bytes ->
  Lemma (sign_pred (sig_key_usage_pred up) idx t ==>
	      (exists j. j <= idx /\ up j t))
	[SMTPat (sign_pred (sig_key_usage_pred up) idx t)]


/// Conversion Between Literals and Bytes
/// -------------------------------------
///

val literal_to_bytes: literal -> bytes
val bytes_to_literal: bytes -> result literal
val to_literal_lemma: s:literal ->
                 Lemma (ensures (bytes_to_literal (literal_to_bytes s) == Success s))
                       [SMTPat (bytes_to_literal (literal_to_bytes s))]
val literal_eq_fun_lemma: t1:bytes -> t2:bytes ->
		 Lemma (ensures (eq_bytes t1 t2 ==> bytes_to_literal t1 == bytes_to_literal t2))
		       [SMTPat (eq_bytes t1 t2); SMTPat (bytes_to_literal t1)]

let string_to_bytes s = literal_to_bytes (String s)
let bytes_to_string t =
  match bytes_to_literal t with
  | Success (String s) -> Success s
  | _ -> Error "literal is not a string"
let to_string_lemma (s:string) : 
    Lemma (ensures (bytes_to_string (string_to_bytes s) == Success s))
	  [SMTPat (bytes_to_string (string_to_bytes s))] = ()
val from_string_lemma: t:bytes ->
                 Lemma (ensures (match bytes_to_string t with
				 | Error _ -> True
				 | Success s -> string_to_bytes s == t))
                       [SMTPat (bytes_to_string t)]
val string_to_bytes_equal_lemma : a:string -> b:string -> Lemma (requires (eq_bytes (string_to_bytes a) (string_to_bytes b))) (ensures (a == b))
				 [SMTPat (eq_bytes (string_to_bytes a) (string_to_bytes b))]

val string_to_bytes_eqbytes_lemma : a:string -> b:bytes -> Lemma (requires (eq_bytes (string_to_bytes a) b)) (ensures (string_to_bytes a == b))
				 [SMTPat (eq_bytes (string_to_bytes a) b)]

val bytes_to_string_eqbytes_lemma : a:bytes -> b:bytes -> Lemma (requires (eq_bytes a b)) (ensures (bytes_to_string a == bytes_to_string b))
						    [SMTPat (eq_bytes a b)]
let nat_to_bytes s = literal_to_bytes (Nat s)
let bytes_to_nat t =
  match bytes_to_literal t with
  | Success (Nat n) -> Success n
  | _ -> Error "literal is not a nat"
let to_nat_lemma (s:nat) : Lemma (ensures (bytes_to_nat (nat_to_bytes s) == Success s))
                       [SMTPat (bytes_to_nat (nat_to_bytes s))] = ()

let bytestring_to_bytes s = literal_to_bytes (ByteSeq s)
let bytes_to_bytestring t =
  match bytes_to_literal t with
  | Success (ByteSeq s) -> Success s
  | _ -> Error "literal is not a bytesequence"


/// Manipulation of Bytes
/// ---------------------

/// Nonces
/// ~~~~~~
(** Nonces, can only be generated by gen *)
val gnonce: i:nat -> l:DY.Labels.label -> u:usage -> GTot bytes
val gnonce_eq_fun_lemma (i:nat) (l1:DY.Labels.label) (l2:DY.Labels.label) (u1:usage) (u2:usage) :
  Lemma ((l1 == l2 /\ u1 == u2) ==>
	 eq_bytes (gnonce i l1 u1) (gnonce i l2 u2))
  [SMTPat (eq_bytes (gnonce i l1 u1) (gnonce i l2 u2))]

val gnonce_inj_lemma (i1:nat) (i2:nat) (l1:DY.Labels.label) (l2:DY.Labels.label)
		     (u1:usage) (u2:usage) :
  Lemma (gnonce i1 l1 u1 == gnonce i2 l2 u2 ==> (i1 == i2 /\ l1 == l2 /\ u1 == u2))
  [SMTPat (gnonce i1 l1 u1); SMTPat (gnonce i2 l2 u2)]

val gnonce_eq_inj_lemma (i:nat) (l1:DY.Labels.label) (u1:usage) (t2:bytes) :
  Lemma (eq_bytes (gnonce i l1 u1) t2 ==>
	(exists l2 u2. l1 == l2 /\ u1 == u2 /\ t2 == gnonce i l2 u2))
  [SMTPat (eq_bytes (gnonce i l1 u1) t2)]

/// Concatenation and Splitting
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~
(** Concatenate bytes *)
val concat: bytes -> bytes -> bytes
val concat_eq_fun_lemma (t10 t11 t20 t21: bytes) :
  Lemma ((eq_bytes t10 t20 /\ eq_bytes t11 t21) <==> eq_bytes (concat t10 t11) (concat t20 t21))
  [SMTPat (eq_bytes (concat t10 t11) (concat t20 t21))]

(* Injectivity lemmas: they only work because our concat functions prefix with lengths *)
val concat_inj_lemma (t10 t11 t20 t21: bytes) :
  Lemma ((concat t10 t11 == concat t20 t21) ==> (t10 == t20 /\ t11 == t21))
val concat_eq_inj_lemma (t10 t11 t2: bytes) :
  Lemma (eq_bytes (concat t10 t11) t2 ==>
	(exists t20 t21. t2 == concat t20 t21 /\ eq_bytes t10 t20 /\ eq_bytes t11 t21))
val concat_eq_inj_forall_lemma (t10 t11: bytes) :
  Lemma (forall t2. eq_bytes (concat t10 t11) t2 ==>
	(exists t20 t21. t2 == concat t20 t21 /\ eq_bytes t10 t20 /\ eq_bytes t11 t21))

(** Split concatenated bytes *)
val split: bytes -> result (bytes * bytes)
val split_inj_lemma (t1 t2:bytes):
  Lemma ((split t1 == split t2 /\ Success? (split t1)) ==> t1 == t2)
val split_eq_inj_lemma (t1 t2:bytes):
  Lemma (eq_bytes t1 t2 ==> (match split t1 with | Success (t0, t1) -> (exists t21 t22. (split t2 == Success (t21, t22)) /\ eq_bytes t21 t0 /\ eq_bytes t22 t1)
						| Error _ -> Error? (split t2)))
val split_concat_lemma: a:bytes -> b:bytes ->
    Lemma (ensures (split (concat a b) == Success (a,b)))
          [SMTPat (split (concat a b))]
val concat_split_lemma (t:bytes):
    Lemma (match split t with
	 | Error _ -> True
	 | Success (t0,t1) -> t == concat t0 t1)
    [SMTPat (split t)]

val cannot_split_string_bytes: (a:bytes{exists s. a == string_to_bytes s}) -> Lemma (Error? (split a)) [SMTPat (split a)]

val concat_bytes_is_not_a_string_bytes: (a:bytes{exists b c. a == concat b c}) -> Lemma (Error? (bytes_to_string a)) [SMTPat (bytes_to_string a)]


/// Asymmetric Encryption and Decryption
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
(** Public key corresponding to a secret key *)
val pk: bytes -> bytes
val pk_eq_fun_lemma (t1 t2:bytes):
  Lemma (eq_bytes t1 t2 ==> eq_bytes (pk t1) (pk t2))
  [SMTPat (eq_bytes (pk t1) (pk t2))]
(* enable the following only if needed: it may not be true for some PK functions like Curve25519
val pk_inj_lemma (t1 t2:bytes) :
  Lemma (pk t1 == pk t2 ==> t1 == t2)
val pk_eq_inj_lemma (t1 t2:bytes):
  Lemma (eq_bytes (pk t1) t2 ==> (exists t2'. t2 == pk t2' /\ eq_bytes t1 t2'))
  [SMTPat (eq_bytes (pk t1) t2)]
*)

val is_pk: t:bytes -> bool

(** Public key encryption *)
val pke_enc: public_key:bytes -> msg:bytes -> bytes
val pke_enc_eq_fun_lemma (pub1 msg1 pub2 msg2: bytes):
  Lemma ((eq_bytes pub1 pub2 /\ eq_bytes msg1 msg2) ==> eq_bytes (pke_enc pub1 msg1) (pke_enc pub2 msg2))
  [SMTPat (eq_bytes (pke_enc pub1 msg1) (pke_enc pub2 msg2))]

(* Injectivity holds only when public keys are the same *)
val pke_enc_inj_lemma (pub msg1 msg2: bytes):
  Lemma (pke_enc pub msg1 == pke_enc pub msg2 ==> msg1 == msg2)
val pke_enc_eq_inj_lemma (pub1 pub2 msg1 msg2: bytes):
  Lemma ((eq_bytes (pke_enc pub1 msg1) (pke_enc pub2 msg2) /\ eq_bytes pub1 pub2) ==> eq_bytes msg1 msg2)
  [SMTPat (eq_bytes (pke_enc pub1 msg1) (pke_enc pub2 msg2))]

(** Public key decryption *)
val pke_dec: secret_key:bytes -> ciphertext:bytes -> result bytes

val pke_dec_enc_lemma: s:bytes -> b:bytes ->
    Lemma (ensures (pke_dec s (pke_enc (pk s) b) == Success b))
    [SMTPat (pke_dec s (pke_enc (pk s) b))]
val pke_enc_dec_lemma: s:bytes -> c:bytes ->
    Lemma (match pke_dec s c with
           | Error _ -> True
           | Success m -> (exists s'. c == pke_enc (pk s') m /\ eq_bytes s s'))


/// Authenticated Encryption and Decryption
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
val aead_enc: key:bytes -> msg:bytes -> associated_data:option bytes -> bytes

val aead_enc_eq_fun_lemma (key1 msg1 key2 msg2 ad1 ad2 : bytes):
    Lemma ((eq_bytes key1 key2 /\ eq_bytes msg1 msg2 /\ eq_bytes ad1 ad2) ==>
	   eq_bytes (aead_enc key1 msg1 (Some ad1)) (aead_enc key2 msg2 (Some ad2)))
    [SMTPat (eq_bytes (aead_enc key1 msg1 (Some ad1)) (aead_enc key2 msg2 (Some ad2)))]
val ae_enc_eq_fun_lemma (key1 msg1 key2 msg2 : bytes):
    Lemma ((eq_bytes key1 key2 /\ eq_bytes msg1 msg2) ==>
	   eq_bytes (aead_enc key1 msg1 None) (aead_enc key2 msg2 None))
    [SMTPat (eq_bytes (aead_enc key1 msg1 None) (aead_enc key2 msg2 None))]

(* Injectivity holds only when AEAD keys are the same *)
val aead_enc_inj_lemma (key msg1 msg2: bytes) (ad1 ad2: option bytes):
  Lemma (aead_enc key msg1 ad1 == aead_enc key msg2 ad2 ==> (msg1 == msg2 /\ ad1 == ad2))
val ae_enc_eq_inj_lemma (key1 key2 msg1 msg2: bytes):
  Lemma ((eq_bytes (aead_enc key1 msg1 None) (aead_enc key2 msg2 None) /\ eq_bytes key1 key2)==> eq_bytes msg1 msg2)
  [SMTPat (eq_bytes (aead_enc key1 msg1 None) (aead_enc key2 msg2 None))]
val aead_enc_eq_inj_lemma (key1 key2 msg1 msg2 ad1 ad2: bytes):
  Lemma ((eq_bytes (aead_enc key1 msg1 (Some ad1)) (aead_enc key2 msg2 (Some ad2)) /\ eq_bytes key1 key2)
         ==> (eq_bytes msg1 msg2 /\ eq_bytes ad1 ad2))
  [SMTPat (eq_bytes (aead_enc key1 msg1 (Some ad1)) (aead_enc key2 msg2 (Some ad2)))]

val aead_dec: key:bytes -> ciphertext:bytes -> associated_data:option bytes -> result bytes
val aead_dec_enc_lemma: k:bytes -> p:bytes -> ad:option bytes ->
                 Lemma (ensures (aead_dec k (aead_enc k p ad) ad == Success p))
                       [SMTPat (aead_dec k (aead_enc k p ad))]
val ae_enc_dec_lemma: s:bytes -> c:bytes ->
                 Lemma (
                   match aead_dec s c None with
                   | Error _ -> True
                   | Success m -> (exists s'. c == aead_enc s' m None /\ eq_bytes s s'))
val aead_enc_dec_lemma: s:bytes -> c:bytes -> ad:bytes ->
                 Lemma (ensures (
                 match aead_dec s c (Some ad) with
                 | Error _ -> True
                 | Success m -> (exists s' ad'. c == aead_enc s' m (Some ad') /\ eq_bytes s s' /\ eq_bytes ad ad')))

/// Public Key Signatures
/// ~~~~~~~~~~~~~~~~~~~~~

(** Convert a signing key into a verification key *)
val vk: secret_key:bytes -> public_key:bytes
val vk_eq_fun_lemma (t1 t2:bytes):
  Lemma (eq_bytes t1 t2 ==> eq_bytes (vk t1) (vk t2))
  [SMTPat (eq_bytes (vk t1) (vk t2))]
(* enable the following only if needed: it may not be true for some PK functions like Curve25519
val vk_inj_lemma (t1 t2:bytes) :
  Lemma (vk t1 == vk t2 ==> t1 == t2)
val vk_eq_inj_lemma (t1 t2:bytes):
  Lemma (eq_bytes (vk t1) t2 ==> (exists t2'. t2 == vk t2' /\ eq_bytes t1 t2'))
  [SMTPat (eq_bytes (vk t1) t2)]
*)

(** Creating a tag for msg using the key secret_key.*)
val sign: secret_key:bytes -> msg:bytes -> tag:bytes

val sign_eq_fun_lemma (priv1 msg1 priv2 msg2: bytes):
  Lemma ((eq_bytes priv1 priv2 /\ eq_bytes msg1 msg2) ==>
	  eq_bytes (sign priv1 msg1) (sign priv2 msg2))
  [SMTPat (eq_bytes (sign priv1 msg1) (sign priv2 msg2))]

(* Disabling injectivity: allowing all DSKS-style attacks *)
(*
val sign_inj_lemma (priv msg1 msg2: bytes):
  Lemma (sign priv msg1 == sign priv msg2 ==> msg1 == msg2)
*)

(** Verification of signatures *)
val verify: public_key:bytes -> msg:bytes -> tag:bytes -> bool
val verify_eq_fun_lemma (pub1 pub2 msg1 msg2: bytes) (tag:bytes):
  Lemma ((eq_bytes pub1 pub2 /\ eq_bytes msg1 msg2) ==>
	 verify pub1 msg1 tag == verify pub2 msg2 tag)
  [SMTPat (verify pub1 msg1 tag); SMTPat (verify pub2 msg2 tag)]
val verify_sign_lemma: s:bytes -> b:bytes ->
  Lemma (ensures (verify (pk s) b (sign s b) == true))
  [SMTPat (verify (pk s) b (sign s b))]

(* Disable sign_verify_lemma, because it does not hold with DEO attacks *)
//val sign_verify_lemma: p:bytes -> msg:bytes -> tag:bytes ->
//  Lemma (verify p msg tag ==>
//	 (exists s' msg'. tag == sign s' msg' /\ eq_bytes p (pk s') /\ eq_bytes msg msg'))

(* CEOgen - see Seems Legit paper *)
val ceo_gen: sig:bytes -> bytes
val ceo_gen_verify_lemma: m:bytes -> sk:bytes ->
  Lemma (ensures (verify (pk (ceo_gen (sign sk m))) m (sign sk m) == true))

(* DEOgen - see Seems Legit paper *)
val deo_gen: msg:bytes -> sig:bytes -> bytes
val deo_gen_verify_lemma: m1:bytes -> m2:bytes -> sk:bytes ->
  Lemma (ensures (verify (pk (deo_gen m2 (sign sk m1))) m2 (sign sk m1) == true))

/// Key Derivation
/// ~~~~~~~~~~~~~~

val kdf: key:bytes -> context:bytes -> extract:bool -> bytes
val kdf_eq_fun_lemma (key1 key2 context1 context2: bytes) (extract:bool):
  Lemma ((eq_bytes key1 key2 /\ eq_bytes context1 context2) ==>
	 eq_bytes (kdf key1 context1 extract) (kdf key2 context2 extract))
	 [SMTPat (eq_bytes (kdf key1 context1 extract) (kdf key2 context2 extract))]

(* Injectivity for KDF *)
val kdf_inj_lemma (key1 key2 context1 context2: bytes) (extract:bool):
  Lemma (kdf key1 context1 extract == kdf key2 context2 extract ==>
	 (eq_bytes key1 key2 /\ eq_bytes context1 context2))
	[SMTPat (kdf key1 context1 extract); SMTPat (kdf key2 context2 extract)]
(* A strong injectivity lemma for KDF, may need to be weakened *)
val kdf_eq_inj_lemma (key1 context1 t2: bytes) (extract:bool):
  Lemma (eq_bytes (kdf key1 context1 extract) t2 ==>
	 (exists key2 context2. t2 == kdf key2 context2 extract /\
			   eq_bytes key1 key2 /\ eq_bytes context1 context2))

/// Message Authentication Codes
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(** Creating a tag for msg using the key secret_key.*)
val mac: shared_secret_key:bytes -> msg:bytes -> tag:bytes
val mac_eq_fun_lemma (k1 k2 m1 m2:bytes) :
  Lemma ((eq_bytes k1 k2 /\ eq_bytes m1 m2) ==>
	 eq_bytes (mac k1 m1) (mac k2 m2))
(* Injectivity for MACs *)
val mac_inj_lemma (key1 key2 msg1 msg2: bytes):
  Lemma (mac key1 msg1 == mac key2 msg2 ==>
	 (eq_bytes key1 key2 /\ eq_bytes msg1 msg2))
  [SMTPat (mac key1 msg1); SMTPat (mac key2 msg2)]
(* A strong injectivity lemma for KDF, may need to be weakened *)
val mac_eq_inj_lemma (key1 msg1 t2: bytes):
  Lemma (eq_bytes (mac key1 msg1) t2 ==>
	 (exists key2 msg2. t2 == mac key2 msg2 /\
		       eq_bytes key1 key2 /\ eq_bytes msg1 msg2))
  [SMTPat (eq_bytes (mac key1 msg1) t2)]

(** Verifying authenticity of message: Returns True iff message and tag are not tampered with. Verified using the shared secret key.*)
val verify_mac: shared_secret_key:bytes -> msg:bytes -> tag:bytes -> bool
val verify_mac_lemma: k:bytes -> m:bytes -> tag:bytes ->
  Lemma (ensures (verify_mac k m tag == eq_bytes (mac k m) tag))
  [SMTPat (verify_mac k m tag)]


/// Hashing
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(** Hash bytes *)
val hash: msg:bytes -> bytes

val hash_eq_fun_lemma (msg1 msg2: bytes) :
  Lemma (eq_bytes msg1 msg2 ==> eq_bytes (hash msg1) (hash msg2))
  [SMTPat (eq_bytes (hash msg1) (hash msg2))]
val hash_inj_lemma (msg1 msg2: bytes) :
  Lemma (hash msg1 == hash msg2 ==> msg1 == msg2)
val hash_eq_inj_lemma (msg1 msg2: bytes) :
  Lemma (eq_bytes (hash msg1) (hash msg2) ==> eq_bytes msg1 msg2)
  [SMTPat (eq_bytes (hash msg1) (hash msg2))]

/// Diffie-Hellman Shared Secret
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

val dh: key:bytes -> publickey:bytes -> bytes
val dh_eq_fun_lemma (s1 s2 p1 p2:bytes) :
  Lemma ((eq_bytes s1 s2 /\ eq_bytes p1 p2) ==> eq_bytes (dh s1 p1) (dh s2 p2))
  [SMTPat (eq_bytes (dh s1 p1) (dh s2 p2))]

val dh_shared_secret_lemma: x:bytes -> y:bytes ->
  Lemma (eq_bytes (dh x (pk y)) (dh y (pk x)))
  [SMTPat (eq_bytes (dh x (pk y)) (dh y (pk x)))]

(* Equality of various DH bytes *)
val dh_shared_secret_eq_bytes_lemma: unit ->
  Lemma (forall x y x' y'. eq_bytes y' (pk y) /\ eq_bytes x' (pk x) ==>
		      (eq_bytes (dh x (pk y)) (dh y (pk x)) /\ eq_bytes (dh x y') (dh y x') /\
		      eq_bytes (dh x (pk y)) (dh x y') /\ eq_bytes (dh x y') (dh y (pk x))))


/// More properties about bytes
/// ---------------------------
///
/// Used to prove termination of helper functions.

(** Returns the depth of bytes. Note that it returns a ghost value, this function
is intended to be used to prove termination. Also note the according lemmas. *)
val bytes_depth: bytes -> GTot nat

val bytes_depth_decreases_when_splitting:
  (t:bytes) ->
  Lemma (
    match split t with
    | Error _ -> True
    | Success (t1, t2) ->
        bytes_depth t1 < bytes_depth t /\
        bytes_depth t2 < bytes_depth t
  )
  [SMTPat (bytes_depth t)]


val pk_injective_lemma:
 t1:bytes ->
 t2:bytes ->
 Lemma
 (requires pk t1 == pk t2)
 (ensures t1 == t2)
 [SMTPat (pk t1 == pk t2)]

val pk_injective_lemma_forall:
 t:bytes ->
 Lemma
 (ensures forall t'. pk t' == pk t ==> t' == t)


val eq_bytes_concat_split_lemma:
 t1: bytes ->
 t2: bytes ->
 t: bytes ->
 Lemma
 (requires eq_bytes t (concat t1 t2))
 (ensures (
   match split t with
   | Success (t1', t2') -> eq_bytes t1' t1 /\ eq_bytes t2' t2
   | _ -> False
 ))

