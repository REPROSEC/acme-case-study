/// DY.AttackerAPI
/// ==============
/// 

module DY.AttackerAPI

(* A Dolev-Yao Model Using Monotonic State *)

open Helpers
open DY.Principals
module C = DY.Crypto
module P = DY.Principals
module L = DY.Labels
open DY.Entry
open DY.Monad
open DY.Trace

let bytes = C.bytes

/// .. _dy_attacker_can_derive:
/// 
/// Attacker's knowledge
/// --------------------
///
/// The knowledge of the attacker up to position i in the trace is defined as follows:

(**
Predicate on attacker knowledge: Returns true iff the attacker can derive
a bytes in a given number of steps after the first i entries in the trace.
*)
let query_result (idx_state:nat) (p:P.principal) (si:nat) (sv:nat) (tag:string) (res:bytes) : Type0 =
  (exists ver_vec state.
    is_set_state_at idx_state p ver_vec state /\
    Seq.length ver_vec = Seq.length state /\
    Seq.length ver_vec > si /\
    Seq.index ver_vec si = sv /\
    is_some (lookup state.[si] tag) res)

let rec attacker_can_derive (i:nat) (steps:nat) (t:bytes):
                         Tot Type0 (decreases steps) =
  if steps = 0 then
    (* Attacker can read bytes that were published (i.e., messages sent by someone in the past) *)
      ((i > 0 /\ is_published_before (i-1) t) \/
       (i > 0 /\ is_auth_published_before (i-1) t) \/
    (* Attacker can read the state of corrupted principals *)
      (exists idx_state sess_idx sess_ver corrupted_principal str.
        idx_state < i /\
	query_result idx_state corrupted_principal sess_idx sess_ver str t /\
        is_corrupted_before i corrupted_principal sess_idx sess_ver) \/
    (* Attacker can call from_pub_bytes, i.e., can derive constants *)
      (exists (s:C.literal). t == C.literal_to_bytes s))
  else (
      // Just reduce steps by one
      (attacker_can_derive i (steps - 1) t) \/
      // Attacker can concatenate bytes
      (exists (t1 t2:bytes).
        t == C.concat t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Attacker can construct public key from private key
      (exists (priv_key:bytes).
        t == C.pk priv_key /\
        attacker_can_derive i (steps - 1) priv_key) \/
      // Asymmetric encryption
      (exists (t1 t2:bytes).
        t == C.pke_enc t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Symmetric encryption
      (exists (t1 t2:bytes).
        t == C.aead_enc t1 t2 None /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Create signatures
      (exists (t1 t2:bytes).
        t == C.sign t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Create CEOgen
      (exists (t1:bytes).
        t == C.ceo_gen t1 /\
        attacker_can_derive i (steps - 1) t1) \/
      // Create DEOgen
      (exists (t1 t2:bytes).
        t == C.deo_gen t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Create macs
      (exists (t1 t2:bytes).
        t == C.mac t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Create hashes
      (exists t1.
        t == C.hash t1 /\
        attacker_can_derive i (steps - 1) t1) \/
      // Attacker can derive new keys from a key and a context
      (exists (t1 t2:bytes) (b:bool).
        t == C.kdf t1 t2 b /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Split up concatenated bytes
      (exists (t1 t2:bytes).
        is_succ2 (C.split t1) t t2 /\
        attacker_can_derive i (steps - 1) t1) \/
      (exists (t1 t2:bytes).
         is_succ2 (C.split t1) t2 t /\
        attacker_can_derive i (steps - 1) t1) \/
      // Asymmetric decryption
      (exists (t1 t2:bytes).
        is_succ (C.pke_dec t1 t2) t /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Symmetric decryption
      (exists (t1 t2:bytes).
        is_succ (C.aead_dec t1 t2 None) t /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // DH shared secret
      (exists (t1 t2:bytes).
        t == (C.dh t1 t2) /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2))

/// Properties of the Attacker Knowledge
/// ------------------------------------


/// If a specific version of a session of a principal is corrupted, then the attacker can derive the state value immediately, i.e., in zero steps.

(**
If the versions ver_vec of the sessions of the principal were set to state_at_j, and if this version of the session is corrupted,
then the attacker can derive the content of the version immediately, i.e., in zero steps.
*)
val attacker_can_query_compromised_state:
    idx_state:nat -> idx_corrupt:nat -> idx_query:nat ->
    principal:P.principal -> sess_index:nat -> sess_ver:nat ->
    tag:string -> res:bytes ->
  Lemma
    (requires
      ( idx_state < idx_query /\
	idx_corrupt < idx_query /\
	query_result idx_state principal sess_index sess_ver tag res /\ //at idx_state, the principals state was set to state
        is_corrupted_before idx_corrupt principal sess_index sess_ver
      )
    )
    (ensures (attacker_can_derive idx_query 0 res))

/// If the attacker can derive bytes in some steps, he can also derive it in more steps.

(**
If the attacker can derive bytes t in position i of the trace with steps1 many steps,
then he can also derive t with a higher number of steps steps2.
*)
val attacker_can_derive_in_more_steps: i:nat -> steps1:nat -> steps2:nat ->
  Lemma (requires (steps1 <= steps2))
        (ensures (forall t. attacker_can_derive i steps1 t  ==> attacker_can_derive i steps2 t))

/// If the attacker can derive bytes in some steps, he can also derive it in more steps.

(**
If the attacker can derive bytes t in position i of the trace,
he can also derive t at a higher position in the trace (with the same number of steps).
*)
val attacker_can_derive_later: i:nat -> steps:nat -> j:nat ->
  Lemma (requires (i <= j))
        (ensures (forall t. attacker_can_derive i steps t ==> attacker_can_derive j steps t))
        (decreases steps)

/// Predicates
/// ----------

(**
The attacker knows bytes t at the position i in the trace if
it is derivable by the attacker (for some number of steps).
*)
let attacker_knows_at (i:nat) (t:bytes) =
  exists (steps:nat). attacker_can_derive i steps t

(**
bytes t is a secret at the position i in the trace if
it is not known to the attacker.
*)
let is_unknown_to_attacker_at (i:nat) (t:bytes) =
  ~ (attacker_knows_at i t)

val attacker_knows_later: i:nat -> j:nat ->
  Lemma (requires (i <= j))
        (ensures (forall a. attacker_knows_at i a ==> attacker_knows_at j a))


/// API for Attacker
/// ----------------
///
/// These are the functions that are **at least** available to the attacker,
/// i.e., if the typecheck is successfull, we know that the attacker can perform these actions.
///
/// However, this API does not define the attacker that we are talking about in the proof, i.e., we do not show that the protocol is secure wrt. all attackers having access to exactly this API.

/// Attacker API: Manipulation of Bytes:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
  
(**
A pub_bytes is bytes that is known to the attacker (in position i of the trace).
*)
let pub_bytes (i:nat) = t:C.bytes{attacker_knows_at i t}

let pub_bytes_later (i:nat) (j:nat{i<=j}) (t:pub_bytes i) : pub_bytes j =
    attacker_knows_later i j;
    t

val literal_to_pub_bytes: l:C.literal -> t:pub_bytes 0
val from_literal_lemma: l:C.literal ->
  Lemma (literal_to_pub_bytes l == C.literal_to_bytes l)

val bytes_to_string: #i:nat -> t:pub_bytes i ->
		    Err string (ensures (fun r -> r == C.bytes_to_string t))


val concat: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i -> t3:pub_bytes i
val concat_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i ->
  Lemma (concat t1 t2 == C.concat t1 t2)

val split: #i:nat -> t:pub_bytes i -> Err (pub_bytes i * pub_bytes i)
	   (ensures (fun r ->
	     match r with
             | Success (a,b) -> C.split t == Success (a,b)
             | Error x -> C.split t == Error x))


val pk: #i:nat -> s:pub_bytes i -> p:pub_bytes i
val pk_lemma: #i:nat -> s:pub_bytes i -> Lemma (pk s == C.pk s)

val pke_enc: #i:nat -> pub_bytes i -> pub_bytes i -> pub_bytes i
val pke_enc_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i ->
  Lemma (pke_enc t1 t2 == C.pke_enc t1 t2)

val pke_dec: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i -> Err (pub_bytes i)
	     (ensures (fun r ->
	       match r with
               | Success p -> C.pke_dec t1 t2 == Success p
               | Error s -> C.pke_dec t1 t2 == Error s))

val ae_enc: #i:nat -> pub_bytes i -> pub_bytes i -> pub_bytes i
val ae_enc_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i ->
  Lemma (ae_enc t1 t2 == C.aead_enc t1 t2 None)

val ae_dec: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i -> Err (pub_bytes i)
	     (ensures (fun r ->
	       match r with
               | Success p -> C.aead_dec t1 t2 None == Success p
               | Error s -> C.aead_dec t1 t2 None == Error s))

val sign: #i:nat -> pub_bytes i -> pub_bytes i -> pub_bytes i
val sign_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i ->
  Lemma (sign t1 t2 == C.sign t1 t2)
val verify: #i:nat -> pub_bytes i -> pub_bytes i -> pub_bytes i -> bool
val verify_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i -> t3:pub_bytes i ->
  Lemma (verify t1 t2 t3 == C.verify t1 t2 t3)
val ceo_gen: #i:nat -> sig:pub_bytes i -> pub_bytes i
val ceo_gen_lemma: #i:nat -> t1:pub_bytes i -> 
  Lemma (ensures (ceo_gen t1 == C.ceo_gen t1))
val deo_gen: #i:nat -> msg:pub_bytes i -> sig:pub_bytes i -> pub_bytes i
val deo_gen_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i -> 
  Lemma (ensures (deo_gen t1 t2 == C.deo_gen t1 t2))

val mac: #i:nat -> pub_bytes i -> pub_bytes i -> pub_bytes i
val mac_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i ->
  Lemma (mac t1 t2 == C.mac t1 t2)
val verify_mac: #i:nat -> pub_bytes i -> pub_bytes i -> pub_bytes i -> bool
val verify_mac_lemma: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i -> t3:pub_bytes i ->
  Lemma (verify_mac t1 t2 t3 == C.verify_mac t1 t2 t3)

val hash: #i:nat -> pub_bytes i -> pub_bytes i
val hash_lemma: #i:nat -> t1:pub_bytes i ->
  Lemma (hash t1 == C.hash t1)

val dh: #i:nat -> t1:pub_bytes i -> t2:pub_bytes i -> pub_bytes i
val dh_lemma: #i:nat ->  t1:pub_bytes i -> t2:pub_bytes i ->
  Lemma (dh t1 t2 == C.dh t1 t2)

/// Attacker API: Manipulation of Trace:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///

val current_trace_len: unit -> DY nat
                       (requires (fun h -> True))
                       (ensures (fun t0 r t1 -> t0 == t1 /\ r == Success (trace_len t0)))

// used for abbreviating the postconditions below
let attacker_modifies_trace (t0:trace) (t1:trace) =
  (((exists u n. trace_len t1 = trace_len t0 + 2 /\
           is_nonce_generated_at (trace_len t0) n L.public u (C.default_usage_pred u) /\
           C.is_pub_usage u /\
           is_published_at (trace_len t0 + 1) n) \/
    (exists i a. trace_len t1 = trace_len t0 + 1 /\
            i <= trace_len t0 /\
            attacker_knows_at i a /\
            is_published_at (trace_len t0) a) \/
    (exists i s r a. trace_len t1 = trace_len t0 + 1 /\
            i <= trace_len t0 /\
            attacker_knows_at i a /\
	    is_principal_corrupted_before (trace_len t0) s /\
	    is_authenticated_message_sent_at (trace_len t0) s r a /\
            is_auth_published_at (trace_len t0) a) \/
    (exists p s v.   trace_len t1 = trace_len t0 + 1 /\
           is_corrupted_at (trace_len t0) p s v)))


val pub_gen: u:C.usage -> DY (i:nat & pub_bytes i)
                      (requires (fun t0 -> C.is_pub_usage u))
                      (ensures (fun t0 s t1 ->
			match s with
			| Error _ -> True
			| Success (| i, n |) ->
                          attacker_modifies_trace t0 t1 /\
                          i = trace_len t1 /\
                          trace_len t1 = trace_len t0 + 2 /\
                          is_nonce_generated_at (trace_len t0) n L.public u (Crypto.default_usage_pred u) /\
                          is_published_at (trace_len t0 + 1) n))

val send: #i:nat -> p1:P.principal -> p2:P.principal -> a:pub_bytes i -> DY nat
                      (requires (fun t0 -> i <= trace_len t0))
                      (ensures (fun t0 n t1 ->
			match n with
			| Error _ -> t0 == t1
			| Success n ->
                          attacker_modifies_trace t0 t1 /\
                          trace_len t1 = trace_len t0 + 1 /\
			  n = trace_len t0 /\
                          is_published_at (trace_len t0) a))

val receive_i: i:nat -> p2:P.principal -> DY (j:nat & pub_bytes j)
                      (requires (fun t0 -> i < trace_len t0))
                      (ensures (fun t0 t t1 ->
                        t0 == t1 /\
			(match t with
			 | Error _ -> True
			 | Success (|j,m|) ->
			   trace_len t0 = j /\ is_published_at i m /\
                           (exists p1 p2. is_message_sent_at i p1 p2 m))))

val compromise: p:principal -> s:nat -> v:nat -> DY nat
                (requires (fun t0 -> True))
                (ensures (fun t0 r t1 ->
			match r with
			| Error _ -> t0 == t1
			| Success r ->
				  r == trace_len t0 /\
				  attacker_modifies_trace t0 t1 /\
				  trace_len t1 = trace_len t0 + 1 /\
				  is_corrupted_at (trace_len t0) p s v))
val query_state_i: idx_state:nat -> idx_corrupt:nat -> idx_query:nat ->
		   p:P.principal -> si:nat -> sv:nat ->
		   tag:string -> DY (pub_bytes idx_query)
                  (requires (fun t0 -> idx_state < idx_query /\
				    idx_corrupt < idx_query /\
				    idx_query <= trace_len t0 /\
				    is_corrupted_at idx_corrupt p si sv))
                  (ensures (fun t0 r t1 ->
                        t0 == t1 /\
                        (match r with
                         | Error _ -> True
                         | Success x -> query_result idx_state p si sv tag x)))


(**
   Returns (optionally) the length of the trace, a message, and a principal.
*)
val authenticated_receive_i: i:nat -> p2:P.principal ->
    			     DY (j:nat & pub_bytes j & principal)
                      (requires (fun t0 -> i < trace_len t0))
                      (ensures (fun t0 t t1 ->
                        t0 == t1 /\
                        (match t with
                         | Error _ -> True
                         | Success (| j, m, sender |) ->
			   	   trace_len t0 = j /\
				   is_auth_published_at i m /\
                                   (exists recv. is_authenticated_message_sent_at i sender recv m))))

(**
  The model only considers corrupted versions, but not corrupted principals.
  For now, we assume that the attacker can send on behalf of a principal if some version of the principal is corrupted.
*)
val authenticated_send: #i:nat -> p1:P.principal -> p2:P.principal -> a:pub_bytes i -> DY nat
                      (requires (fun t0 ->
		      		i <= trace_len t0 /\
				is_principal_corrupted_before (trace_len t0) p1))
                      (ensures (fun t0 b t1 ->
			match b with
			| Error _ -> t0 == t1
			| Success n ->
			  attacker_modifies_trace t0 t1 /\
                          trace_len t1 = trace_len t0 + 1 /\
			  n = trace_len t0 /\
                          is_auth_published_at n a /\
                          is_authenticated_message_sent_at n p1 p2 a))

