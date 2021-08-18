/// Labeled.SecrecyLemmas
/// ======================
module Labeled.SecrecyLemmas
open DY.Principals
open DY.Labels
open DY.Entry
open DY.Monad
open DY.Trace
open DY.Crypto
open Labeled.Crypto
open Application.Predicates
open Labeled.ApplicationAPI
open DY.AttackerAPI


/// Lemmas to prove application properties
/// --------------------------------------

(* Security Properties: Attacker cannot break trace validity and cannot learn secrets without compromising their readers *)

/// Attacker cannot break (general) trace validity
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// See also :ref:`the definition of valid_trace<general_valid_trace>`.

(** Whatever the attacker does, he cannot break (general) trace validity. *)
val attacker_preserves_validity: t0:trace -> t1:trace ->
  Lemma ((valid_trace t0 /\ attacker_modifies_trace t0 t1) ==> valid_trace t1)
  [SMTPat (attacker_modifies_trace t0 t1)]

/// Secrets do not leak
/// ~~~~~~~~~~~~~~~~~~~
///
/// Terms labeled as being secrets between a certain set of principals are not leaked to any
/// principals outside that set or to the attacker; except if at least one principal in the set is
/// corrupted.

(** The attacker (or any principal outside [l]) will never know [t], except if one
of the principals in [l] is corrupted. *)
val secrecy_lemma: t:bytes -> intended_readers:secret_intendees -> DYL unit (requires (fun t0 -> is_labeled_at (trace_len t0) t (readable_by intended_readers)))
          (ensures (fun t0 _ t1 -> t0 == t1 /\ (is_unknown_to_attacker_at (trace_len t0) t \/ contains_corrupt_principal (corrupt_at (trace_len t0)) intended_readers)))

val conditional_secrecy_lemma: t:bytes -> intended_readers:secret_intendees -> DYL unit (requires (fun t0 -> is_labeled_at (trace_len t0) t (readable_by intended_readers) \/ contains_corrupt_principal (corrupt_at (trace_len t0)) intended_readers))
          (ensures (fun t0 _ t1 -> t0 == t1 /\ (is_unknown_to_attacker_at (trace_len t0) t \/ contains_corrupt_principal (corrupt_at (trace_len t0)) intended_readers)))

val secrecy_label_lemma: t:bytes -> l:versionid -> DYL unit (requires (fun t0 -> is_labeled_at (trace_len t0) t (can_read [l]))) (ensures (fun t0 _ t1 -> t0 == t1 /\ (is_unknown_to_attacker_at (trace_len t0) t \/ corrupt_at (trace_len t0) l)))

val secrecy_join_label_lemma: t:bytes -> DYL unit (requires (fun t0 -> True))
			      (ensures (fun t0 _ t1 -> t0 == t1 /\ (forall l l'. is_labeled_at (trace_len t0) t (join (can_read [l]) (can_read [l'])) ==> (
				(is_unknown_to_attacker_at (trace_len t0) t \/ corrupt_at (trace_len t0) l \/ corrupt_at (trace_len t0) l')))))
