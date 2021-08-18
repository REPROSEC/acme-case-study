/// DY.Monad (implementation)
/// ==========================
module DY.Monad

(* This module is adapted from Aseem Rastogi's example in
   FStar/examples/layeredeffects/MSeqExn.fst *)

open Helpers
open DY.Entry
module Seq = FStar.Seq
module W = FStar.Monotonic.Witnessed

/// Some actions

inline_for_extraction
let get ()
: DY trace
  (fun _ -> True)
  (fun s0 r s1 -> r == Success s0 /\ s0 == s1)
= DY?.reflect (fun s0 -> Success s0, s0)

let put (s:trace)
: DY unit
  (fun s0 -> grows s0 s)
  (fun _ r s1 ->
    r == Success () /\
    s1 == s)
= DY?.reflect (fun _ -> Success (), s)

inline_for_extraction
let error (#a:Type) (e:string)
: DY a
  (fun _ -> True)
  (fun s0 r s1 -> r == Error e /\ s0 == s1)
= DY?.reflect (fun s0 -> Error e, s0)

inline_for_extraction
let current_trace_len ()
: DY nat
  (fun _ -> True)
  (fun s0 r s1 ->
    r == Success (trace_len s0) /\
    s0 == s1)
= let s0 = get () in
  Seq.length s0

inline_for_extraction
let write_at_end (e:entry_t)
: DY unit
  (fun s0 -> trace_inv0 (Seq.snoc s0 e))
  (fun s0 r s1 ->
    r == Success () /\
    s1 == Seq.snoc s0 e)
= let s0 = get () in
  let s1 = Seq.snoc s0 e in
  assert (forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i == Seq.index s1 i);
  put s1

inline_for_extraction
let index (i:nat)
: DY entry_t
  (fun s0 -> i < Seq.length s0)
  (fun s0 r s1 ->
    r == Success (Seq.index s0 i) /\
    s0 == s1)
= let s0 = get () in
  Seq.index s0 i

/// "Monotonic" Stable Predicates over the Trace
/// See Ahman et al.'s POPL 2018 paper "Recalling a Witness:
/// Foundations and Applications of Monotonic State".

let witnessed p = W.witnessed grows p

// The following two cannot be implemented/proven inside F*
// (to see why they are sound, see "recalling a witness" paper)

(* An admitted definition for witness *)
let witness p = assume(witnessed p)

(* An admitted definition for recall. *)
let recall p = let t = get() in assume(witnessed p ==> p t)


let witnessed_constant (p:Type0)
: Lemma (witnessed (fun _ -> p) <==> p)
= W.lemma_witnessed_constant grows p

let witnessed_nested (p:trace_pred)
: Lemma (witnessed (fun s -> witnessed p) <==> witnessed p)
= assert_norm (witnessed (fun _ -> witnessed p) ==
               W.witnessed grows (fun _ -> W.witnessed grows p));
  assert_norm (witnessed p == W.witnessed grows p);
  W.lemma_witnessed_nested grows p

let witnessed_and (p q:trace_pred)
: Lemma (witnessed (fun s -> p s /\ q s) <==> (witnessed p /\ witnessed q))
= W.lemma_witnessed_and grows p q

let witnessed_or (p q:trace_pred)
: Lemma ((witnessed p \/ witnessed q) ==> witnessed (fun s -> p s \/ q s))
= W.lemma_witnessed_or grows p q

let witnessed_impl (p q:trace_pred)
: Lemma ((witnessed (fun s -> p s ==> q s) /\ witnessed p) ==> witnessed q)
= W.lemma_witnessed_impl grows p q

let witnessed_forall (#t:Type) (p:(t -> trace_pred))
: Lemma ((witnessed (fun s -> forall x. p x s)) <==> (forall x. witnessed (p x)))
= W.lemma_witnessed_forall grows p

let witnessed_exists (#t:Type) (p:(t -> trace_pred))
: Lemma ((exists x. witnessed (p x)) ==> witnessed (fun s -> exists x. p x s))
= W.lemma_witnessed_exists grows p


let massert p = assert p
let massume p = assume p
let madmit (#a:Type) () = admit ()

/// Trace predicates

val entry_at_pred_injective (n:nat) (e1:entry_t) (e2:entry_t) :
  Lemma (forall t. (entry_at_pred n e1 t /\ entry_at_pred n e2 t) ==> e1 == e2)
let entry_at_pred_injective n e1 e2 = ()

(** Property of [entry_at]: If [entry_at i] is true for two entries (with the same [i]), then these
two entries are equal. *)
let entry_at_injective i e1 e2 =
  let p : trace_pred = fun t -> entry_at_pred i e1 t /\ entry_at_pred i e2 t in
  let q : trace_pred = fun t -> e1 == e2 in
  witnessed_and (entry_at_pred i e1) (entry_at_pred i e2);
  assert (witnessed p);
  entry_at_pred_injective i e1 e2;
  W.lemma_witnessed_weakening grows p q;
  assert (witnessed (fun t -> e1 == e2));
  witnessed_constant (e1 == e2)


let entry_at_before_now idx et = 
  assert(witnessed (entry_at_pred idx et));
  let t0 = get() in
  recall (entry_at_pred idx et);
  assert(entry_at_pred idx et t0)
