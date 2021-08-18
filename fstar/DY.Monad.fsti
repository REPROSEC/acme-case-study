/// DY.Monad
/// ========
module DY.Monad

(* This module is adapted from Aseem Rastogi's example in
   FStar/examples/layeredeffects/MSeqExn.fst *)

open Helpers
open DY.Entry
module Seq = FStar.Seq
module W = FStar.Monotonic.Witnessed

(* Generic trace invariant, currently empty (i.e., always true) - if this is changed, also change
the documentation in the fsti file. Meant as a place-holder for more complex invariants than the
is_publishable condition *)
let trace_inv0 (s:Seq.seq entry_t) = True

/// Define the global execution trace as a sequence of entries

type trace = s:Seq.seq entry_t{trace_inv0 s}

(** Length of the trace in the given global state. *)
inline_for_extraction // Ignore this - it's only about the extraction to OCaml
let trace_len (t0:trace) : GTot nat = Seq.length t0


/// The state grows monotonically
(** Predicate on valid transitions on the trace (note that this is only enforced later) *)
let grows : Preorder.preorder trace =
  fun (s1:trace) (s2:trace) ->
  Seq.length s1 <= Seq.length s2 /\
  (forall (i:nat).{:pattern (Seq.index s1 i) \/ (Seq.index s2 i)}
            i < Seq.length s1 ==> Seq.index s1 i == Seq.index s2 i)

/// Effect mechanics
/// ----------------
///
///
/// Intro to weakest precondition style program verification
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// For more information on how WP (weakest precondition) style program verification works, see the
/// following:
///
///  - *Guarded commands, nondeterminacy and formal derivation of programs* by Dijkstra (ACM, 1975)
///  - Section 9.1 of the F* tutorial
///
/// Basically, the idea is to have a symbolic execution of the program "backwards" where we start
/// with a postcondition for the whole program and go backwards. At each statement, we take the
/// postcondition to that statement and apply the WP transformation to it. By doing that to every
/// statement, we end up with a weakest precondition for the whole program - of course that should
/// be trivially true, otherwise we can't prove the program to be valid.
///
/// Note that the WP-style of specifying conditions is (at least for our purposes) equivalent to the
/// Hoare style with pre- and postconditions (in F*: ``requires`` and ``ensures``). The two can
/// actually be converted into each other, which is exactly what we do below to get from WP-style
/// notation to the ``requires``/``ensures`` notation. By default, F* uses the WP style.
///
/// Types for the pre-/postconditions and WP transformers
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Type of the preconditions for this monad, taking a trace, returning True/False
type pre_t = trace -> Type0

/// Type of the postconditions for this monad, taking the result of the function plus a trace,
/// returning True/False
type post_t (a:Type) = result a -> trace -> Type0

/// Type of the weakest precondition transformers for this monad (i.e., type of functions that
/// compute weakest preconditions from postconditions).
/// This is only relevant for type checking and not for "functional" aspects.
type wp_t (a:Type) =
  wp:(post_t a -> pre_t){ // This type describes a function from post_t to pre_t with the following refinement:
    forall (p q:post_t a). (  // For all pairs p, q of post conditions...
      forall (r:result a) (s:trace). p r s ==> q r s // ... if p implies q forall results and traces...
    ) ==> (
      forall (s:trace). wp p s ==> wp q s // ... then the wp of p implies the wp of q forall traces.
    )
  }
// Intuition of the above: A stronger postcondition always requires an equal or stronger
// precondition.


/// Type of what the effect will later expect: A total function from a trace to a (result & trace).
/// Basically the "monadic type"; or: "Real" type of a function of this monad.
///
/// In our case: Take a trace, output a trace + some result. Plus: If ``wp`` is true before the
/// function, we are guaranteed to have ``grows s0 s1 ==> postcond (result, s1)`` at the end of the
/// function. This does *not* enforce ``grows``!
type repr (a:Type) (wp:wp_t a) =
  s0:trace ->
  PURE
  (result a & trace)
  (fun (postcond:pure_post (result a & trace)) ->
    // "Raise" to DYERROR world, i.e., define a postcondition in the DYERROR world
    let dy_error_postcond:post_t a = fun (x:result a) s1 -> grows s0 s1 ==> postcond (x, s1) in
    // Calculate the precondition in the DYERROR world
    let dy_error_precond:pre_t = wp dy_error_postcond in
    // "Step back down" to the PURE world by "factoring out" the trace from the precondition
    let pure_precond:pure_pre = dy_error_precond s0 in
    // Return the PURE world precondition (note that this is of kind "Type")
    pure_precond
  )



/// How to create an element of the effect (i.e., an instance of the monadic type; sometimes this
/// function is also called "unit" outside of F*).

unfold
let return_wp (a:Type) (x:a) : wp_t a = fun p -> p (Success x)

inline_for_extraction
let return (a:Type) (x:a) // Basically: Take an x of some type a and convert/lift it to our monadic type
: repr a (return_wp a x)
= fun s0 -> Success x, s0 // Don't change the trace, just return x


/// What happens if we call two of our monadic functions in sequence? Sequential composition g(f(⋅))
/// where f takes a value of arbitrary type and returns a value of type "a"; g takes a value of type
/// "a" and returns a value of type "b".
/// The wp stuff is again only relevant for type checking.

// WP transformation for bind: Use wp_f in case f returns Error, otherwise use wp_f(wp_g) (i.e.,
// "backwards execution").
unfold
let bind_wp (#a:Type) (#b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : wp_t b =
  fun (p:post_t b) s0 -> wp_f (fun (x:result a) s1 ->
    (Error? x ==> p (Error (Error?.e x)) s1) /\
    (Success? x ==> (wp_g (Success?.v x)) p s1)) s0  

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b (bind_wp wp_f wp_g)
= fun s0 -> // Remember: type repr ... means that we expect a trace and return a result plus a trace
  let x, s1 = f s0 in // call the "inner function", i.e., f with the input trace
  match x with
  | Error e -> Error e, s1 // if f threw an error, propagate that error (w/o calling g)
  | Success x -> (g x) s1  // if f returned a value, call g with that value and f's output trace,
                          // g will then return a tuple (result a & trace)


inline_for_extraction
let subcomp (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f)
: Pure (repr a wp_g)
  (requires forall (p:post_t a) s. wp_g p s ==> wp_f p s)
  (ensures fun _ -> True)
= f

/// Defines branching within the effect (this is "just" about the WPs, not about values we actually
/// touch in the later implementations; i.e., this is about "how to verify the code" and not about
/// "how to run the code" from F*'s point of view).
///
/// It is defined straight-forward here: If the "then" branch is used, use the wp of the "then"
/// branch, otherwise use the wp of the "else" branch. I.e., we don't use this to do anything fancy.

unfold
let if_then_else_wp (#a:Type) (wp_then wp_else:wp_t a) (p:bool) : wp_t a =
  fun post s0 ->
    (p ==> wp_then post s0) /\
    ((~ p) ==> wp_else post s0)  

inline_for_extraction
let if_then_else (a:Type)
  (wp_then:wp_t a) (wp_else:wp_t a)
  (f:repr a wp_then) (g:repr a wp_else) // "Expressions" for the then/else branches
  (p:bool)
: Type
= repr a (if_then_else_wp wp_then wp_else p)

/// Actual effect definition (DYERROR)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// Here, we define a new effect with the following attributes:
///
/// - "total": everything terminates,
/// - "reifiable": We can take a function of this effect and reify it (i.e., make it a pure
///   function, which is executable) and
/// - "reflectable": allows us to look inside the structure, e.g., for tactics - unused by us a.t.m.,
///   except for "get"
/// - layered: this enables us to use ``sub_effects``, see below for examples (e.g., lifting from
///   PURE)

total reifiable reflectable
layered_effect {
  DYERROR : a:Type -> wp_t a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

/// Layering DYERROR
/// ----------------
///
/// From here on, the layering is used; i.e., inject DYERROR into other monads and the other way
/// round. Compare this to ST: Inside ST functions, we can also use Tot/PURE functions. This works
/// because PURE is a (strict) subset of ST.
///
/// Note the PURE is a bit special, so calling a PURE function inside a DYERROR function *might*
/// still somehow work, but since DYERROR does not just wrap a trace, but also the ``result`` return
/// type, it probably will be a bit complicated (you basically would have to do the lifting "by
/// hand"). But in general, we need a layered effect here as our lifting is not trivial.

// We want to link PURE and DY world - that's where we need lifting; to lift from PURE to DYERROR effect

// Tell F* how to lift a PURE WP to a DYERROR WP

unfold
let lift_pure_dyerror_wp (#a:Type) (wp:pure_wp a) : wp_t a =
  FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun p s0 -> wp (fun x -> p (Success x) s0)

// Tell F* how to lift a PURE function to DYERROR (just call the function and leave the trace as-is)

inline_for_extraction
let lift_pure_dyerror (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
: repr a (lift_pure_dyerror_wp wp)
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun s0 -> Success (f ()), s0

sub_effect PURE ~> DYERROR = lift_pure_dyerror

/// Effects based on DYERROR (i.e., DY)
/// -----------------------------------
///
/// Now we're defining new effects to make it more convenient to use the DYERROR effect (which is in
/// WP-style, we want the more convenient requires/ensures-style). This kind of transformation
/// between the styles (Hoare - req, ens vs. Dijkstra - WP) is pretty standard.

// Effect abbreviation - DY is an abbreviation of DYERROR with a specific set of params (like Tot and PURE)
// "a" is the return type of a function with effect DY (e.g. "term")
// "req" is the "requires" predicate (pre condition)
// "ens" is the "ensures" predicate (post condition)
effect DY (a:Type) (req:trace -> Type0) (ens:(s0:trace{req s0} -> result a -> trace -> Type0)) =
  DYERROR a (fun post s0 -> req s0 /\ (forall (x:result a) (s1:trace). ens s0 x s1 ==> post x s1))
//          | This thing above is the weakest precondition
// WP is: requires predicate AND for all results and "after" traces which satisfy the ensures
//        predicate, the post condition is true.



/// Some actions on instances of the mondaic type
/// ---------------------------------------------

(** Get the current trace *)
inline_for_extraction
val get (_:unit)
: DYERROR trace (fun p s -> p (Success s) s)

(** Set a new trace (which has to be an extenstion of the current trace) *)
inline_for_extraction
val put (s1:trace)
: DYERROR unit (fun p s0 -> grows s0 s1 /\ p (Success ()) s1)

(** "Emit" an error inside of a DYERROR function *)
inline_for_extraction
val error (#a:Type) (e:string)
: DYERROR a (fun p s -> p (Error e) s)

(** Get the current trace length *)
inline_for_extraction
val current_trace_len (_:unit)
:DYERROR nat (fun p s -> p (Success (trace_len s)) s)

(** Append an entry to the trace *)
inline_for_extraction
val write_at_end (e:entry_t)
: DYERROR unit (fun p s -> trace_inv0 (Seq.snoc s e) /\ p (Success ()) (Seq.snoc s e))

(** Get the trace entry at index i *)
inline_for_extraction
val index (i:nat)
:DYERROR entry_t (fun p s -> i < Seq.length s /\ p (Success (Seq.index s i)) s)

/// "Monotonic" Stable Predicates over the Trace
/// --------------------------------------------
///
/// See Ahman et al.'s POPL 2018 paper "Recalling a Witness:
/// Foundations and Applications of Monotonic State".

type trace_pred = trace -> Type0

/// Stable predicates: Once they are true, they stay true => This gives us monotonic properties as
/// long as we stay within the effect/monad.
inline_for_extraction
let stable (p:trace_pred) =
  forall s0 s1. (p s0 /\ grows s0 s1) ==> p s1

/// Think about witnessed as a "token" which can be used at some point to "prove to F*" that we
/// proved p to be true before.  And if p is stable, we can use this token later (see "recall") to
/// remind F* of that fact.
val witnessed (p:trace_pred) : Type0

/// "Create" a witnessed "token"
inline_for_extraction
val witness (p:trace_pred)
: DYERROR unit (fun post s -> p s /\ stable p /\ (witnessed p ==> post (Success ()) s))

/// "Remind" F* that we witnessed p before.
inline_for_extraction
val recall (p:trace_pred)
: DYERROR unit (fun post s -> witnessed p /\ (p s ==> post (Success ()) s))

// Part from "recalling a witness" paper stops here

/// Monadic wrappers for admit/assume
/// ---------------------------------
///
/// The following three functions are kind of wrappers arount assert, assume and admit - they might
/// sometimes be more efficient than the "originals", because they are tailored towards the DYERROR
/// effect monad.
///
/// These are convenience functions that could be helpful for debugging (i.e., helping F* to figure
/// out what exactly it couldn't prove). Certainly useful to debug the monad itself, maybe not so
/// much for application code.

// Read as m assert - lifts the assert to be a monad-specific assertion
val massert (p:Type0)
: DYERROR unit (fun post s -> p /\ (p ==> post (Success ()) s))

// Read as m assume
val massume (p:Type0)
: DYERROR unit (fun post s -> p ==> post (Success ()) s)

// Read as m admit
inline_for_extraction
val madmit: #a:Type -> unit -> DY a
			     (fun _ -> True)
			     (fun _ _ _ -> False)

/// Trace predicates
/// ----------------

(** Checks whether [entry] can be found at [trace_index] in the trace. *)
inline_for_extraction
let entry_at_pred (n:nat) (e:entry_t) : (p:trace_pred{stable p}) =
  fun (s:trace) ->
  Seq.length s > n /\
  Seq.index s n == e

(** Checks whether [entry] can be found at [trace_index] in the trace. This is a witnessing of the
entry_at_pred*)
let entry_at trace_index entry = witnessed (entry_at_pred trace_index entry)


(** Property of [entry_at]: If [entry_at i] is true for two entries (with the same [i]), then these
two entries are equal. *)
val entry_at_injective: i:nat -> e1:entry_t -> e2:entry_t ->
  Lemma (requires (entry_at i e1 /\ entry_at i e2))
        (ensures (e1 == e2))
        [SMTPat (entry_at i e1); SMTPat (entry_at i e2)]


val entry_at_before_now: idx:nat -> et:entry_t -> DY unit
  (requires fun t0 -> entry_at idx et)
  (ensures fun t0 _ t1 -> 
     t0 == t1 /\
     idx < trace_len t1
  )
  



/// PURE (stateless) error monad (ERROR)
/// ------------------------------------

(**+ Up to here, we have basically what we had before. Now we define a PURE error monad which can be lifted to DYERROR. That way, we can always stay in the DYERROR world. *)



/// Error monad (not stateful), basically a thin wrapper around PURE to always return a ``result``.

type epre_t = Type0
type epost_t (a:Type) = result a -> Type0

/// wp has a refinement for monotonicity -- we should handle it more uniformly in the typechecker

type ewp_t (a:Type) = wp:(epost_t a -> epre_t)

/// Now the underlying representation of the layered effect
///
/// It's just a thunked option-returning computation

type erepr (a:Type) (wp:ewp_t a) = unit -> PURE (result a) wp


/// Defining the effect combinators
///
/// We require return, bind, subcomp, and if_then_else


inline_for_extraction
let ereturn (a:Type) (x:a)
: erepr a (fun p -> p (Success x))
= fun _ -> Success x

assume EWP_monotonicity_axiom:
  forall (a:Type) (wp:ewp_t a).
    (forall p q. (forall x. p x ==> q x) ==>
            (wp p ==> wp q))

inline_for_extraction
let ebind (a:Type) (b:Type)
  (wp_f:ewp_t a) (wp_g:a -> ewp_t b)
  (f:erepr a wp_f) (g:(x:a -> erepr b (wp_g x)))
: erepr b
  (fun (p:epost_t b) ->
    wp_f (fun (r:result a) ->
      match r with
      | Success x -> wp_g x p
      | Error s -> p (Error s)))
= fun _ ->
  let r = f () in
  match r with
  | Error s -> Error s
  | Success x -> g x ()


inline_for_extraction
let esubcomp (a:Type)
  (wp_f:ewp_t a) (wp_g:ewp_t a)
  (f:erepr a wp_f)
: Pure (erepr a wp_g)
  (requires forall p. wp_g p ==> wp_f p)
  (ensures fun _ -> True)
= f


inline_for_extraction
let eif_then_else (a:Type)
  (wp_f:ewp_t a) (wp_g:ewp_t a)
  (f:erepr a wp_f) (g:erepr a wp_g)
  (p:bool)
: Type
= erepr a
  (fun post ->
    (p ==> wp_f post) /\
    ((~ p) ==> wp_g post))


/// The effect definition

total reifiable reflectable
layered_effect {
  ERROR : a:Type -> ewp_t a -> Effect
  with
  repr = erepr;
  return = ereturn;
  bind = ebind;
  subcomp = esubcomp;
  if_then_else = eif_then_else
}


/// Lift from PURE to ERROR

assume Pure_wp_monotonic:
  (forall (a:Type) (wp:pure_wp a).
     (forall p q. (forall x. p x ==> q x) ==>
             (wp p ==> wp q)))

inline_for_extraction
let lift_pure_error (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
: erepr a (fun p -> wp (fun x -> p (Success x)))
= fun _ -> Success (f ())


sub_effect PURE ~> ERROR = lift_pure_error


/// Shorthand for hoare-style specs: Err functions have no precondition

//effect Err (a:Type) (pre:Type0) (post:result a -> Type0) =
//  ERROR a (fun p -> pre /\ (forall r. post r ==> p r))

effect Err (a:Type) (post:result a -> Type0) =
   ERROR a (fun p -> (forall r. post r ==> p r))



// More interesting:


/// Lifting ERROR to DY


unfold
let lift_error_dyerror_wp (#a:Type) (ewp:ewp_t a) : wp_t a =
  fun p s0 -> ewp (fun r -> p r s0)  

inline_for_extraction
let lift_error_dyerror (a:Type) (ewp:ewp_t a) (f:erepr a ewp)
: repr a (lift_error_dyerror_wp ewp)
= fun s0 -> f (), s0

sub_effect ERROR ~> DYERROR = lift_error_dyerror

// ERROR monad version of "error" (i.e., function to throw errors)
inline_for_extraction
let err (#a:Type) (e:string)
: ERROR a (fun p -> p (Error e))
= ERROR?.reflect (fun _ -> Error e)

// ERROR is kind of a constructor, it's "just" a wrapper with some fields. By adding reflectable to
// the layered effect, we tell F* to construct another "field" (actually a function) named "reflect"
// in ERROR that takes a pure function and lifts that to the monadic type. "reify" is the same
// concept, just the other way (i.e., from an ERROR function to a PURE function).
