/// DY.Trace
/// ========
///
/// This module contains the definition of the global (shared) execution trace. This trace contains
/// different types of events which record things like sending messages, the attacker corrupting
/// entities, principals changing their states and protocol-specific events like starting a login
/// session.
module DY.Trace

open Helpers
open DY.Principals
open DY.Labels
open DY.Crypto
open DY.Entry
open DY.Monad

/// Monotonic predicates on the state

/// Generation of nonces
(** Predicate on trace entries, true iff the entry at [trace_index] is a [Gen] event with the given
bytes, label and usage AND that bytes is a nonce. *)
let is_nonce_generated_at (trace_index:nat) (generated_value:bytes) (label:label) (usage:usage) (usage_pred: usage_pred usage) =
  entry_at trace_index (Gen generated_value label usage usage_pred) /\
  generated_value == gnonce trace_index label usage

(** Predicate on the trace, true iff there is a [Gen] entry with index <= j in the trace with
the given bytes, label and usage AND that bytes is a nonce. *)
let is_nonce_generated_before (j:nat) (t:bytes) (l:label) (u:usage) (p:usage_pred u) =
  exists (trace_index:nat). trace_index <= j /\ is_nonce_generated_at trace_index t l u p

let is_generated_at_implies_generated_bytes_is_a_nonce
    (trace_index:nat) (t:bytes) (l:label) (u:usage) (p:usage_pred u):
    Lemma (requires (is_nonce_generated_at trace_index t l u p))
          (ensures (eq_bytes t (gnonce trace_index l u)))
    [SMTPat (is_nonce_generated_at trace_index t l u p)] = ()

(** If two bytes [t1] and [t2] are both generated at the same trace index [n], then they are equal. *)
let is_generated_is_injective (n:nat) (t1:bytes) (t2:bytes):
    Lemma (forall l1 u1 l2 u2 p1 p2. is_nonce_generated_at n t1 l1 u1 p1 /\
				is_nonce_generated_at n t2 l2 u2 p2 ==>
				t1 == t2 /\ l1 == l2 /\ u1 == u2 /\ p1 == p2) = ()

(* Equivalent nonces are generated at the same position in the trace *)
let is_generated_at_preserved_by_eq
    (trace_index:nat) (t:bytes) (l:label) (u:usage) (p:usage_pred u):
    Lemma (requires (is_nonce_generated_at trace_index t l u p))
          (ensures (forall t' l' u'.
	     (eq_bytes t t' /\ l == l' /\ u == u') ==>
	     is_nonce_generated_at trace_index t' l' u' p))
    [SMTPat (is_nonce_generated_at trace_index t l u p)] = ()

let is_generated_at_eq_bytes_are_equal (trace_index:nat) (t:bytes) (t':bytes) : 
    Lemma (forall l u l' u'. (eq_bytes t t' /\ l == l' /\ u == u') ==>
	     (forall p. is_nonce_generated_at trace_index t l u p ==> is_nonce_generated_at trace_index t' l' u' p)) = () 

(* Eq_bytes nonces are equal *)
let nonce_eq_bytes_is_generated (t:bytes) (t':bytes) :
    Lemma (eq_bytes t t' ==> (forall i l u p. is_nonce_generated_at i t l u p <==> is_nonce_generated_at i t' l u p)) 
    [SMTPat (eq_bytes t t'); SMTPat (forall i l u p. is_nonce_generated_at i t l u p)]= () 
    
let is_generated_eq (n:nat) (l:label) (u:usage) : 
    Lemma (forall n' l' u' p. is_nonce_generated_at n' (gnonce n l u) l' u' p ==> (n = n' /\ l == l' /\ u == u')) = ()

/// Events
(** Predicate on trace entries, true iff the entry at [trace_index] is an [Event] event with the
given value. *)
let did_event_occur_at trace_index p (ev,tl) =
  (exists tl'. eq_list_bytes tl' tl /\ entry_at trace_index (Event p (ev,tl')))

let did_event_occur_at_preserved_by_eq
    (trace_index:nat) (p:principal )(ev:string) (tl1:list bytes):
    Lemma (requires (did_event_occur_at trace_index p (ev,tl1)))
          (ensures (forall tl2.
	     eq_list_bytes tl1 tl2 ==>
	     did_event_occur_at trace_index p (ev,tl2)))
    [SMTPat (did_event_occur_at trace_index p (ev,tl1))] = ()


(** Predicate on the trace, true iff there is an [Event] entry with index <= j in the trace with
the given value. *)
let did_event_occur_before (j:nat) (p:principal) (e:event) =
  exists (trace_index:nat). trace_index <= j /\ did_event_occur_at trace_index p e

(** Predicate on trace entries, true iff the entry at [trace_index] is a [Message] event with the
given value. *)
let is_published_at trace_index t =
  exists p1 p2. entry_at trace_index (Message p1 p2 t)

(** Predicate on trace entries, true iff the entry at [trace_index] is an
[AuthenticatedMessage] event with the given value. *)
let is_auth_published_at trace_index t =
  exists p1 p2. entry_at trace_index (AuthenticatedMessage p1 p2 t)

(** Predicate on the trace, true iff there is a [Message] entry with index <= j in the trace
with the given bytes. *)
let is_published_before (j:nat) (t:bytes) =
  exists (trace_index:nat). trace_index <= j /\ is_published_at trace_index t

(** Predicate on the trace, true iff there is an [AuthenticatedMessage] entry with index <= j in the
trace with the given bytes. *)
let is_auth_published_before (j:nat) (t:bytes) =
  exists (trace_index:nat). trace_index <= j /\ is_auth_published_at trace_index t

(** Predicate on trace entries, true iff the entry at [trace_index] is a [Message] event with the
given sender, receiver and bytes. *)
let is_message_sent_at trace_index sender receiver b =
  entry_at trace_index (Message sender receiver b)

(** Predicate on trace entries, true iff the entry at [trace_index] is an [AuthenticatedMessage]
event with the given sender, receiver and bytes. *)
let is_authenticated_message_sent_at trace_index sender receiver b =
  entry_at trace_index (AuthenticatedMessage sender receiver b)

(** Predicate on trace entries, true iff the entry at [trace_index] is a [SetState] event for the
given principal with the given state value. *)
let is_set_state_at trace_index principal v new_state =
  entry_at trace_index (SetState principal v new_state)

(** Predicate on the trace, true iff the state of [p] at [trace_index] is the given state
value. I.e., the last time that this principal's state has been set, it was set to [s] with version
vector [v]. *)
let rec is_state_at_equal_to (i:nat) (p:principal) (v:version_vec) (b:principal_state) : Type0 =
  // Either the state is set right here (at this i) and we are done...
  is_set_state_at i p v b \/
  // ... or we look at the index before the current i (this recurses until the whole trace has been looked at)
  (
    i > 0 /\
    (~ (exists b'. is_set_state_at i p v b')) /\
    is_state_at_equal_to (i-1) p v b
  )

let rec existing_current_state_implies_state_was_set
  (i:nat) (p:principal) (v:version_vec) (s:principal_state):
  Lemma (is_state_at_equal_to i p v s ==> (exists j. j <= i /\ is_set_state_at j p v s))  =
  if i = 0 then ()
  else existing_current_state_implies_state_was_set (i-1) p v s


/// Corruption
(** Predicate on trace entries, true iff the entry at [trace_index] is a [Corrupt] event with the
given [versionid]. *)
let is_corrupted_at trace_index p s v = entry_at trace_index (Corrupt p s v)

let is_corrupted_before trace_index p s v =
  (exists idx'. idx' <= trace_index /\ is_corrupted_at idx' p s v)  
(** Predicate on the trace, true iff the principal p contains a version that was corrupted before
[trace_index] (see also [is_corrupted_before]). *)
let is_principal_corrupted_before trace_index p =
  exists s v. is_corrupted_before trace_index p s v

(** True, iff [p] covers a corrupted version (at any index in the trace). *)
let contains_corrupted_version_at (idx:nat) (p:versionid) =
    exists p' s' v'. (is_corrupted_before idx p' s' v' /\ covers p (sess_ver p' s' v'))

(** Type of a predicate which is true iff [p] contains a corrupted version. 
Note that this type for predicates is not actually linked to corruption, we just happen to always
use it in that context. *)
let corrupt_pred =
  (p:(versionid -> Type0){forall x y. (covers x y /\ p y) ==> p x})

(** Predicate on [versionid]: True, iff the given [versionid] contains a corrupted version. Note
that the type of this symbol is an arrow type, i.e., this is a function/predicate taking a
[versionid] and returning a logical value. *)
let corrupt_at i : corrupt_pred =
  covers_is_transitive ();
  contains_corrupted_version_at i


/// Trace API
/// ---------
///
/// These functions allow users of the module to interact with the trace in a clean, defined
/// way. Note that they are not meant to be used by protocol implementations (those should use the
/// functions provided by the Labeled.ApplicationAPI).

(** Pretty-Printing Functions *)
val tot_print_string: string -> bool

val print_string: string -> DY unit
		   (requires (fun t0 -> True))
		   (ensures (fun t0 _ t1 -> t0 == t1))

val print_bytes: bytes -> DY unit
		   (requires (fun t0 -> True))
		   (ensures (fun t0 _ t1 -> t0 == t1))

val print_trace: unit -> DY unit
		   (requires (fun t0 -> True))
		   (ensures (fun t0 _ t1 -> t0 == t1))

(** Initialize the trace (actually: Make sure that it's currently empty) *)
val init: unit -> DY unit
    (requires (fun t0 -> trace_len t0 = 0))
    (ensures (fun t0 _ t1 -> t0 == t1))

(** Get current trace length *)
val current_trace_len: unit -> DY nat
    (requires (fun t0 -> True))
    (ensures (fun t0 r t1 -> t0 == t1 /\ r == Success (trace_len t0)))


(** Generate fresh (random) values. Returns the generated value (which is always a nonce). *)
val gen: l:label -> u:usage -> p:usage_pred u -> DY bytes
                      (requires (fun t0 -> True))
                      (ensures (fun t0 (s) t1 ->
			match s with
			| Error _ -> t0 == t1
			| Success s ->
                          trace_len t1 = trace_len t0 + 1 /\
                          is_nonce_generated_at (trace_len t0) s l u p))

(** Triggering protocol-specific events, e.g., for authentication properties. *)
val trigger_event: p:principal -> ev:event -> DY unit
                      (requires (fun t0 -> True))
                      (ensures (fun t0 (s) t1 ->
			match s with
			| Error _ -> t0 == t1
			| Success s ->
				  trace_len t1 = trace_len t0 + 1 /\
				  did_event_occur_at (trace_len t0) p ev))

(** Send messages on the network. This publishes the message to the attacker. Returns the index of
the send event in the trace. Note that sender and receiver are not checked in any way. *)
val send: sender:principal -> receiver:principal -> msg:bytes -> DY nat
                      (requires (fun t0 -> True))
                      (ensures (fun t0 trace_index t1 ->
			match trace_index with
			| Error _ -> t0 == t1
			| Success n ->
                          (trace_len t1 = trace_len t0 + 1 /\
                          n = trace_len t0 /\
                          is_published_at n msg /\
                          is_message_sent_at n sender receiver msg)))

(** Authenticated messages sent on the network *)
val authenticated_send: sender:principal -> receiver:principal -> msg:bytes -> DY nat
                      (requires (fun h0 -> True))
                      (ensures (fun t0 trace_index t1 ->
                        match trace_index with
			 | Error _ -> t0 == t1
			 | Success n ->
                         trace_len t1 = trace_len t0 + 1 /\
                         n = trace_len t0 /\
                         is_auth_published_at n msg /\
                         is_authenticated_message_sent_at n sender receiver msg))


(** Receive a message. Returns [Some bytes] if the given trace index corresponds to a send event for
the given receiver, [None] otherwise. *)
val receive_i: trace_index:nat -> receiver:principal -> DY (claimed_sender:principal * bytes)
                      (requires (fun t0 -> trace_index < trace_len t0))
                      (ensures (fun t0 t t1 ->
                        t0 == t1 /\
                        (match t with
			 | Error _ -> True
			 | Success (_,t) ->
                           (is_published_at trace_index t /\
                           (exists sender recv. is_message_sent_at trace_index sender recv t)))))


(** Authenticate message received on the network *)
val authenticated_receive_i: trace_index:nat -> receiver:principal -> DY (bytes & principal)
                      (requires (fun t0 -> trace_index < trace_len t0))
                      (ensures (fun t0 t t1 ->
                        t0 == t1 /\
                        (match t with
			 | Error _ -> True
			 | Success (message,sender) ->
                           is_auth_published_at trace_index message /\
                           (exists recv. is_authenticated_message_sent_at trace_index sender recv message)
                      )))


/// Version and actual state content are kept separately to be able to later model metadata leakage:
/// The version vector represents metadata about where things are stored. If we kept metadata and
/// session state inside one type, this would be harder to model.
(** Set the internal state [s] of a principal [p] with version vector [v]. *)
val set_state: p:principal -> v:version_vec -> s:principal_state -> DY unit
                      (requires (fun t0 -> Seq.length v = Seq.length s))
                      (ensures (fun t0 trace_index t1 ->
			match trace_index with
			| Error _ -> t0 == t1
			| Success _ ->
				  trace_len t1 = trace_len t0 + 1 /\
				  is_set_state_at (trace_len t0) p v s))


(** Get state for principal (set at index trace_index) *)
val get_state_i: trace_index:nat -> p:principal -> DY (version_vec & principal_state)
                      (requires (fun t0 -> trace_index < trace_len t0))
                      (ensures (fun t0 s t1 ->
                        t0 == t1 /\
                        (match s with
                         | Error _ -> True 
                         | Success (v,s) -> is_set_state_at trace_index p v s)))


(** Helper function for [get_last_update_index_before] below *)
let has_last_update (t:trace) (p:principal) (trace_index:nat) (jvs:option (nat & version_vec & principal_state)) : Type0 =
    match jvs with
    // State of p has not been set yet (up to index trace_index in the trace)
    | None -> forall j v s. j <= trace_index ==> ~ (is_set_state_at j p v s)
    // State of p has been set at some index [j <= trace_index] and there is no index k with [k > j]
    // and [k <= trace_index] at which p's state has been set.
    // I.e., the latest SetState for p (in the trace up to length trace_index) was at index j.
    | Some (j,v,s) -> j <= trace_index /\ is_set_state_at j p v s /\ (forall k v s. (j < k /\ k <= trace_index) ==> ~ (is_set_state_at k p v s))


(** Get the index of the last update to a principal's state before trace_index. *)
val get_last_state_before: trace_index:nat -> p:principal -> DY (option (nat & version_vec & principal_state))
                      (requires (fun t0 -> trace_index < trace_len t0))
                      (ensures (fun t0 jvs t1 -> t0 == t1 /\
				 (match jvs with
				  | Success jvs -> has_last_update t0 p trace_index jvs
				  | Error _ -> True)))


(** Compromise a version. *)
val compromise: p:principal -> s:nat -> v:nat -> DY unit
                (requires (fun t0 -> True))
                (ensures (fun t0 r t1 ->
		      match r with
		      | Error _ -> t0 == t1
		      | Success _ ->
                        trace_len t1 = trace_len t0 + 1 /\
                        is_corrupted_at (trace_len t0) p s v))
