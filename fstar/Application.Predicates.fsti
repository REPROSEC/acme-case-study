/// Application.Predicates
/// ======================
///
/// This interface describes some properties of the application and must be implemented by the
/// application.  It serves as a way of "injecting" application properties into the generic model.
module Application.Predicates
open Helpers
open DY.Principals
open DY.Labels
open DY.Crypto
open DY.Entry
open DY.Monad
open DY.Trace
open Labeled.Crypto

/// Pre-/Postconditions on cryptographic operations
/// -----------------------------------------------
///
/// These predicates can be used to set application-specific preconditions on certain cryptographic
/// operations, e.g., signatures. In the simplest case, these are all just ``True`` - this means
/// that all cryptographic operations (like ``sign``) can be called by any principal at any time
/// with any set of values.
///
/// If used (i.e., not just set to ``True``), these give us certain guarantees when "undoing"
/// them. For example, we could say that signatures are only allowed on bytes with a specific
/// shape. That would make it "harder" to use sigantures, because we have to prove that the signed
/// bytes has the correct format. But: Whenever signature verification succeeds, we have a guarantee
/// that the signed message is bytes with that specific shape.
///
/// Think of these as giving us authentication properties whereas the labeling gives us
/// confidentiality properties.

(** Global Predicate on public key encryption with untrusted keys:
    Encryption of bytes is only allowed if this predicate is
    true. On the other hand, whenever decryption succeeds, we and
    F* know that the bytes fulfills this predicate. *)
val pke_un_pred: label -> bytes -> Type0

val pke_un_pred_lemma: t:bytes -> t':bytes -> 
    Lemma (forall l l'. (pke_un_pred l t /\ eq_label l l' /\ eq_bytes t t') ==> pke_un_pred l' t')

let corrupt_at_lemma (i:nat) :
  Lemma (forall j. i <= j ==> extends_corrupt (corrupt_at i) (corrupt_at j)) = ()

(** A collection of predicated needed by the labeling relation *)
let app_preds : preds = {
  model = {
    corrupt_at = corrupt_at;
    corrupt_at_lemma = corrupt_at_lemma;
    is_generated = is_nonce_generated_at;
    is_generated_lemma = is_generated_is_injective;
    is_generated_eq_bytes_lemma = is_generated_at_eq_bytes_are_equal;
    is_generated_eq_lemma = is_generated_eq;
 };
  global = {
    pke_un_pred = pke_un_pred;
    pke_un_pred_lemma = pke_un_pred_lemma;
 }}


let contains_corrupt_principal_later_lemma
 (idx:nat)
 (sec_intendees: secret_intendees):
 Lemma
 (
   contains_corrupt_principal (app_preds.model.corrupt_at  idx) sec_intendees ==>
    (forall i. later idx i ==>
     contains_corrupt_principal (app_preds.model.corrupt_at i) sec_intendees
   )
 )
 [SMTPat (contains_corrupt_principal (app_preds.model.corrupt_at idx) sec_intendees)]
 = corrupt_at_lemma idx


/// Application-specific Global predicates
/// --------------------------------------

val authenticated_send_pred: idx:nat -> sender:principal -> receiver:principal ->
			     msg:bytes -> Type0
let authenticated_send_pred_preserves_eq (idx:nat) (sender:principal) (receiver:principal)
    (msg:bytes) (msg':bytes) : Lemma
    ((authenticated_send_pred idx sender receiver msg /\
      eq_bytes msg msg') ==> authenticated_send_pred idx sender receiver msg') = ()

val event_pred: idx:nat -> sender:principal -> event:event -> Type0

val event_pred_preserves_eq : (idx:nat) -> (sender:principal) ->
    (ev:string) -> (pl:list bytes) -> (pl':list bytes) -> Lemma
    ((event_pred idx sender (ev,pl) /\ eq_list_bytes pl pl') ==> event_pred idx sender (ev,pl'))
    [SMTPat (event_pred idx sender (ev,pl));
     SMTPat (event_pred idx sender (ev,pl'))] 

(** True iff all bytes in [session_state] are readable by [p]'s session/version
([session_index]/[version_index]). *)
let is_session_state_readable (i:nat) (p:principal) (session_index:nat) (version_index:nat) (session_state:session_state) =
    (forall s.
      Some? (lookup session_state s) ==>
          can_label_of_bytes_flow_to app_preds i (Some?.v (lookup session_state s))
                         (readable_by (create_secret_intendees [] [sess_ver p session_index version_index]))
    )

(** True iff [v] and [state] have the same length and all sessions in [state] are readable by the version given in [v]. *)
let is_principal_state_readable (idx:nat) (p:principal) (v:version_vec) (state:principal_state) =
  (Seq.length state = Seq.length v) /\
  (forall i. i < Seq.length v ==> is_session_state_readable idx p i v.[i] state.[i])

/// State invariant
/// ---------------
///
/// This invariant carries all integrity and trace-based properties, i.e., all security and privacy
/// properties except simple confidentiality. Thus, this is a key element when modeling protocols
/// and properties.
(** Invariant on pricipals' states; carries application-specific integrity and trace-based properties. *)
val state_inv: i:nat -> principal -> version_vec -> principal_state -> Type0

val state_inv_later: i:nat -> j:nat -> p:principal -> vv:version_vec -> st:principal_state ->
  Lemma ((state_inv i p vv st /\ i <= j) ==> state_inv j p vv st)

/// Principal's state type
/// ----------------------

(** A restricted [principal_state], fulfilling [is_principal_state_readable]. Has to be used when interacting with the application API. *)
type app_state (idx:nat) (p:principal) (v:version_vec) = s:principal_state{is_principal_state_readable idx p v s}


#push-options "--max_fuel 2 --max_ifuel 2"
let corrupt_principal_has_publishable_state (i:nat) (j:nat) (p:principal) (v:version_vec) (s:principal_state) (session_index:nat) (t:string) (x:bytes) :
  Lemma (requires (
          is_principal_state_readable i p v s /\
          Seq.length v = Seq.length s /\
          session_index < Seq.length v /\
          is_some (lookup s.[session_index] t) x /\
	  i <= j /\
          corrupt_at j (sess_ver p session_index (Seq.index v session_index))
        ))
        (ensures (is_publishable_p app_preds j x)) =
  let ps = create_secret_intendees [] [sess_ver p session_index (Seq.index v session_index)] in
  assert ((corrupt_at j) (sess_ver p session_index (Seq.index v session_index)));
  assert (ps.readers == [sess_ver p session_index (Seq.index v session_index)]);
  assert (exists p. FStar.List.Tot.mem p ps.readers /\ (corrupt_at j) p);
  assert (contains_corrupt_reader (corrupt_at j) ps);
  assert (contains_corrupt_principal (corrupt_at j) ps);
  corrupt_can_flow_to_public (corrupt_at j) ps;
  assert (can_flow (corrupt_at j) (readable_by ps) public);
  let l = get_label (Some?.v (lookup s.[session_index] t)) in
  assert (is_labeled_p app_preds i (Some?.v (lookup s.[session_index] t)) l);
  assert (can_flow (corrupt_at i) l (readable_by ps));
  can_flow_transitive (corrupt_at j) l (readable_by ps) public;
  can_flow_later_forall app_preds; 
  assert (can_flow (corrupt_at j) l public)
#pop-options
