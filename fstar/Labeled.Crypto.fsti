/// Labeled.Crypto
/// ==============
///
/// .. fst::
///  :class: hidden

module Labeled.Crypto

open Helpers
open DY.Labels
open DY.Principals
module C = DY.Crypto
open DY.Entry
open DY.Monad
module T = DY.Trace

/// [includes]: Applying [covers] to secret_intendees
/// -------------------------------------------------
///
/// The following part defines the predicate [includes] on two secret_intendees, which basically is true iff
/// a secret_intendee is [covered] by the other one. More precisely, the predicate is true iff
/// every versionid of the second secret_intendee is covered by a versionid in the first secret_intendee
/// (the issuers and readers are considered separately).


(** [super_list] includes [sub_list], i.e., for each entry [v2] in [sub_list], there is an entry [v1] in [super_list] that
covers [v2] *)
let includes_versionids (super_list:list versionid) (sub_list:list versionid) =
    forall v2. List.Tot.mem v2 sub_list ==> (exists v1. List.Tot.mem v1 super_list /\ covers v1 v2)

(** [p1] includes [p2], i.e., each issuer (and each reader) in [p2] is covered by an issuer,
respective reader, in [p1]. *)
let includes (p1:secret_intendees) (p2:secret_intendees) =
    includes_versionids (p1.issuers) (p2.issuers) /\
    includes_versionids (p1.readers) (p2.readers)

(** Lemma stating that a list of secret_intendees [includes] itself. *)
val includes_is_reflexive: l:secret_intendees ->
    Lemma(includes l l)
    [SMTPat (includes l l)]

/// .. _corruption_predicates_labeled_crypto_fsti:
///
/// Predicates Related to Corruption
/// --------------------------------
///

(** 
True iff there is some issuer in issuers_and_readers that [is_corrupt] (according to is_corrupt)
*)
let contains_corrupt_issuer (is_corrupt:T.corrupt_pred) (issuers_and_readers:secret_intendees) : Type0 =
    (exists p. FStar.List.Tot.mem p issuers_and_readers.issuers /\ is_corrupt p)

(** 
True iff there is some reader in issuers_and_readers that [is_corrupt] (according to is_corrupt)
*)
let contains_corrupt_reader (is_corrupt:T.corrupt_pred) (issuers_and_readers:secret_intendees) : Type0 =
    (exists p. FStar.List.Tot.mem p issuers_and_readers.readers /\ is_corrupt p)

(** True iff one of the issuers or readers in issuers_and_readers [is_corrupt] (according to [c]). *)
let contains_corrupt_principal (is_corrupt:T.corrupt_pred) (issuers_and_readers:secret_intendees) : Type0 =
    contains_corrupt_issuer is_corrupt issuers_and_readers \/
    contains_corrupt_reader is_corrupt issuers_and_readers


/// temporal version of corruption

(** 
True iff there is some issuer in issuers_and_readers that [is_corrupt] (according to is_corrupted_before)
*)
let contains_corrupt_issuer_before
(trace_idx:nat)
(is_corrupt:T.corrupt_pred) (issuers_and_readers:secret_intendees) : Type0 =
    (exists p. FStar.List.Tot.mem p issuers_and_readers.issuers /\ DY.Trace.contains_corrupted_version_at trace_idx p)

(** 
True iff there is some reader in issuers_and_readers that [is_corrupt] (according to is_corrupted_before)
*)
let contains_corrupt_reader_before 
(trace_idx:nat) 
(is_corrupt:T.corrupt_pred) (issuers_and_readers:secret_intendees) : Type0 =
    (exists p. FStar.List.Tot.mem p issuers_and_readers.readers /\ DY.Trace.contains_corrupted_version_at trace_idx p)

(** True iff one of the issuers or readers in issuers_and_readers [is_corrupt] (according to [c]). *)
let contains_corrupt_principal_before
(trace_idx:nat) 
(is_corrupt:T.corrupt_pred) (issuers_and_readers:secret_intendees) : Type0 =
    contains_corrupt_issuer_before trace_idx is_corrupt issuers_and_readers \/
    contains_corrupt_reader_before trace_idx is_corrupt issuers_and_readers


/// Flow of Labels
/// --------------
///
/// The following section defines the **can_flow** predicate on a predicate on corruption and two
/// labels l1 and l2, specifying the possible flows between labels. To put it simply, l1 can_flow to l2
/// if the principals specified in l2 can access the bytes labeled with l1.
///
/// Some central rules are given in the following, see the implementation for all rules:
///
/// * A [Public] label can flow to anything
/// * [ReadableBy secret_intendees] can flow to [Public] if one of the principals is corrupt
///   (under the given corruption predicate)
/// * [ReadableBy secret_intendees_1] can flow to [ReadableBy secret_intendees_2] if one of the
///   principals is corrupt (under the given corruption predicate) or secret_intendees_1 is a superset of secret_intendees_2
/// * [ReadableBy secret_intendees] flows to [Meet label_a label_b]  if [ReadableBy secret_intendees] flows to at least one of [label_a] or [label_b]
/// * [ReadableBy secret_intendees] flows to [Join label_a label_b]  if [ReadableBy secret_intendees] flows to both [label_a] and [label_b]
///


(** If some label can flow to another, this transition is "allowed". Note that the implementation of
this predicate is hidden, users (e.g., the proof) can only use the lemmas describing its
properties. *)
val can_flow: c:T.corrupt_pred -> source:label -> destination:label -> Type0

val corrupt_can_flow_to_public: c:T.corrupt_pred -> issuers_and_readers:secret_intendees ->
    Lemma (ensures (contains_corrupt_principal c issuers_and_readers ==> can_flow c (readable_by issuers_and_readers) public))
          [SMTPat (can_flow c (readable_by issuers_and_readers) public)]

(** [c1] is a superset of [c2] in bytes of who is corrupted *)
let extends_corrupt (c1:T.corrupt_pred) (c2:T.corrupt_pred) =
    forall p. c1 p ==> c2 p

val can_flow_with_more_corruption: c1:T.corrupt_pred -> c2:T.corrupt_pred -> 
  l1:label -> l2:label ->
  Lemma (requires (extends_corrupt c1 c2))
        (ensures (can_flow c1 l1 l2 ==> can_flow c2 l1 l2))
        [SMTPat (extends_corrupt c1 c2); SMTPat (can_flow c1 l1 l2)]

val flows_to_public_can_flow: c:T.corrupt_pred -> l1:label -> l2:label ->
  Lemma (can_flow c l1 public ==> can_flow c l1 l2)

val can_flow_from_public: c:T.corrupt_pred -> l: label ->
  Lemma (can_flow c public l)
        [SMTPat (can_flow c public l)]

val can_flow_transitive: c:T.corrupt_pred -> l1: label -> l2:label -> l3:label ->
  Lemma ((can_flow c l1 l2 /\ can_flow c l2 l3) ==> (can_flow c l1 l3))

val can_flow_reflexive: c:T.corrupt_pred -> l: label ->
  Lemma (ensures (can_flow c l l))
        (decreases %[l;0])
        [SMTPat (can_flow c l l)]

val can_flow_to_meet_left: c:T.corrupt_pred -> l1:label -> l2:label -> l3:label ->
  Lemma (ensures (can_flow c l1 l2 ==> can_flow c l1 (meet l2 l3)))
        (decreases %[l1;1])
        [SMTPat (can_flow c l1 (meet l2 l3))]

val can_flow_to_meet_right: c:T.corrupt_pred -> l1:label -> l2:label -> l3:label ->
  Lemma (ensures (can_flow c l1 l3 ==> can_flow c l1 (meet l2 l3)))
        (decreases %[l1;1])
        [SMTPat (can_flow c l1 (meet l2 l3))]

val can_flow_from_join_left: c:T.corrupt_pred -> l1:label -> l2:label -> l3:label ->
  Lemma (ensures (can_flow c l1 l3 ==> can_flow c (join l1 l2) l3))
        (decreases %[l1;1])
        [SMTPat (can_flow c (join l1 l2) l3)]

val can_flow_from_join_right: c:T.corrupt_pred -> l1:label -> l2:label -> l3:label ->
  Lemma (ensures (can_flow c l2 l3 ==> can_flow c (join l1 l2) l3))
        (decreases %[l1;1])
        [SMTPat (can_flow c (join l1 l2) l3)]

val can_flow_from_meet: c:T.corrupt_pred -> l1:label -> l2:label -> l3:label ->
  Lemma (requires (can_flow c l1 l3 /\ can_flow c l2 l3))
        (ensures (can_flow c (meet l1 l2) l3))
        [SMTPat (can_flow c (meet l1 l2) l3)]

val can_flow_to_join: c:T.corrupt_pred -> l1:label -> l2:label -> l3:label ->
  Lemma (requires (can_flow c l1 l2 /\ can_flow c l1 l3))
        (ensures (can_flow c l1 (join l2 l3)))
        [SMTPat (can_flow c l1 (join l2 l3))]

val can_flow_from_join: c:T.corrupt_pred -> l1:label -> l2:label -> 
  Lemma (ensures (can_flow c (join l1 l2) l1 /\ can_flow c (join l1 l2) l2))
        [SMTPat (can_flow c (join l1 l2) l1); SMTPat (can_flow c (join l1 l2) l2)]

val can_flow_to_smaller_list: c:T.corrupt_pred -> l1:secret_intendees -> l2:secret_intendees ->
  Lemma (requires (includes l1 l2))
        (ensures (can_flow c (readable_by l1) (readable_by l2)))
        [SMTPat (can_flow c (readable_by l1) (readable_by l2))]

val can_flow_to_singleton: c:T.corrupt_pred -> l:secret_intendees -> x:versionid ->
  Lemma (requires (List.Tot.mem x (l.readers)))
        (ensures (can_flow c (readable_by l) (readable_by (create_secret_intendees [] [x]))))
        [SMTPat (can_flow c (readable_by l) (readable_by (create_secret_intendees [] [x])))]

/// Container for Application-Specific Predicates
/// ---------------------------------------------

(** Container for generic modeling predicate *)
noeq type model_preds = {
  corrupt_at : nat -> T.corrupt_pred;
  corrupt_at_lemma: i:nat -> Lemma (forall j. i <= j ==> extends_corrupt (corrupt_at i) (corrupt_at j));
  is_generated: nat -> C.bytes -> label -> u:C.usage -> C.usage_pred u -> Type0;
  is_generated_lemma: n:nat -> t1:C.bytes -> t2:C.bytes ->
		      Lemma (forall l1 u1 l2 u2 p1 p2. is_generated n t1 l1 u1 p1 /\ is_generated n t2 l2 u2 p2 ==> 
						  (t1 == t2 /\ l1 == l2 /\ u1 == u2 /\ p1 == p2));
  is_generated_eq_bytes_lemma : n:nat -> t1:C.bytes -> t2:C.bytes ->
      Lemma (forall l u l' u'. (C.eq_bytes t1 t2 /\ l == l' /\ u == u') ==>
			  (forall (up:C.usage_pred u). is_generated n t1 l u up ==> is_generated n t2 l' u' up));
  is_generated_eq_lemma : n:nat -> l:label -> u:C.usage ->
			    Lemma (forall n' l' u' p. is_generated n' (C.gnonce n l u) l' u' p ==> (n = n' /\ l == l' /\ u == u'));
}

(** Container for global application-specific predicates - not attached to a specific key *)
noeq type global_preds = {
  pke_un_pred: label -> C.bytes -> Type0; // The predicates that must be satisfied when a principal uses pke_un for an untrusted public key
  pke_un_pred_lemma: t:C.bytes -> t':C.bytes -> 
    Lemma (forall l l'. (pke_un_pred l t /\ eq_label l l' /\ C.eq_bytes t t') ==> pke_un_pred l' t')
}

(** Container for all predicates needed for labeling *)
noeq type preds = {
  model: model_preds;
  global: global_preds;
}

(**
  True iff the corrupt predicate of c1 is an extension of the corrupt predicate of c2 (per
  [extends_corrupt]) and the rest of the preds are equal.
*)
let corrupt_entry_is_extended (pr1:preds) (pr2:preds) =
  (forall i. extends_corrupt (pr1.model.corrupt_at i) (pr2.model.corrupt_at i)) /\
  pr1.model.is_generated == pr2.model.is_generated /\
  pr1.global == pr2.global

/// Functions returning labels and usages
/// -------------------------------------


(** 
Returns the label and usage of a secret. More precisely:

  If the secret is a nonce, its label and usage are returned.

  In case of a derived secret [Derive inner_secret context extract_flag], [inner_secret] must have the usage for
  KDF, i.e., the usage must be [KDF (extract_label, extract_usage) expand_usage].
  
  If an expand happened, then the overall label is the label of [inner_secret], as the security level stays the same
  (i.e., we just use the old label).
  Otherwise, in the extract case, the derived secret gets the label that is specified in the usage of the inner secret,
  i.e., extract_label. 
  The overall usage is either [extract_usage] or [expand_usage].

  If the secret is a DH key, its label is the join of labels of private key and public key, and usage is the usage of the keys' DHKey u.
  In all other cases, None is returned.
*)
val get_label_and_usage_of_secret: C.bytes -> option (label & C.usage)

(**
  Returns the label of bytes as follows:
 
   Literal: Public
   Public Key: Public
   Ciphertexts: Public
   Concatenation: Meet of labels of both bytes (corresponds to intersection, see also DY.Principals).
   Signature: Label of the message.
   Nonce: Label of nonce (via get_label_and_usage_of_secret).
   Derived Secrets: Either the extract_label (if an extract happened),
   the expand label (if an expand happened), or None (via get_label_and_usage_of_secret).
*)
val get_label: C.bytes -> label

(** Get label and usage of nonces and derived secrets via [get_label_and_usage_of_secret]. *)
let get_usage_of_secret (t:C.bytes) : option C.usage =
  match get_label_and_usage_of_secret t with
  | None -> None
  | Some (l,u) -> Some u

let get_label_of_secret (t:C.bytes) : option label =
  match get_label_and_usage_of_secret t with
  | Some (l,u) -> Some l
  | _ -> None

let eq_opt_label_and_usage (t: option (label & C.usage)) (t': option (label & C.usage)) =
  match t, t' with 
  | Some (l, u), Some (l', u') -> eq_label l l' /\ C.eq_usage u u'
  | None, None -> True
  | _, _ -> False

let eq_opt_usage (t: option C.usage) (t': option C.usage) =
  match t, t' with 
  | Some u, Some u' -> C.eq_usage u u'
  | None, None -> true
  | _, _ -> false

let eq_opt_label (t: option label) (t': option label) =
  match t, t' with 
  | Some l, Some l' -> eq_label l l'
  | None, None -> True
  | _, _ -> False

val eq_bytes_secrets_have_eq_label_and_usage : t1:C.bytes -> t2:C.bytes -> 
    Lemma (C.eq_bytes t1 t2 ==> eq_opt_label_and_usage (get_label_and_usage_of_secret t1) (get_label_and_usage_of_secret t2))

val eq_bytes_secrets_have_eq_usage : t1:C.bytes -> t2:C.bytes -> Lemma (C.eq_bytes t1 t2 ==> eq_opt_usage (get_usage_of_secret t1) (get_usage_of_secret t2))

val eq_bytes_secrets_have_eq_label : t1:C.bytes -> t2:C.bytes -> Lemma (C.eq_bytes t1 t2 ==> eq_opt_label (get_label_of_secret t1) (get_label_of_secret t2))

(** Get usage predicate of a secret *)
val has_secret_usage_pred: preds -> C.bytes -> u:C.usage -> C.usage_pred u -> Type0

val has_secret_usage_pred_lemma_forall: pr:preds -> 
    Lemma (forall t t' u p. (C.eq_bytes t t' /\ has_secret_usage_pred pr t u p) ==> (has_secret_usage_pred pr t' u p))

(** Get usage predicate of a public_key *)
let has_public_key_usage_pred (pr:preds) (t:C.bytes) (u:C.usage) (p:C.usage_pred u) =
  (exists sk. has_secret_usage_pred pr sk u p /\
	 (u == C.sig_key_usage \/ u == C.pke_key_usage \/ (exists u'. u == C.dh_key_usage u')) /\
	 t == C.pk sk)

val has_public_usage_pred_lemma_forall: pr:preds -> 
    Lemma (forall t t' u p. (C.eq_bytes t t' /\ has_public_key_usage_pred pr t u p) ==> (has_public_key_usage_pred pr t' u p))

val has_secret_usage_pred_for_dh : pr:preds -> k:C.bytes -> pk:C.bytes ->
  Lemma (forall u p. (has_secret_usage_pred pr k (C.dh_key_usage u) (C.dh_usage_pred u p) /\
		has_secret_usage_pred pr pk (C.dh_key_usage u) (C.dh_usage_pred u p) /\ C.is_pk pk) ==>
		has_secret_usage_pred pr (C.dh k pk) u p)

(** Get label and usage of corresponding private key *)
val get_label_and_usage_of_private_key: C.bytes -> option (label * C.usage)

let get_label_of_private_key (t:C.bytes) : option label =
  match get_label_and_usage_of_private_key t with
  | None -> None
  | Some (l,u) -> Some l

let get_usage_of_private_key (t:C.bytes) : option C.usage =
  match get_label_and_usage_of_private_key t with
  | None -> None
  | Some (l,u) -> Some u

val get_label_and_usage_of_private_key_lemma: t:C.bytes ->
  Lemma (forall l u. get_label_and_usage_of_private_key t == Some (l,u) <==>
	 (exists s. t == C.pk s /\ get_label_and_usage_of_secret s == Some (l,u)))
	[SMTPat (get_label_and_usage_of_private_key t)]


/// The following lemmas show that the functions that were just defined return the correct label
/// and usage in case of nonces:

val get_label_of_secret_lemma: t:C.bytes ->
    Lemma (ensures (match get_label_of_secret t with
		    | Some l -> l == get_label t
		    | _ -> True))
          [SMTPat (get_label_of_secret t)]

val get_label_and_usage_of_secret_nonce_lemma: i:nat -> l:label -> u:C.usage ->
    Lemma (ensures (get_label_and_usage_of_secret (C.gnonce i l u) == Some (l,u)))
          [SMTPat (get_label_and_usage_of_secret (C.gnonce i l u))]

val get_usage_of_secret_lemma: i:nat -> l:label -> u:C.usage ->
    Lemma (ensures (get_usage_of_secret (C.gnonce i l u) == Some u))
          [SMTPat (get_usage_of_secret (C.gnonce i l u))]

val get_label_of_secret_bytes_lemma: t:C.bytes -> 
    Lemma (ensures (match get_label_of_secret t with | Some l -> get_label t == l | None -> True))
          [SMTPat (get_label_of_secret t)]

(* Labels can flow to eq_labels *)
val eq_label_can_flow_lemma : l:label -> l':label -> 
    Lemma (ensures (eq_label l l' ==> (forall c. can_flow c l l' /\ can_flow c l' l))) [SMTPat (eq_label l l')]

val eq_label_can_flow_to_lemma : c:T.corrupt_pred -> l:label -> l':label -> l'':label ->
    Lemma (ensures (eq_label l l' /\ can_flow c l l'' ==> can_flow c l' l'')) [SMTPat (eq_label l l'); SMTPat (can_flow c l l'')] 

val can_flow_to_eq_labels_lemma : c:T.corrupt_pred -> l:label -> l':label -> l'':label ->
    Lemma (ensures (can_flow c l l' /\ eq_label l' l'' ==> can_flow c l l'')) [SMTPat (eq_label l' l''); SMTPat (can_flow c l l')] 

val eq_usage_ae_lemma : u:C.usage -> Lemma (requires (u == C.ae_key_usage)) (ensures (forall u'. C.eq_usage u u' ==> u' == C.ae_key_usage))

val eq_usage_dh_ae_lemma : u:C.usage -> Lemma (requires (u == C.dh_key_usage C.ae_key_usage)) (ensures (forall u'. C.eq_usage u u' ==> u' == C.dh_key_usage C.ae_key_usage))

val eq_usage_pke_lemma : u:C.usage -> Lemma (requires (u == C.pke_key_usage)) (ensures (forall u'. C.eq_usage u u' ==> u' == C.pke_key_usage))

val readable_label_equals_can_read : i:principal -> 
    Lemma (ensures (readable_by ({issuers=[];readers=[any i]}) == can_read [any i])) 

val eq_label_means_equal_readers : i:principal -> 
    Lemma (ensures (forall l. eq_label l (readable_by ({issuers=[];readers=[any i]})) ==> 
				  (l == (readable_by ({issuers=[];readers=[any i]}))))) 

val eq_label_means_equal_join_readers : i:principal -> j:principal ->
    Lemma (ensures (forall l. eq_label l (join (can_read [any i]) (can_read [any j])) ==> 
		   (l == (join (can_read [any i]) (can_read [any j])) \/ 
		     l == (join (can_read [any j]) (can_read [any i]))))) 

val generated_secret_usage_pred_lemma: pr:preds -> i:nat -> l:label -> u:C.usage -> p:C.usage_pred u  ->
    Lemma (ensures (pr.model.is_generated i (C.gnonce i l u) l u p ==>  has_secret_usage_pred pr (C.gnonce i l u) u p))
          [SMTPat (has_secret_usage_pred pr (C.gnonce i l u) u p)]

val unique_secret_usage_pred_lemma_forall: pr:preds -> t:C.bytes -> t':C.bytes ->
    Lemma (forall u p u' p'. (C.eq_bytes t t' /\ has_secret_usage_pred pr t u p /\ has_secret_usage_pred pr t' u' p') ==>
			(u == u' /\ p == p'))

val unique_secret_usage_pred_lemma: pr:preds -> t:C.bytes -> t':C.bytes -> 
				    u:C.usage -> p:C.usage_pred u ->
				    u':C.usage -> p':C.usage_pred u' ->
    Lemma ((C.eq_bytes t t' /\ has_secret_usage_pred pr t u p /\ has_secret_usage_pred pr t' u' p') ==>
	   (u == u' /\ p == p'))
	  [SMTPat (has_secret_usage_pred pr t u p);
	   SMTPat (has_secret_usage_pred pr t' u' p')]

val unique_public_key_usage_pred_lemma_forall: pr:preds -> t:C.bytes -> t':C.bytes ->
    Lemma (forall u p u' p'. (C.eq_bytes t t' /\ has_public_key_usage_pred pr t u p /\ has_public_key_usage_pred pr t' u' p') ==>
			(C.eq_usage u u' /\ p == p'))

val extracted_secret_usage_pred_lemma: pr:preds -> k:C.bytes -> c:C.bytes ->
				      l:label -> u:C.usage -> u':C.usage ->
				      p:C.usage_pred u  -> p':C.usage_pred u' ->
    Lemma (requires (
	  let ku = C.kdf_usage (l,u) u' in
	  let kup: C.usage_pred ku = C.kdf_usage_pred l u u' p p' in
	  has_secret_usage_pred pr k ku kup))
	  (ensures (has_secret_usage_pred pr (C.kdf k c true) u p))
          [SMTPat (has_secret_usage_pred pr (C.kdf k c true) u p);
	   SMTPat (has_secret_usage_pred pr k (C.kdf_usage (l,u) u') (C.kdf_usage_pred l u u' p p'))]

val expanded_secret_usage_pred_lemma: pr:preds -> k:C.bytes -> c:C.bytes ->
				      l:label -> u:C.usage -> u':C.usage ->
				      p:C.usage_pred u  -> p':C.usage_pred u' ->
    Lemma (requires (
      let ku = C.kdf_usage (l,u) u' in
      let kup: C.usage_pred ku = C.kdf_usage_pred l u u' p p' in
      has_secret_usage_pred pr k ku kup))
          (ensures (has_secret_usage_pred pr (C.kdf k c false) u' p'))
          [SMTPat (has_secret_usage_pred pr (C.kdf k c false) u' p');
	   SMTPat (has_secret_usage_pred pr k (C.kdf_usage (l,u) u') (C.kdf_usage_pred l u u' p p'))]

(**
   The main function of this predicate is to check whether in case of a KDF usage, the new label is
   'larger' than or equal to the old label, i.e., we can go from less public labels to more public
   labels.
   For this, it is checked if the new label [can_flow] to the old label. This must also hold true
   recursively for the labels and usages of both expand and extract.

   In all other cases, this predicate is True.
*)
val are_kdf_labels_increasing: T.corrupt_pred -> label -> C.usage -> Type0
// When generating a fresh nonce, you have to label how many times you want to derive from that (so
// deriving REMOVES a layer of KDF usage, NOT ADD one).  So this thing is about the "right"
// combination of labels and usages. This is an invariant on label/usage: When you follow these
// rules at generation time, it will stay true.

(** 
   Lemma stating that for every usage except for kdf_usage, are_kdf_labels_increasing is true (i.e., for
   pke_key_usage, ae_key_usage, mac_key_usage, sig_key_usage, nonce_usage, guid_usage).
*)
val are_kdf_labels_increasing_lemma1: pr:T.corrupt_pred -> l:label ->
  Lemma (ensures (are_kdf_labels_increasing pr l C.pke_key_usage /\
                  are_kdf_labels_increasing pr l C.ae_key_usage /\
                  are_kdf_labels_increasing pr l C.mac_key_usage /\
                  are_kdf_labels_increasing pr l C.sig_key_usage /\
                  are_kdf_labels_increasing pr l C.nonce_usage /\
                  are_kdf_labels_increasing pr l C.guid_usage))
        [SMTPatOr [[SMTPat (are_kdf_labels_increasing pr l C.pke_key_usage)];
                   [SMTPat (are_kdf_labels_increasing pr l C.ae_key_usage)];
                   [SMTPat (are_kdf_labels_increasing pr l C.mac_key_usage)];
                   [SMTPat (are_kdf_labels_increasing pr l C.sig_key_usage)];
                   [SMTPat (are_kdf_labels_increasing pr l C.nonce_usage)];
                   [SMTPat (are_kdf_labels_increasing pr l C.guid_usage)]]]

(** 
   Lemma stating the main property of are_kdf_labels_increasing regarding kdf_usage (see also the
   description of are_kdf_labels_increasing above).
*)
val are_kdf_labels_increasing_lemma2: pr:T.corrupt_pred -> l:label -> extract_label:label -> extract_usage:C.usage -> expand_usage:C.usage ->
  Lemma (requires (
          can_flow pr extract_label l) /\ 
          are_kdf_labels_increasing pr extract_label extract_usage /\ 
          are_kdf_labels_increasing pr l expand_usage)
        (ensures (are_kdf_labels_increasing pr l (C.kdf_usage (extract_label,extract_usage) expand_usage)))
        [SMTPat (are_kdf_labels_increasing pr l (C.kdf_usage (extract_label,extract_usage) expand_usage))]

(** 
   Lemma stating the main property of are_kdf_labels_increasing regarding dh_key_usage 
*)
val are_kdf_labels_increasing_lemma3: pr:T.corrupt_pred -> l:label -> u:C.usage ->
  Lemma (requires (are_kdf_labels_increasing pr l u))
        (ensures (are_kdf_labels_increasing pr l (C.dh_key_usage u)))
        [SMTPat (are_kdf_labels_increasing pr l u)]

val are_kdf_labels_increasing_lemma4: pr:T.corrupt_pred -> l:label -> u:C.usage ->
  Lemma (requires (are_kdf_labels_increasing pr l (C.dh_key_usage u)))
	(ensures (are_kdf_labels_increasing pr l u))
        [SMTPat (are_kdf_labels_increasing pr l (C.dh_key_usage u))]
(**
   Given the tuple of predicates preds, bytes t is valid if:

     1) Each component of the bytes t is valid

     2) Nonce: was generated and has a valid usage/label pair (according to are_kdf_labels_increasing)

     3) Literal: always valid

     4) Encryption:
       the key has the wrong usage: both the label of the msg and key flow to Public
       the label of the message must flow to the label of the key (intution: Everyone allowed to know the key must also be allowed to know the plaintext/message)
       the key has the correct usage: if the key is readable by some principal, then the corresponding predicate in preds
                        must hold true for the principal and the message (for PKEnc: or the label of the msg can_flow to Public)

     5) Signature/Mac:
        key has the wrong usage: label of key can flow to public
        key has correct usage: either the signing key flows to public, or if the key is readable by some principal, then the corresponding predicate in preds must hold true for the principal and the message

     6) Derived: If the inner secret has correct KDF labels/usages, see [get_label_and_usage_of_secret], then it is required that these KDF related labels are increasing,
        see [are_kdf_labels_increasing]. Otherwise, it is required that the label of the inner secret can flow to Public.

     7) DH: If the two keys are valid and the private key and public key have same usages, then its label should be increasing.
     
   This predicate is used for enforcing labeling rules (and is also an intermediate definition for [is_labeled]).

   For the crypto primitives, if the usage of the key is wrong, then it is required that this key [can_flow] to Public (i.e., the bytes was constructed by the attacker).

*)
val is_valid_p: preds -> nat -> C.bytes -> Type0

val validity_extends_lemma : pr:preds -> i:nat -> t:C.bytes -> Lemma (forall j. (is_valid_p pr i t /\ i <= j) ==> (is_valid_p pr j t)) 
			     [SMTPat (is_valid_p pr i t)] 
  
val valid_and_eq_bytes_implies_equal : pr:preds -> idx:nat -> t1:C.bytes -> t2:C.bytes ->
    Lemma (requires (is_valid_p pr idx t1 /\ is_valid_p pr idx t2 /\ C.eq_bytes t1 t2))
          (ensures (t1 == t2))
          [SMTPat (C.eq_bytes t1 t2); SMTPat (is_valid_p pr idx t1); SMTPat (is_valid_p pr idx t2)]
(**
   Lemma stating that two bytes that are valid and equal according to eq_bytes also have equal labels and usage defined be eq_label and eq_usage. 
   We do not have syntactic equality because of the symbolic eq_bytes. 
*)
// val valid_and_eq_bytes_implies_equal_labels_and_usage : pr:preds -> idx:nat -> t1:C.bytes -> t2:C.bytes ->
//     Lemma (requires (is_valid_p pr idx t1 /\ is_valid_p pr idx t2 /\ C.eq_bytes t1 t2))
//           (ensures (eq_label (get_label t1) (get_label t2) /\ 
// 		   eq_opt_label_and_usage (get_label_and_usage_of_secret t1) (get_label_and_usage_of_secret t2) /\
// 		   eq_opt_label_and_usage (get_label_and_usage_of_private_key t1) (get_label_and_usage_of_private_key t2)))
//           [SMTPat (C.eq_bytes t1 t2); SMTPat (is_valid_p pr idx t1); SMTPat (is_valid_p pr idx t2)]

val eq_bytes_has_secret_usage_pred_lemma : pr:preds -> idx:nat -> t:C.bytes -> t':C.bytes ->
    Lemma (requires (C.eq_bytes t t' /\ is_valid_p pr idx t /\ is_valid_p pr idx t'))
	  (ensures (forall u p. has_secret_usage_pred pr t u p ==> has_secret_usage_pred pr t' u p))
	  [SMTPat (C.eq_bytes t t'); SMTPat (is_valid_p pr idx t); SMTPat (is_valid_p pr idx t')]

// val eq_bytes_implies_validity : pr:preds -> idx:nat -> t1:C.bytes -> t2:C.bytes ->
//     Lemma (requires (is_valid_p pr idx t1 /\ C.eq_bytes t1 t2))
//           (ensures (is_valid_p pr idx t2))
//           [SMTPat (C.eq_bytes t1 t2); SMTPat (is_valid_p pr idx t1)]

// val eq_bytes_implies_validity_forall : pr:preds -> idx:nat -> t1:C.bytes -> 
//     Lemma (requires (is_valid_p pr idx t1))
//           (ensures (forall t2. C.eq_bytes t1 t2 ==> is_valid_p pr idx t2 /\ (eq_label (get_label t1) (get_label t2) /\ 
// 		   eq_opt_label_and_usage (get_label_and_usage_of_secret t1) (get_label_and_usage_of_secret t2) /\
// 		   eq_opt_label_and_usage (get_label_and_usage_of_private_key t1) (get_label_and_usage_of_private_key t2))))


(**
   True iff bytes is valid (via [is_valid_p]) and has the given label. 

   This is the main labeling relation. Either the bytes is valid, or we don't care about its label.
   From this, it follows that labels are injective (because we don't care about "invalid"
   bytes).
*)
let is_labeled_p preds idx bytes label = is_valid_p preds idx bytes /\ eq_label (get_label bytes) label

(**
  True iff the bytes t is valid and has a label that can flow to the label l.
*)
let can_label_of_bytes_flow_to (pr:preds) (idx:nat) (t:C.bytes) (l:label) = exists l'. is_labeled_p pr idx t l' /\ can_flow (pr.model.corrupt_at idx) l' l

(**
  True iff the bytes t is valid and the given label can flow to the label of t.
*)
let can_label_of_bytes_flow_from (pr:preds) (idx:nat) (t:C.bytes) (l:label) = exists l'. is_labeled_p pr idx t l' /\ can_flow (pr.model.corrupt_at idx) l l'

(*
val label_is_still_valid_with_more_corruption: c1:preds -> c2:preds -> idx:nat -> t:C.bytes -> l:label ->
    Lemma (requires (corrupt_entry_is_extended c1 c2 /\ is_labeled_p c1 idx t l))
          (ensures (is_labeled_p c2 idx t l))
          [SMTPat (corrupt_entry_is_extended c1 c2); SMTPat (is_labeled_p c1 idx t l)]
*)

(**
  True iff the bytes t is valid and has a label that can flow to Public.
*)
let is_publishable_p c idx t = can_label_of_bytes_flow_to c idx t public

(*
val extended_corrupt_entry_does_not_change_publishability: c1:preds -> c2:preds -> idx:nat -> t:C.bytes ->
    Lemma (requires (corrupt_entry_is_extended c1 c2 /\ is_publishable_p c1 idx t))
          (ensures (is_publishable_p c2 idx t))
          [SMTPat (corrupt_entry_is_extended c1 c2); SMTPat (is_publishable_p c1 idx t)]
*)

val injective_labels: c:preds -> idx:nat -> t:C.bytes -> l1:label -> l2:label ->
  Lemma (requires (is_labeled_p c idx t l1 /\ is_labeled_p c idx t l2))
        (ensures (eq_label l1 l2))

(**
  Lemma to show that bytes that are equal and valid are publishable if either of them is publishable (visible to public attacker)
*)
// val valid_and_eq_bytes_are_publishable : pr:preds -> idx:nat -> t1:C.bytes -> t2:C.bytes ->
//   Lemma (requires (is_valid_p pr idx t1 /\ is_valid_p pr idx t2 /\ C.eq_bytes t1 t2))
//         (ensures (is_publishable_p pr idx t1 <==> is_publishable_p pr idx t2))
//         [SMTPat (C.eq_bytes t1 t2); SMTPat (is_valid_p pr idx t1); SMTPat (is_valid_p pr idx t2)]

/// Lemmas about labeling

/// The following lemmas are needed to show that the Attacker API is well typed. They are basically helper lemmas exposing properties of the labeling rules.

val labeled_nonce_forall : pr:preds ->
  Lemma (forall i l u p. (pr.model.is_generated i (C.gnonce i l u) l u p /\ are_kdf_labels_increasing (pr.model.corrupt_at i) l u) ==> is_labeled_p pr i (C.gnonce i l u) l)

val labeled_nonce_public_forall : pr:preds ->
  Lemma (forall i u p. pr.model.is_generated i (C.gnonce i public u) public u p /\ C.is_pub_usage u ==> is_labeled_p pr i (C.gnonce i public u) public)

(**
   Lemma stating that if two bytes are publishable (i.e., can flow to Public), then
   the concatenation of the bytes is also publishable.
*)
val concatenation_of_publishable_bytes_is_publishable_forall : c:preds ->
  Lemma (forall i t1 t2. (is_publishable_p c i t1 /\ is_publishable_p c i t2) ==>
                  is_publishable_p c i (C.concat t1 t2))
(**
   Lemma stating that concatenation_of_publishable_bytes_is_publishable_forall is true under any preds
*)
val concatenation_of_publishable_bytes_is_publishable_forall_under_any_preds : t1:C.bytes -> t2:C.bytes ->
  Lemma (forall i c . (is_publishable_p c i t1 /\ is_publishable_p c i t2) ==>
                  is_publishable_p c i (C.concat t1 t2))

(**
  Lemma stating that literals are publishable.
*)
val literals_are_publishable_forall : c:preds ->
  Lemma (forall i (s:C.literal). is_publishable_p c i (C.literal_to_bytes s))

(**
  Lemma stating that if bytes that can be splitted up is publishable, than each component is also publishable.
*)
val splittable_bytes_publishable_implies_components_publishable_forall: c:preds ->
  Lemma (forall i t t_part1 t_part2. (is_succ2 (C.split t) t_part1 t_part2 /\ is_publishable_p c i t) ==>
                     (is_publishable_p c i t_part1 /\ is_publishable_p c i t_part2))


val concatenation_publishable_implies_components_publishable: c:preds -> i:nat -> t1:C.bytes -> t2:C.bytes ->
  Lemma ((is_publishable_p c i (C.concat t1 t2)) ==> (is_publishable_p c i t1 /\ is_publishable_p c i t2))
  [SMTPat (is_publishable_p c i (C.concat t1 t2))]

(**
   Lemma stating that if the concatenation of two bytes is publishable (i.e., can flow to Public),
   then both bytes are publishable.
*)
val concatenation_publishable_implies_components_publishable_forall : c:preds ->
  Lemma (forall i t1 t2. (is_publishable_p c i (C.concat t1 t2)) ==> (is_publishable_p c i t1 /\ is_publishable_p c i t2))

(**
  Lemma stating that public keys are publishable if their corresponding private keys are publishable.
*)
val public_key_is_publishable_if_private_key_is_publishable_forall : c:preds ->
  Lemma (forall i t. is_publishable_p c i t  ==> is_publishable_p c i (C.pk t))


(**
  Lemma stating that a ciphertext (created by [pke_enc]) is publishable if the key and msg are publishable.
*)
val pke_ciphertext_publishable_if_key_and_msg_are_publishable_forall: c:preds ->
  Lemma (forall i pub_key msg. (is_publishable_p c i pub_key /\ is_publishable_p c i msg) ==>
                  (is_publishable_p c i (C.pke_enc pub_key msg)))

(**
  Lemma stating that a plaintext (created by [pke_dec]) is publishable if both the private key and ciphertext are publishable.
*)
val pke_plaintext_publishable_if_key_and_ciphertext_publishable_forall: c:preds ->
  Lemma (forall i priv_key ciphertext plaintext. (is_succ (C.pke_dec priv_key ciphertext) plaintext /\ is_publishable_p c i priv_key /\ is_publishable_p c i ciphertext) ==>
                      is_publishable_p c i plaintext)

(**
  Lemma stating that a ciphertext (created by [sym_enc]) is publishable if the key and msg are publishable.
*)
val sym_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall: c:preds ->
  Lemma (forall i key msg. (is_publishable_p c i key /\ is_publishable_p c i msg) ==>
                  (is_publishable_p c i (C.aead_enc key msg None)))

(**
  Lemma stating that a plaintext (created by [sym_dec]) is publishable if both the private key and ciphertext are publishable.
*)
val sym_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall: c:preds ->
  Lemma (forall i key ciphertext plaintext. (is_succ (C.aead_dec key ciphertext None) plaintext /\ is_publishable_p c i key /\ is_publishable_p c i ciphertext) ==>
                     is_publishable_p c i plaintext)

(**
  Lemma stating that a ciphertext (created by [aead_enc]) is publishable if the key, msg and ad are publishable.
*)
val aead_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall: c:preds ->
  Lemma (forall i key msg ad. (is_publishable_p c i key /\ is_publishable_p c i msg /\ is_publishable_p c i ad) ==>
                  (is_publishable_p c i (C.aead_enc key msg (Some ad))))

(**
  Lemma stating that a plaintext (created by [aead_dec]) is publishable if both the private key and ciphertext are publishable.
*)
val aead_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall: c:preds ->
  Lemma (forall i key ciphertext plaintext ad. (is_succ (C.aead_dec key ciphertext (Some ad)) plaintext /\ is_publishable_p c i key /\ is_publishable_p c i ciphertext /\ is_publishable_p c i ad) ==>
                     is_publishable_p c i plaintext)

(**
  Lemma stating that if a key and a message is publishable, then the signature created by these values is also publishable.
*)
val sig_is_publishable_if_key_and_msg_are_publishable_forall: c:preds ->
  Lemma (forall i t1 t2. (is_publishable_p c i t1 /\ is_publishable_p c i t2) ==>
                   is_publishable_p c i (C.sign t1 t2))

(**
  Lemma stating that if a message is publishable, then the CEOgen created by it is also publishable.
*)
val ceo_is_publishable_if_msg_is_publishable_forall: c:preds ->
  Lemma (forall i t. (is_publishable_p c i t) ==>
                   is_publishable_p c i (C.ceo_gen t))

(**
  Lemma stating that if a key and a message is publishable, then the DEOgen created by these values is also publishable.
*)
val deo_is_publishable_if_key_and_msg_are_publishable_forall: c:preds ->
  Lemma (forall i t1 t2. (is_publishable_p c i t1 /\ is_publishable_p c i t2) ==>
                   is_publishable_p c i (C.deo_gen t1 t2))

(**
  Lemma stating that if a key and a message is publishable, then the MAC tag is also publishable.
*)
val mac_is_publishable_if_key_and_msg_are_publishable_forall: c:preds ->
  Lemma (forall i t1 t2. (is_publishable_p c i t1 /\ is_publishable_p c i t2) ==>
                   is_publishable_p c i (C.mac t1 t2))

(**
  Lemma stating that if both the secret and the context are publishable, then the derived secret is also publishable.
*)
val derived_value_publishable_if_secret_and_context_are_publishable_forall: c:preds ->
  Lemma (forall i t1 t2 b. (is_publishable_p c i t1 /\ is_publishable_p c i t2) ==>
                   is_publishable_p c i (C.kdf t1 t2 b))

(**
  Lemma stating that if the secret and public keys are publishable, then the DH nonce is also publishable.
*)
val dh_is_publishable_if_keys_are_publishable_forall: c:preds ->
  Lemma (forall i (t1:C.bytes) (t2:C.bytes). (is_publishable_p c i t1 /\ is_publishable_p c i t2 /\ C.is_pk t2) ==>
                   is_publishable_p c i (C.dh t1 t2))
		   
/// Labeled Bytes
/// -------------
///
/// An [lbytes_p] is basically bytes that is labeled.
/// Here, this type is parametric (hence, the '_p' suffix). This will be instantiated at the application level
/// (i.e., without '_p').
/// 
/// .. _labeled_crypto_lbytes_p:
/// 

type lbytes_p (p:preds) (i:nat) (l:label) = t:C.bytes{is_labeled_p p i t l}


/// Maybe a subsection?
/// ~~~~~~~~~~~~~~~~~~~
/// 

// In the following, we will define subsets of bytes parametric in pred - this is what _p means. Later, we define types that describe bytes which are in this subset. From the protocol point of view, we never use these _p types, because there, we actually know the preds.

(**
   Predicate that is true iff the bytes is labeled with l and has the given usage u.

   Also, if 'u' is a KDF usage, it is required that the new label defined inside of the usage is
   'larger' than or equal to the old label l.

   This also requires that t is either a nonce or a derived secret (otherwise,
   [get_usage_of_secret] returns None.)
*)
let is_secret_p (p:preds) (i:nat) (t:C.bytes) (l:label) (u:C.usage) (up:C.usage_pred u) =
  is_labeled_p p i t l /\
  are_kdf_labels_increasing (p.model.corrupt_at i) l u /\
  (get_usage_of_secret t == Some u) /\
  has_secret_usage_pred p t u up

(**
  Returns true iff the bytes t is labeled with l and has the usage
  [PKE], i.e., the bytes is intended to be used as a private key for public key cryptography. (See
  also [is_secret_p] for more details.)
*)
let is_private_dec_key_p (p:preds) (i:nat) (t:C.bytes) (l:label) (up:C.usage_pred C.pke_key_usage) = is_secret_p p i t l C.pke_key_usage up

(**
  Returns true iff the bytes t is labeled with l and has the usage
  [SIG], i.e., the bytes is intended to be used as a signing key. (See also [is_secret_p] for more
  details.)
*)
let is_sign_key_p (p:preds) i (t:C.bytes) (l:label) (up: C.usage_pred C.sig_key_usage) = is_secret_p p i t l C.sig_key_usage up

(**
  Returns true iff the bytes t is labeled with l and has the usage
  [AE], i.e., the bytes is intended to be used as a key for authenticated encryption. (See also
  [is_secret_p] for more details.)
*)
let is_ae_key_p (p:preds) i (t:C.bytes) (l:label) (up: C.usage_pred C.ae_key_usage) = is_secret_p p i t l C.ae_key_usage up

(**
  Returns true iff the bytes t is labeled with l and has the usage [MAC], i.e., the bytes is intended to be used as a key creating MACs. (See also [is_secret_p] for more details.)
*)
let is_mac_key_p (p:preds) i (t:C.bytes) (l:label) (up: C.usage_pred C.mac_key_usage) = is_secret_p p i t l C.mac_key_usage up

(**
  Returns true iff the bytes t is labeled with l and has the usage [NONCE]. (See also [is_secret_p] for more details.)
*)
let is_nonce_p (p:preds) i (t:C.bytes) (l:label) = is_secret_p p i t l C.nonce_usage (C.default_usage_pred C.nonce_usage)

(**
  Secrets which have been generated vs. given by somebody else (e.g., the symm key in login example from the client to the server) - after decryption, we know: Either this is a secret or one of the issuers is corrupt and thus the value is public.
*)
let is_issued_secret_p (pr:preds) i (t:C.bytes) (l:label) (u:C.usage) (up:C.usage_pred u) =
  (can_flow (pr.model.corrupt_at i) l public /\ is_publishable_p pr i t) \/ 
  is_secret_p pr i t l u up

let is_issued_private_dec_key_p (p:preds) i (t:C.bytes) (l:label) up =
  is_issued_secret_p p i t l C.pke_key_usage up
let is_issued_ae_key_p (p:preds) i (t:C.bytes) (l:label) up =
  is_issued_secret_p p i t l C.ae_key_usage up
let is_issued_mac_key_p (p:preds) i (t:C.bytes) (l:label) up =
  is_issued_secret_p p i t l C.mac_key_usage up

let is_public_key_p (p:preds) i (t:C.bytes) (l:label) (u:C.usage) up =
  (u == C.pke_key_usage \/ u == C.sig_key_usage) /\
  (exists s. is_secret_p p i s l u up /\ t == C.pk s) /\ // u is usage on corresponding private key (s)
  is_publishable_p p i t // derivable from is_secret

let is_public_enc_key_p (p:preds) i (t:C.bytes) (l:label) up =
  is_public_key_p p i t l C.pke_key_usage up
let is_verify_key_p (p:preds) i (t:C.bytes) (l:label) up =
  is_public_key_p p i t l C.sig_key_usage up
let is_issued_public_key_p (pr:preds) i (t:C.bytes) (l:label) (u:C.usage) up =
  (u == C.pke_key_usage \/ u == C.sig_key_usage) /\
  (can_flow (pr.model.corrupt_at i) l public \/ is_public_key_p pr i t l u up) /\
  is_publishable_p pr i t
let is_issued_public_enc_key_p (p:preds) i (t:C.bytes) (l:label) up =
  is_issued_public_key_p p i t l C.pke_key_usage up
let is_issued_kdf_expandable_p (pr:preds) i (k:C.bytes) (l:label) (u:C.usage) (up:C.usage_pred u) =
    exists l' u' up'. is_issued_secret_p pr i k l (C.kdf_usage (l', u') u) (C.kdf_usage_pred l' u' u up' up)

let is_dh_private_key_p (p:preds) i (t:C.bytes) (l:label) (u:C.usage) up =
    is_secret_p p i t l (C.dh_key_usage u) (C.dh_usage_pred u up)

let is_dh_public_key_p (p:preds) i (t:C.bytes) (l:label) (u:C.usage) up =
   (exists priv. is_dh_private_key_p p i priv l u up /\ C.eq_bytes t (C.pk priv)) /\
   is_publishable_p p i t // derivable from is_secret

/// Maybe a subsection?
/// ~~~~~~~~~~~~~~~~~~~
/// 
// In pi calculus typing systems, we have two kinds of bytes: 1) Payloads/Data of messages, signatures, ... - but never used as keys; might be secret, but never used as keys. These are usually called messages in pi calc. And 2) "channels" or "keys".
type msg_p (p:preds) (i:nat) (l:label) = x:C.bytes{can_label_of_bytes_flow_to p i x l} 
// When talking about secrets, we want to know the exact label; for messages, we don't care, we only want to know where it can flow to.
type secret_p (p:preds) (i:nat) (l:label) (u:C.usage) (up:C.usage_pred u) =
  x:C.bytes{is_secret_p p i x l u up}
type issued_secret_p (p:preds) (i:nat) (l:label) (u:C.usage) (up:C.usage_pred u) =
  x:C.bytes{is_issued_secret_p p i x l u up}
type public_key_p (p:preds) i (l:label) (u:C.usage) up = x:C.bytes{is_public_key_p p i x l u up}
type issued_public_key_p (p:preds) i (l:label) (u:C.usage) up = x:C.bytes{is_issued_public_key_p p i x l u up}
type private_dec_key_p (p:preds) i (l:label) up = secret_p p i l C.pke_key_usage up
type issued_private_dec_key_p (p:preds) i (l:label) up = issued_secret_p p i l C.pke_key_usage up
type public_enc_key_p (p:preds) i (l:label) up = public_key_p p i l C.pke_key_usage up
type issued_public_enc_key_p (p:preds) i (l:label) up = issued_public_key_p p i l C.pke_key_usage up
type ae_key_p (p:preds) i (l:label) up = secret_p p i l C.ae_key_usage up
type issued_ae_key_p (p:preds) i (l:label) up = issued_secret_p p i l C.ae_key_usage up
type sign_key_p (p:preds) i (l:label) up = secret_p p i l C.sig_key_usage up
type verify_key_p (p:preds) i (l:label) up = public_key_p p i l C.sig_key_usage up
type kdf_key_p (p:preds) i (l:label) (ext_l:label) (ext_u:C.usage) (exp_u:C.usage) up1 up2 = secret_p p i l (C.kdf_usage (ext_l,ext_u) exp_u) (C.kdf_usage_pred ext_l ext_u exp_u up1 up2)
type issued_kdf_key_p (p:preds) i (l:label) (ext_l:label) (ext_u:C.usage) (exp_u:C.usage) up1 up2 = issued_secret_p p i l (C.kdf_usage (ext_l,ext_u) exp_u) (C.kdf_usage_pred ext_l ext_u exp_u up1 up2)
type issued_kdf_expandable_p (pr:preds) i (l:label) (u:C.usage) up =
    x:C.bytes{is_issued_kdf_expandable_p pr i x l u up}
type mac_key_p (p:preds) i (l:label) up = secret_p p i l C.mac_key_usage up

type dh_private_key_p (p:preds) i (l:label) u up = x:C.bytes{is_dh_private_key_p p i x l u up}
type dh_public_key_p (p:preds) i (l:label) u up = x:C.bytes{is_dh_public_key_p p i x l u up}
type dh_shared_secret_p (p:preds) i (l:label) (u:C.usage) up = secret_p p i l u up

val labeled_public_is_publishable: #p:preds -> #i:nat -> t:msg_p p i public -> Lemma (is_publishable_p p i t)

val restrict: #pr:preds -> #i:nat -> #l1:label -> t:msg_p pr i l1 -> l2:label{can_flow (pr.model.corrupt_at i) l1 l2} -> t':msg_p pr i l2{t' == t}

/// Cryptographic API

/// Conversion Between Literals and Labeled Bytes

let later earlier later = earlier <= later

val can_flow_later_forall (p:preds):
  Lemma (forall i j l1 l2. (i <= j /\ can_flow (p.model.corrupt_at i) l1 l2) ==>
	            can_flow (p.model.corrupt_at j) l1 l2)

val are_kdf_labels_increasing_later_forall (p:preds) :
  Lemma (forall i j l u. (i <= j /\ are_kdf_labels_increasing (p.model.corrupt_at i) l u) ==>
		    are_kdf_labels_increasing (p.model.corrupt_at j) l u)

val is_secret_later: p:preds -> i:nat -> j:nat -> t:C.bytes -> l:label -> u:C.usage -> up:C.usage_pred u ->
  Lemma ((later i j /\ is_secret_p p i t l u up) ==> is_secret_p p j t l u up)
	[SMTPat (is_secret_p p i t l u up);
	 SMTPat (is_secret_p p j t l u up)]
//	 SMTPat (later i j)]

let is_secret_later_forall (p:preds) :
  Lemma (forall i j t l u up. (later i j /\ is_secret_p p i t l u up) ==> is_secret_p p j t l u up) = ()

val is_labeled_later_forall (p:preds) :
  Lemma (forall i j t l. (i <= j /\ is_labeled_p p i t l) ==> is_labeled_p p j t l)


val can_label_of_bytes_flow_later: p:preds -> i:nat -> j:nat -> t:C.bytes -> l:label ->
  Lemma ((later i j /\ can_label_of_bytes_flow_to p i t l) ==>
	  can_label_of_bytes_flow_to p j t l)
	[SMTPat (can_label_of_bytes_flow_to p i t l);
	 SMTPat (can_label_of_bytes_flow_to p j t l)]
//	 SMTPat (later i j)]

let can_label_of_bytes_flow_later_forall (p:preds) :
  Lemma (forall i j t l. (later i j /\ can_label_of_bytes_flow_to p i t l) ==>
	            can_label_of_bytes_flow_to p j t l) = ()

val pke_pred_later_forall: unit ->
  Lemma (forall i j up t. (i <= j /\ C.pke_pred up i t) ==> C.pke_pred up j t)

val sign_pred_later_forall: unit ->
  Lemma (forall i j up t. (i <= j /\ C.sign_pred up i t) ==> C.sign_pred up j t)

val mac_pred_later_forall: unit ->
  Lemma (forall i j up t. (i <= j /\ C.mac_pred up i t) ==> C.mac_pred up j t)

val ae_pred_later_forall: unit ->
  Lemma (forall i j up t t'. (i <= j /\ C.ae_pred up i t t') ==> C.ae_pred up j t t')

val literal_to_bytes_labeled_lemma: p:preds -> i:nat -> s:C.literal ->
  Lemma (is_labeled_p p i (C.literal_to_bytes s) public)
	[SMTPat (is_labeled_p p i (C.literal_to_bytes s))]

val literal_to_bytes: p:preds -> i:nat -> s:C.literal -> msg_p p i public
val literal_to_bytes_lemma: p:preds -> i:nat -> s:C.literal ->
  Lemma (ensures (literal_to_bytes p i s == C.literal_to_bytes s))
        [SMTPat (literal_to_bytes p i s)]

val bytes_to_literal: #p:preds -> #i:nat -> #l:label -> t:msg_p p i l -> Err C.literal
  (ensures (fun r -> match r with
		  | Success s -> C.bytes_to_literal t == Success s
		  | Error e -> C.bytes_to_literal t == Error e))

val string_to_bytes: p:preds -> i:nat -> s:string -> msg_p p i public
val string_to_bytes_lemma: p:preds -> i:nat -> s:string ->
  Lemma (ensures (forall p. string_to_bytes p i s == C.string_to_bytes s))
        [SMTPat (string_to_bytes p i s)]
val string_to_bytes_lemma2: s:string ->
  Lemma (ensures (forall i p . string_to_bytes p i s == C.string_to_bytes s))
        [SMTPat (C.string_to_bytes s)]

val string_to_bytes_can_flow: s:string ->
  Lemma (ensures (forall pr i l. can_label_of_bytes_flow_to pr i (C.string_to_bytes s) l))
        [SMTPat (C.string_to_bytes s)]

val bytes_to_string: #p:preds -> #i:nat -> #l:label -> t:msg_p p i l ->
	Err string (fun r -> match r with
			  | Error _ -> r == C.bytes_to_string t
			  | Success _ -> r == C.bytes_to_string t)


val nat_to_bytes: p:preds -> i:nat -> s:nat -> msg_p p i public
val nat_to_bytes_lemma: p:preds -> i:nat -> s:nat ->
  Lemma (ensures (nat_to_bytes p i s == C.nat_to_bytes s))
        [SMTPat (nat_to_bytes p i s)]

val bytes_to_nat: #p:preds -> #i:nat -> #l:label -> t:msg_p p i l -> Err nat
    (ensures (fun r -> match r with
		  | Success s -> C.bytes_to_nat t == Success s
		  | Error e -> C.bytes_to_nat t == Error e))

/// (De)Construct labeled tuples

let max i j = if i < j then j else i

val concat_labeled_lemma: #p:preds -> #i:nat -> #l:label -> m1:C.bytes -> m2:C.bytes ->
  Lemma ((can_label_of_bytes_flow_to p i m1 l /\ can_label_of_bytes_flow_to p i m2 l) ==>
	  can_label_of_bytes_flow_to p i (C.concat m1 m2) l)
	  [SMTPat (can_label_of_bytes_flow_to p i (C.concat m1 m2) l)]

val concat: #p:preds -> #i:nat -> #l:label -> msg_p p i l -> msg_p p i l -> msg_p p i l

val concat_lemma: #p:preds -> #i:nat -> #l:label -> t1:msg_p p i l -> t2:msg_p p i l ->
    Lemma (ensures (concat #p #i #l t1 t2 == C.concat t1 t2))
          [SMTPat (concat #p #i #l t1 t2)]

val concat_valid_lemma : pr:preds -> i:nat -> m:C.bytes -> a:C.bytes -> 
		   Lemma (requires (is_valid_p pr i (DY.Crypto.concat m a)))
			 (ensures (is_valid_p pr i m /\ is_valid_p pr i a))
			 [SMTPat (is_valid_p pr i (DY.Crypto.concat m a))]

val split_labeled_lemma: #p:preds -> #i:nat -> #l:label ->
    t:C.bytes ->
    Lemma (
      can_label_of_bytes_flow_to p i t l ==>
      (match C.split t with
       | Error x -> True
       | Success (x,y) -> can_label_of_bytes_flow_to p i x l /\
			 can_label_of_bytes_flow_to p i y l))
       [SMTPat (C.split t);
	SMTPat (can_label_of_bytes_flow_to p i t l)]


val split: #p:preds -> #i:nat -> #l:label -> t:msg_p p i l -> Err (msg_p p i l & msg_p p i l)
		      (ensures (fun r -> match r with
				      | Error x -> C.split t == Error x
				      | Success (x,y) -> C.split t == Success (x,y)))

val split_valid_lemma : (pr:preds) -> (i:nat) -> (t:C.bytes) ->
    Lemma (requires (is_valid_p pr i t)) (ensures (match C.split t with | Success (x,y) -> is_valid_p pr i x /\ is_valid_p pr i y | _ -> True)) 
	  [SMTPat (is_valid_p pr i t); SMTPat (C.split t)]

/// Asymmetric cryptographic primitives

val pk_labeled_lemma: #p:preds -> #i:nat -> #l:label ->
    t:C.bytes ->  Lemma
    (is_labeled_p p i t l ==> is_labeled_p p i (C.pk t) public)
    [SMTPat (is_labeled_p p i t l)]

(** Create a public key (intended for asymmetric encryption) from a private (decryption) key. *)
val pk: #p:preds -> #i:nat -> #l:label -> #up:C.usage_pred C.pke_key_usage -> private_dec_key_p p i l up -> public_enc_key_p p i l up
val pk_lemma: #p:preds -> #i:nat -> #l:label -> #up:C.usage_pred C.pke_key_usage -> s:private_dec_key_p p i l up ->
  Lemma (ensures (pk s == C.pk s))
        [SMTPat (pk s)]


(** Get label of corresponding private key, or return Public if it is not a public key *)
val get_label_of_private_dec_key: C.bytes -> label
val get_label_of_private_dec_key_lemma: p:C.bytes -> Lemma
  (forall pr i l up. is_public_enc_key_p pr i p l up ==> eq_label l (get_label_of_private_dec_key p))
  [SMTPat (get_label_of_private_dec_key p)]
val get_label_of_private_dec_key_eq_lemma : pr:preds -> i:nat -> 
    Lemma (forall p p'. (C.eq_bytes p p' /\ is_valid_p pr i p /\ is_valid_p pr i p') ==>
		      (eq_label (get_label_of_private_dec_key p') (get_label_of_private_dec_key p)))

(** Create a public key (intended for signature verification) from a private (signing) key. *)
val vk: #p:preds -> #i:nat -> #l:label -> #up:C.usage_pred C.sig_key_usage -> sign_key_p p i l up -> verify_key_p p i l up
val vk_lemma: #p:preds -> #i:nat -> #l:label -> #up:C.usage_pred C.sig_key_usage -> s:sign_key_p p i l up ->
  Lemma (ensures (vk s == C.pk s))
        [SMTPat (vk s)]

(**
Create a public key from a private key (without specifying the intended usage of the created public
key: The suffix un means "unknown").
*)


val pk_un: #p:preds -> #i:nat -> #l:label -> s:lbytes_p p i l -> lbytes_p p i public
val pk_un_lemma: #p:preds -> #i:nat -> #l:label -> s:lbytes_p p i l ->
  Lemma (ensures (pk_un #p #i #l s == C.pk s))
        [SMTPat (pk_un s)]


(** Create a DH public key (intended for DH shared secrets) from a private key. *)
val dh_pk: #p:preds -> #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> dh_private_key_p p i l u up -> dh_public_key_p p i l u up
val dh_pk_lemma:  #p:preds -> #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> s:dh_private_key_p p i l u up -> 
  Lemma (ensures (dh_pk s == C.pk s))
        [SMTPat (dh_pk s)]

(** Get label of corresponding DH private key, or return Public if it is not a DH public key *)
val get_label_of_dh_public_key: C.bytes -> C.usage -> label
val get_label_of_dh_public_key_lemma : (p:C.bytes) -> Lemma
  (forall pr i l u up. (is_dh_public_key_p pr i p l u up) ==> eq_opt_label (Some l) (get_label_of_private_key p)) 
val get_usage_of_dh_public_key_lemma : (pr:preds) -> Lemma
  (forall p i l u up. (is_dh_public_key_p pr i p l u up) ==>
		 (eq_opt_usage (get_usage_of_private_key p) (Some (C.dh_key_usage u))))

/// Encryption
/// ..........

val pke_enc_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    pk:C.bytes ->
    msg:C.bytes ->
    Lemma (
    (is_public_enc_key_p pr i pk l up /\
     can_label_of_bytes_flow_to pr i msg l /\
     C.pke_pred up i msg) ==>
     can_label_of_bytes_flow_to pr i (C.pke_enc pk msg) public)
    [SMTPat (is_public_enc_key_p pr i pk l up);
     SMTPat (can_label_of_bytes_flow_to pr i msg l);
     SMTPat (C.pke_pred up i msg)]

(** Asymmetric encryption of bytes [message] using a public (encryption) key [public_key]. *)
val pke_enc:
    #pr:preds ->
    #i:nat -> 
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    public_key:public_enc_key_p pr i l up ->
    message:msg_p pr i l{C.pke_pred up i message} ->
    msg_p pr i public

val pke_enc_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    p:public_enc_key_p pr i l up ->
    m:msg_p pr i l ->
  Lemma (ensures (C.pke_pred up i m ==> pke_enc p m == C.pke_enc p m))
        [SMTPat (pke_enc p m)]

(**
Asymmetric encryption of bytes [message] using a public key [p]. The main difference to [pke_enc]
is that the encryption key is untrusted. The encryptor does not know that it is actually a public
key, or its usage, or the label of its private key.
*)
val pke_enc_un_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    p:C.bytes ->
    message:C.bytes ->
    Lemma (
     (can_label_of_bytes_flow_to pr i p public /\
      can_label_of_bytes_flow_to pr i message l /\
     (is_publishable_p pr i message \/
      (can_flow (pr.model.corrupt_at i) l (get_label_of_private_dec_key p) /\
       (pr.global.pke_un_pred (get_label_of_private_dec_key p) message \/
       (exists up. has_public_key_usage_pred pr p C.pke_key_usage up /\ C.pke_pred up i message)))))
     ==> can_label_of_bytes_flow_to pr i (C.pke_enc p message) public)
    [SMTPat (can_label_of_bytes_flow_to pr i (C.pke_enc p message) public);
     SMTPat (can_label_of_bytes_flow_to pr i  message l)]

     
val pke_enc_un:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    p:msg_p pr i public ->
    message:msg_p pr i l{
      is_publishable_p pr i message \/
      ((can_flow (pr.model.corrupt_at i) l (get_label_of_private_dec_key p)) /\
       (pr.global.pke_un_pred (get_label_of_private_dec_key p) message \/
	(exists up. has_public_key_usage_pred pr p C.pke_key_usage up /\ C.pke_pred up i message)))} ->
    msg_p pr i public

(** Either the plaintext is publishable or we have a "regular" public key encryption. *)
val pke_enc_un_lemma: #pr:preds -> #i:nat -> #l:label -> p:msg_p pr i public -> m:msg_p pr i l ->
  Lemma (ensures ((is_publishable_p pr i m \/
		  ((can_flow (pr.model.corrupt_at i) l (get_label_of_private_dec_key p)) /\
		   (pr.global.pke_un_pred (get_label_of_private_dec_key p) m \/
		    (exists up. has_public_key_usage_pred pr p C.pke_key_usage up /\ C.pke_pred up i m)))) ==>
		   pke_enc_un #pr #i #l p m == C.pke_enc p m))
        [SMTPat (pke_enc_un #pr #i #l p m)]


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

val pke_dec_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    private_key:C.bytes ->
    ciphertext:C.bytes ->
    Lemma (
     (can_label_of_bytes_flow_to pr i ciphertext public /\
      is_private_dec_key_p pr i private_key l up) ==>
      (match C.pke_dec private_key ciphertext with
       | Success p -> can_label_of_bytes_flow_to pr i p l /\
		     (is_publishable_p pr i p \/ C.pke_pred up i p \/ pr.global.pke_un_pred l p)
       | Error s -> True))
    [SMTPat (is_private_dec_key_p pr i private_key l up);
     SMTPat (C.pke_dec private_key ciphertext)]

val pke_dec:
    #pr:preds ->
    #i:nat -> 
    #l:label ->
    #up:C.usage_pred C.pke_key_usage ->
    private_key:private_dec_key_p pr i l up ->
    ciphertext:msg_p pr i public ->
    Err (msg_p pr i l)
    (ensures (fun r -> match r with
         | Success p -> C.pke_dec private_key ciphertext == Success p /\
		       (is_publishable_p pr i p \/ C.pke_pred up i p \/ pr.global.pke_un_pred l p)
         | Error x -> C.pke_dec private_key ciphertext == Error x))

(**
Asymmetric decryption of a ciphertext using an arbitrary bytes as decryption key. This is modeled
such that decryption is only possible using the (one unique) private key matching the public key
used to encrypt. If the ciphertext was encrypted using a different private key or is not a PKE
ciphertext at all, this function returns None.

If decryption succeeds and the plaintext is not publishable, the returned plaintext is guaranteed to
satisfy [pr.pke_pred].
*)

val pke_dec_un_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    k:C.bytes ->
    c:C.bytes ->
    Lemma (
      (is_labeled_p pr i k l /\
       can_label_of_bytes_flow_to pr i c public) ==>
       (match C.pke_dec k c with
         | Success p -> can_label_of_bytes_flow_to pr i p l /\
                    (is_publishable_p pr i p \/ pr.global.pke_un_pred l p \/
		     (exists up j. j <= i /\ has_secret_usage_pred pr k C.pke_key_usage up /\
			    C.pke_pred up j p))
         | Error x -> True))
    [SMTPat (is_labeled_p pr i k l);
     SMTPat (C.pke_dec k c)]

val pke_dec_un:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    k:lbytes_p pr i l ->
    c:msg_p pr i public ->
    Err (msg_p pr i l)
    (ensures (fun r -> match r with
         | Success p -> C.pke_dec k c == Success p /\
                    (is_publishable_p pr i p \/ pr.global.pke_un_pred l p \/
		     (exists up j. j <= i /\ has_secret_usage_pred pr k C.pke_key_usage up /\
			    C.pke_pred up j p))
         | Error x -> C.pke_dec k c == Error x))

/// Signing
/// .......

(**
Create a signature (just the tag) for a message [m] using a signing key [k]. The tag itself does not
reveal the signed message, but carries the same label as the message.
*) 

val sign_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l':label ->
    k:C.bytes ->
    m:C.bytes ->
    Lemma (
      (is_sign_key_p pr i k l up /\
       can_label_of_bytes_flow_to pr i m l' /\
       C.sign_pred up i m) ==> can_label_of_bytes_flow_to pr i (C.sign k m) l')
    [SMTPat(is_sign_key_p pr i k l up);
     SMTPat (can_label_of_bytes_flow_to pr i (C.sign k m) l')]

val sign:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l':label ->
    k:sign_key_p pr i l up ->
    m:msg_p pr i l'{C.sign_pred up i m} ->
    msg_p pr i l'

val sign_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l2:label ->
    k:sign_key_p pr i l1 up ->
    m:msg_p pr i l2 ->
  Lemma (ensures (C.sign_pred up i m ==> sign k m == C.sign k m))
        [SMTPat (sign k m)]

/// Verification of signatures
/// ..........................

(**
Verify a signature tag [s] for a message [m] using the verification key [p]. If verification
succeeds and the signing key (i.e., the private key corresponding to the verification key [p]) is
not known to any corrupted parties, this function guarantees that [m] satisfies [up].
*)

val verify_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l':label ->
    k:C.bytes ->
    m:C.bytes ->
    sg:C.bytes ->
    Lemma (
      (is_verify_key_p pr i k l up /\
       can_label_of_bytes_flow_to pr i m l' /\
       can_label_of_bytes_flow_to pr i sg l' /\
       C.verify k m sg) ==>
	   (can_flow (pr.model.corrupt_at i) l public \/
	    C.sign_pred up i m))
    [SMTPat(is_verify_key_p pr i k l up);
     SMTPat(can_label_of_bytes_flow_to pr i sg l');
     SMTPat (C.verify k m sg)]

val verify:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l2:label ->
    p:verify_key_p pr i l up ->
    m:msg_p pr i l2 ->
    s:msg_p pr i l2 ->
    bool
val verify_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.sig_key_usage ->
    #l2:label ->
    p:verify_key_p pr i l1 up ->
    m:msg_p pr i l2 ->
    s:msg_p pr i l2 ->
  Lemma (ensures (if verify p m s then
            C.verify p m s /\ (can_flow (pr.model.corrupt_at i) l1 public \/ C.sign_pred up i m)
         else (C.verify p m s = false)))
        [SMTPat (verify p m s)]


val verify_un:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    p:msg_p pr i l1 ->
    m:msg_p pr i l2 ->
    s:msg_p pr i l2 ->
    bool


val verify_un_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    p:msg_p pr i l1 ->
    m:msg_p pr i l2 ->
    s:msg_p pr i l2 ->
  Lemma
    (ensures (
      if verify_un p m s then
        C.verify p m s /\
        (forall (ps:secret_intendees) (up:C.usage_pred C.sig_key_usage). is_verify_key_p pr i p (readable_by ps) up ==> (
          contains_corrupt_principal (pr.model.corrupt_at i) ps \/
          C.sign_pred up i m
        ))
      else (C.verify p m s = false)
    ))
    [SMTPat (verify_un p m s)]



/// Authenticated Encryption with (optional) Associated Data
/// ........................................................

let to_opt_bytes #pr #i #l (m:option (msg_p pr i l)) : option C.bytes =
  match m with
  | Some x -> Some x
  | None -> None

(** Symmetric (authenticated) encryption of a message [m] under an encryption key [k] with
    associated data ad *)
val aead_enc_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:C.bytes -> m:C.bytes -> ad:option C.bytes ->
    Lemma (
     (is_ae_key_p pr i k l up /\
      can_label_of_bytes_flow_to pr i m l /\
      (Some? ad ==> can_label_of_bytes_flow_to pr i (Some?.v ad) public) /\
      C.ae_pred up i m ad) ==> can_label_of_bytes_flow_to pr i (C.aead_enc k m ad) public)
    [SMTPat (C.aead_enc k m ad);
     SMTPat (is_ae_key_p pr i k l up)]

val aead_enc:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:ae_key_p pr i l up ->
    m:msg_p pr i l ->
    ad:option (msg_p pr i public){C.ae_pred up i m (to_opt_bytes ad)} ->
    msg_p pr i public
val aead_enc_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:ae_key_p pr i l up ->
    m:msg_p pr i l ->
    ad:option (msg_p pr i public) ->
  Lemma (ensures ((C.ae_pred up i m (to_opt_bytes ad)) ==>
		  aead_enc #pr #i #l k m ad == C.aead_enc k m (to_opt_bytes ad)))
        [SMTPat (aead_enc k m ad)]

(** Symmetric (authenticated) encryption of a message [m] under an untrusted
    encryption key [k] with  associated data ad *)
val aead_enc_un_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    k:C.bytes ->
    m:C.bytes ->
    ad:option C.bytes ->
    Lemma (
     (is_labeled_p pr i k l /\
      can_label_of_bytes_flow_to pr i m l /\
      (Some? ad ==> can_label_of_bytes_flow_to pr i (Some?.v ad) public) /\
      (is_publishable_p pr i k \/
       (exists up. has_secret_usage_pred pr k C.ae_key_usage up /\
	      C.ae_pred up i m ad))) ==>
	can_label_of_bytes_flow_to pr i (C.aead_enc k m ad) public)
      [SMTPat (C.aead_enc k m ad);
       SMTPat (is_labeled_p pr i k l)]

val aead_enc_un:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    k:lbytes_p pr i l ->
    m:msg_p pr i l ->
    ad:option (msg_p pr i public){
      is_publishable_p pr i k \/
      (exists up. has_secret_usage_pred pr k C.ae_key_usage up /\
	     C.ae_pred up i m (to_opt_bytes ad))} ->
    msg_p pr i public

val aead_enc_un_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    k:lbytes_p pr i l ->
    m:msg_p pr i l ->
    ad:option (msg_p pr i public) ->
  Lemma (ensures ((is_publishable_p pr i k \/
		   (exists up . has_secret_usage_pred pr k C.ae_key_usage up /\
			  C.ae_pred up i m (to_opt_bytes ad))) ==>
		  aead_enc_un #pr #i #l k m ad == C.aead_enc k m (to_opt_bytes ad)))
        [SMTPat (aead_enc_un k m ad)]


/// Decryption
/// ..........

(**
Symmetric decryption of a ciphertext using (de-/encryption) key [k]. This is modeled such that
decryption is only possible using the same key as was used to encrypt. If the ciphertext was
encrypted using a different key or is not an AEnc ciphertext at all, this function returns None.

If decryption succeeds and the plaintext is not publishable, the returned plaintext is guaranteed to
satisfy [pr.ae_pred].
*)
val aead_dec_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:C.bytes ->
    ciphertext:C.bytes ->
    ado:option C.bytes ->
    Lemma (
      (is_ae_key_p pr i k l up /\
       can_label_of_bytes_flow_to pr i ciphertext public /\
       (Some? ado ==> can_label_of_bytes_flow_to pr i (Some?.v ado) public)) ==>
       (match C.aead_dec k ciphertext ado with
         | Success p -> can_label_of_bytes_flow_to pr i p l /\
	        (is_publishable_p pr i k \/
		 C.ae_pred up i p ado)
         | Error s -> True))
    [SMTPat (C.aead_dec k ciphertext ado);
     SMTPat (is_ae_key_p pr i k l up)]

val aead_dec:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.ae_key_usage ->
    k:ae_key_p pr i l up ->
    ciphertext:msg_p pr i public ->
    ad:option (msg_p pr i public) ->
    Err (msg_p pr i l)
    (ensures (fun r -> match r with
         | Success p -> C.aead_dec k ciphertext (to_opt_bytes ad) == Success p /\ (is_publishable_p pr i k \/
				    (match (to_opt_bytes ad) with | Some ad -> C.ae_pred up i p (Some ad)
								 | None -> (C.ae_pred up i p None)))
         | Error s -> C.aead_dec k ciphertext (to_opt_bytes ad) == Error s))

(**
Symmetric decryption of a ciphertext using an arbitrary bytes as decryption key. This is modeled such
that decryption is only possible using the same key as was used to encrypt. If the ciphertext was
encrypted using a different key or is not an AEnc ciphertext at all, this function returns
None.

If decryption succeeds and the plaintext is not publishable, the returned plaintext is guaranteed to
satisfy [pr.ae_pred].
*)
val aead_dec_un_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    k:C.bytes -> c:C.bytes -> ad:option C.bytes ->
    Lemma(
      (is_labeled_p pr i k l /\
       can_label_of_bytes_flow_to pr i c public /\
       (Some?ad ==> can_label_of_bytes_flow_to pr i (Some?.v ad) public)) ==>
       (match C.aead_dec k c ad with
         | Success p -> can_label_of_bytes_flow_to pr i p l /\
	 		(is_publishable_p pr i k \/
		          (exists up. has_secret_usage_pred pr k C.ae_key_usage up /\
				 (match ad with
				  | Some ad -> C.ae_pred up i p (Some ad)
				  | None -> C.ae_pred up i p None)))
         | Error s -> True))
    [SMTPat (C.aead_dec k c ad);
     SMTPat (is_labeled_p pr i k l)]
     
val aead_dec_un:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    k:lbytes_p pr i l ->
    c:msg_p pr i public ->
    ad:option (msg_p pr i public) ->
    Err (msg_p pr i l)
    (ensures (fun r -> match r with
         | Success p -> C.aead_dec k c (to_opt_bytes ad) == Success p /\
			 (is_publishable_p pr i k \/
		          (exists up. has_secret_usage_pred pr k C.ae_key_usage up /\
				 (match (to_opt_bytes ad) with | Some ad -> C.ae_pred up i p (Some ad)
							      | None -> (C.ae_pred up i p None))))
         | Error s -> C.aead_dec k c (to_opt_bytes ad) == Error s))

/// MAC
/// .......

(**
Create a MAC (just the tag) for a message [m] using a signing key [k]. The tag itself does not
reveal the  message, but carries the same label as the message.
*)
val mac_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l':label ->
    k:C.bytes -> m:C.bytes ->
    Lemma (
      (is_mac_key_p pr i k l up /\
       can_label_of_bytes_flow_to pr i m l' /\
       C.mac_pred up i m) ==>
       can_label_of_bytes_flow_to pr i (C.mac k m) l')
    [SMTPat (is_mac_key_p pr i k l up);
     SMTPat (C.mac k m);
     SMTPat (can_label_of_bytes_flow_to pr i m l')]

val mac:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l':label ->
    k:mac_key_p pr i l up ->
    m:msg_p pr i l'{C.mac_pred up i m} ->
    msg_p pr i l'
val mac_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l2:label ->
    k:mac_key_p pr i l1 up ->
    m:msg_p pr i l2 ->
  Lemma (ensures (C.mac_pred up i m ==> mac k m == C.mac k m))
        [SMTPat (mac k m)]

/// Verification of MACs
/// ..........................

(**
Verify a MAC tag [s] for a message [m] using the verification key [k]. If verification
succeeds and the key [k] is not known to any corrupted parties, this function guarantees that [m] satisfies [pr.mac_pred]. 
*)
val verify_mac_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l2:label ->
    k:C.bytes -> m:C.bytes -> s:C.bytes ->
    Lemma (
      (is_mac_key_p pr i k l1 up /\
       can_label_of_bytes_flow_to pr i m l2 /\
       can_label_of_bytes_flow_to pr i s l2 /\
       C.verify_mac k m s) ==>
       (can_flow (pr.model.corrupt_at i) l1 public \/
	C.mac_pred up i m))
     [SMTPat (C.verify_mac k m s);
      SMTPat (is_mac_key_p pr i k l1 up);
      SMTPat (can_label_of_bytes_flow_to pr i m l2)]

val verify_mac:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l2:label ->
    k:mac_key_p pr i l up ->
    m:msg_p pr i l2 ->
    s:msg_p pr i l2 ->
    bool
val verify_mac_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #up:C.usage_pred C.mac_key_usage ->
    #l2:label ->
    k:mac_key_p pr i l1 up ->
    m:msg_p pr i l2 ->
    s:msg_p pr i l2 ->
  Lemma (ensures (if verify_mac k m s then
            C.verify_mac k m s /\ (can_flow (pr.model.corrupt_at i) l1 public \/ (C.mac_pred up i m))
         else (C.verify_mac k m s = false)))
        [SMTPat (verify_mac k m s)]

/// Creating DH keys
/// ....................

(** Create a DH shared secret from a DH private and public key *)

val dh_labeled_lemma: #pr:preds -> #i:nat -> #l:label -> #u:C.usage ->
     #up:C.usage_pred u -> #l':label -> priv:C.bytes -> pub:C.bytes ->
     Lemma (
      requires (is_dh_private_key_p pr i priv l u up /\
       is_dh_public_key_p pr i pub l' u up))
       (ensures (is_secret_p pr i (C.dh priv pub) (join l l') u up))
     [SMTPat (C.dh priv pub);
      SMTPat (is_dh_private_key_p pr i priv l u up);
      SMTPat (is_dh_public_key_p pr i pub l' u up)]
      
val dh: #p:preds -> #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> #l':label -> 
	dh_private_key_p p i l u up -> dh_public_key_p p i l' u up -> 
	dh_shared_secret_p p i (join l l') u up
	
val dh_lemma: #p:preds -> #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> #l':label ->
	      k:dh_private_key_p p i l u up ->
	      pk:dh_public_key_p p i l' u up ->
  Lemma (ensures (dh #p #i #l #u #up #l' k pk == C.dh k pk)) [SMTPat (dh k pk)]

(** Create a DH shared secret from a DH private and unstrusted public key *)
val dh_un_labeled_lemma: #p:preds -> #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> 
    k:dh_private_key_p p i l u up -> pk:msg_p p i public ->
    Lemma 
      (C.is_pk pk ==> 
	(let c = C.dh k pk in
        can_label_of_bytes_flow_to p i c l /\
        (match get_label_of_secret c with
	  | Some l' -> l' == (get_label c)
	  | None -> get_label c == public) /\
	(match get_label_and_usage_of_private_key pk with
	  | Some (l', u') ->
	    if C.eq_usage u' (C.dh_key_usage u)
	    then (get_usage_of_secret c == Some u \/ get_usage_of_secret c == C.get_dh_usage u') /\
		 (eq_label (get_label c) (join l l'))
	    else True
	  | None -> True)))
    [SMTPat (C.dh k pk);
     SMTPat (is_dh_private_key_p p i k l u up)]

val dh_un: #p:preds -> #i:nat -> #l:label -> #u:C.usage -> #up:C.usage_pred u -> 
	   k:dh_private_key_p p i l u up ->
	   pk:msg_p p i public -> 
	   Err (lbytes_p p i (get_label (C.dh k pk))) 
	   (ensures (fun r -> match r with
			   | Success c -> (C.is_pk pk /\ c == C.dh k pk /\ can_label_of_bytes_flow_to p i c l /\ 
					 (match get_label_of_secret c with 
					   | Some l' -> l' == (get_label c) 
					   | None -> get_label c == public) /\
					 (match get_label_and_usage_of_private_key pk with 
					   | Some (l', u') -> if C.eq_usage u' (C.dh_key_usage u) then 
								(get_usage_of_secret c == Some u \/ 
								  get_usage_of_secret c == C.get_dh_usage u') /\ 
								(eq_label (get_label c) (join l l'))
							     else True 
					   | None -> True))
			   | Error x -> True))


/// Hashing
/// ...............


val hash_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    m:C.bytes ->
    Lemma (
      can_label_of_bytes_flow_to pr i m l ==>
      can_label_of_bytes_flow_to pr i (C.hash m) l)
    [SMTPat (can_label_of_bytes_flow_to pr i (C.hash m) l)]

val hash:
    #pr:preds ->
    #i:nat ->
    #l:label ->
    m:msg_p pr i l ->
    msg_p pr i l


/// Key derivation
/// ~~~~~~~~~~~~~~

val kdf_extract_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:C.bytes -> context:C.bytes ->
    Lemma (
      (is_secret_p pr i k l1 (C.kdf_usage (l2,u1) u2) (C.kdf_usage_pred l2 u1 u2 up1 up2) /\
       can_label_of_bytes_flow_to pr i context public) ==>
       is_secret_p pr i (C.kdf k context true) l2 u1 up1)
    [SMTPat (is_secret_p pr i k l1 (C.kdf_usage (l2,u1) u2) (C.kdf_usage_pred l2 u1 u2 up1 up2));
     SMTPat (C.kdf k context true)]

val kdf_extract:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_p pr i l1 l2 u1 u2 up1 up2 ->
    context:msg_p pr i public ->
    t:secret_p pr i l2 u1 up1

val kdf_expand_labeled_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:C.bytes -> context:C.bytes ->
    Lemma (
      (is_secret_p pr i k l1 (C.kdf_usage (l2,u1) u2) (C.kdf_usage_pred l2 u1 u2 up1 up2) /\
       can_label_of_bytes_flow_to pr i context public) ==>
       is_secret_p pr i (C.kdf k context false) l1 u2 up2)
    [SMTPat (is_secret_p pr i k l1 (C.kdf_usage (l2,u1) u2) (C.kdf_usage_pred l2 u1 u2 up1 up2));
     SMTPat (C.kdf k context false)]
     
val kdf_expand:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_p pr i l1 l2 u1 u2 up1 up2 ->
    context:msg_p pr i public ->
    t:secret_p pr i l1 u2 up2

val kdf_extract_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_p pr i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_p pr i public ->
    Lemma (ensures (kdf_extract k ctx == C.kdf k ctx true))
    [SMTPat (kdf_extract k ctx)]

val kdf_expand_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_p pr i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_p pr i public ->
    Lemma (ensures (kdf_expand k ctx == C.kdf k ctx false))
    [SMTPat (kdf_expand k ctx)]


val kdf_extract_usage_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_p pr i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_p pr i public ->
    Lemma (ensures (get_usage_of_secret (kdf_extract k ctx) == Some u1))
          [SMTPat (get_usage_of_secret (kdf_extract k ctx))]

val kdf_expand_usage_lemma:
    #pr:preds ->
    #i:nat ->
    #l1:label ->
    #l2:label ->
    #u1:C.usage ->
    #u2:C.usage ->
    #up1:C.usage_pred u1 ->
    #up2:C.usage_pred u2 ->
    k:kdf_key_p pr i l1 l2 u1 u2 up1 up2 ->
    ctx:msg_p pr i public ->
    Lemma (ensures (get_usage_of_secret (kdf_expand k ctx) == Some u2))
          [SMTPat (get_usage_of_secret (kdf_expand k ctx))]

/// Lemmas about labeling
///

val nonce_generated_at_implies_is_labeled:
  pr:preds{pr.model.is_generated == T.is_nonce_generated_at} ->
  n:C.bytes ->
  lbl:label ->
  u:C.usage ->
  up:C.usage_pred u ->
  Lemma
  (ensures (forall i. (T.is_nonce_generated_at i n lbl u up /\ are_kdf_labels_increasing (pr.model.corrupt_at i) lbl u) ==> is_labeled_p pr i n lbl))


val can_flow_to_public_implies_corruption:
  c:T.corrupt_pred ->
  allowed_knowers:secret_intendees ->
  Lemma
  (ensures (can_flow c (readable_by allowed_knowers) public  ==>
	    contains_corrupt_principal c allowed_knowers))
  [SMTPat (can_flow c (readable_by allowed_knowers) public)]
  
val publishable_of_secret_implies_corruption:
  #pr:preds ->
  #i:nat ->
  #l:label ->
  #u:C.usage ->
  #up:C.usage_pred u ->
  s:secret_p pr i l u up ->
  Lemma
  (ensures (is_publishable_p pr i s ==> can_flow (pr.model.corrupt_at i) l public))

val is_private_dec_key_p_later_lemma:
  p:preds ->
  i:nat -> 
  t:C.bytes -> 
  l:label -> 
  up:C.usage_pred C.pke_key_usage ->
  Lemma
  (requires is_private_dec_key_p p i t l up)
  (ensures forall j. later i j ==> is_private_dec_key_p p j t l up)

val is_sign_key_p_later_lemma:
  p:preds -> 
  i:nat -> 
  t:C.bytes -> 
  l:label -> 
  up: C.usage_pred C.sig_key_usage ->
Lemma
  (requires is_sign_key_p p i t l up)
  (ensures forall j. later i j ==> is_sign_key_p p j t l up)

val is_publishable_p_later_lemma:
  p:preds -> 
  idx:nat -> 
  t:C.bytes ->
 Lemma
  (requires is_publishable_p p idx t)
  (ensures forall j. later idx j ==> is_publishable_p p j t)
  [SMTPat (is_publishable_p p idx t)]

val later_is_transitive: i: nat -> j: nat -> k:nat -> 
Lemma
(requires later i j /\ later j k )
(ensures later i k)

val corrupt_at_lemma: i:nat ->
  Lemma (forall j. i <= j ==> extends_corrupt (T.corrupt_at i) (T.corrupt_at j))
  [SMTPat (T.corrupt_at i)]

val corrupt_at_later_lemma: pr:preds -> i:nat ->
  Lemma (forall j. later i j ==> extends_corrupt (pr.model.corrupt_at i) (pr.model.corrupt_at j))
  [SMTPat (pr.model.corrupt_at i)]

val is_verify_key_p_later_lemma:
  p:preds ->
  i:nat -> 
  t:C.bytes -> 
  l:label -> 
  up: C.usage_pred C.sig_key_usage ->
Lemma
 (is_verify_key_p p i t l up ==> (
   forall j. later i j ==> is_verify_key_p p j t l up
 ))
 [SMTPat (is_verify_key_p p i t l up)]


val is_verify_key_p_later_lemma2:
  p:preds ->
  i:nat -> 
  t:C.bytes -> 
  l:label -> 
  up: C.usage_pred C.sig_key_usage ->
Lemma
 (forall j. later i j ==> (
 is_verify_key_p p i t l up ==> is_verify_key_p p j t l up
 ))
 [SMTPat (is_verify_key_p p i t l up)]


val there_is_only_one_owner_of_verify_key:
  pr:preds ->
  i:nat ->
  up1:C.usage_pred C.sig_key_usage ->
  up2:C.usage_pred C.sig_key_usage ->
  (key: C.bytes) ->
  (owner1: principal)->
  (owner2: principal)->
 Lemma
  (requires is_verify_key_p pr i key (readable_by (readers [any owner1])) up1 /\ is_verify_key_p pr i key (readable_by (readers [any owner2])) up2)
  (ensures owner1 = owner2)
  [SMTPat (is_verify_key_p pr i key (readable_by (readers [any owner1])) up1); SMTPat (is_verify_key_p pr i key (readable_by (readers [any owner2])) up2)]

val owner_of_verify_key_is_unique:
  pr:preds ->
  i: nat ->
  up1:C.usage_pred C.sig_key_usage ->
  up2:C.usage_pred C.sig_key_usage ->
  (key: C.bytes) ->
  (sec_intendees: secret_intendees)->
  (owner: principal)->
 Lemma
  (requires is_verify_key_p pr i key (readable_by sec_intendees) up1 /\ is_verify_key_p pr i key (readable_by (readers [any owner])) up2 )
  (ensures sec_intendees = readers [any owner])
  [SMTPat (is_verify_key_p pr i key (readable_by sec_intendees) up1); SMTPat (is_verify_key_p pr i key (readable_by (readers [any owner])) up2)]


val there_is_only_one_owner_of_verify_key_forall:
  pr:preds ->
  i:nat ->
  up:C.usage_pred C.sig_key_usage ->
  (key: C.bytes) ->
  (owner: principal)->
 Lemma
  (requires is_verify_key_p pr i key (readable_by (readers [any owner])) up)
  (ensures forall (p:principal) (up_p:C.usage_pred C.sig_key_usage). is_verify_key_p pr i key (readable_by (readers [any p])) up_p ==> p = owner)

