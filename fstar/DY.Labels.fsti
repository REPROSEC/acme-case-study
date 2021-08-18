/// DY.Labels
/// =========
module DY.Labels
open DY.Principals

/// To speed up the process of proving secrecy-related properties, we use a labeling system. The
/// labels are defined here (at the DY layer) for simplifying the labeling of secrets, however,
/// adherence to the labeling is not required at the DY layer, i.e., we can model insecure protocols
/// on this layer.


(**
A [secret_intendees] contains two lists of [versionid]s: Issuers and readers. The issuers are supposed to be
the [versionid]s which might have issued some value (but are supposed to forget about the value
after issuing it). The readers are the [versionid]s which are "allowed" to read (know) the value.

It might seem confusing to use [versionid]s here, as one might argue that a secret is "known" to or
"intended" for a principal and not just for a specific version of a specific session of said
principal. We use [versionid]s here to enable a fine-grained modeling of corruption (e.g.,
corrupting only a specific version of a session and thereby modeling temporary access of an attacker
to some device - this is important when modeling post-compromise security properties).
*)
type secret_intendees = { 
  issuers: list versionid;
  readers: list versionid
}

(** Creates a [secret_intendees] with issuers [issuers] and readers [readers]. *)
let create_secret_intendees issuers readers: secret_intendees = {issuers = issuers; readers = readers}

(** Creates a [secret_intendees] with an empty issuers list and readers [readers]. *)
let readers readers: secret_intendees = ({issuers = []; readers = readers})

(** Creates a [secret_intendees] with an empty issuers list and readers [any reader]. *)
unfold let reader_any1 reader: secret_intendees = {issuers = []; readers = [any reader]}

(** [l1] is a subset of  [l2] if for each element in [l1], there is an equal element in [l2]. *)
let is_subset (l1:list versionid) (l2:list versionid) =
  forall m. List.Tot.mem m l1 ==> List.Tot.mem m l2

(** 
Given two lists of vsessionids l1 and l2, l1 is_subset of (l1 @ l2).
*)
let list_is_subset_of_concatenated_lists1 (l1:list versionid) (l2:list versionid) :
  Lemma (is_subset l1 (l1 @ l2))
        [SMTPat (is_subset l1 (l1 @ l2))] =
        List.Tot.Properties.append_mem_forall l1 l2

(** 
Given two lists of vsessionids l1 and l2, l1 is_subset of (l2 @ l1).
*)
let list_is_subset_of_concatenated_lists2 (l1:list versionid) (l2:list versionid) :
  Lemma (is_subset l1 (l2 @ l1))
        [SMTPat (is_subset l1 (l2 @ l1))] =
        List.Tot.Properties.append_mem_forall l2 l1

(**
Let l1, l2, and l3 be lists of vsessionids. If l1 is a subset of l2,
and l2 is a subset of l3, then l1 is also a subset of l3.
*)
let subset_is_transitive (l1:list versionid) (l2:list versionid) (l3:list versionid) :
  Lemma (is_subset l1 l2 /\ is_subset l2 l3 ==> is_subset l1 l3)
        [SMTPat (is_subset l1 l2); SMTPat (is_subset l2 l3)] = ()


(**
A label describes the intended "audience" or "allowed knowers" for a value (term). For simple terms,
this might be "this term is intended to be known to the following [vsessionids]"; for concatenated
terms (pairs/tuples), the label is derived from its elements' labels (either via "join", i.e., a
union; or via "meet", i.e., intersection).
*)
val label : Type0

(**
Pretty-printing function for labels
*)
val sprint_versionid: versionid -> string
val sprint_label: label -> string

(** Generates a "public" label. The public label indicates that everyone (including the attacker) is
"allowed" to learn that value. *)
val public: label

(** Generates a label with the given secret_intendees (issuers as well as readers) as "allowed knowers". *)
val readable_by: secret_intendees -> label

(** Creates a [label] with an empty issuers list and readers [readers]. *)
unfold let can_read readers: label = readable_by ({issuers = []; readers = readers})

unfold let readable_by_any1 (reader:principal): label = can_read [any reader]

unfold let readable_by_any2 (reader1:principal) (reader2:principal): label = can_read [any reader1; any reader2]

val readable_by_injective: si:secret_intendees -> si':secret_intendees ->
    Lemma (readable_by si == readable_by si' ==> si == si')
	  [SMTPat (readable_by si); SMTPat (readable_by si')]

let can_read_injective p p' :
  Lemma (can_read [any p] == can_read [any p'] ==>
	 p == p')
	 [SMTPat (can_read [any p]); SMTPat (can_read [any p'])] = ()

(** Label for concatenated terms. Represents a laxer alternative to meet (see below) by combining the
labels via union (if we concatenate two secrets meant for audiences a,b,c and c,d,e with join, we
effectively end up with a secret for audience a,b,c,d,e). *)
val join: label -> label -> label

(** Label for concatenated terms. Represents the intuitive notion, i.e., labels are combined via
intersection (if we concatenate two secrets meant for audiences a,b,c and c,d,e with meet,
we effectively end up with a secret for audience c). *)
val meet: label -> label -> label

(**
We use eq_label for defining equality of labels. Labels are modeled as eqtype disallowing equality checks. 
eq_label should be primarily used within the model, as its usage by principals and the attacker could leak information.
*)
val eq_label : l:label -> l':label -> Type0

val eq_label_reflexive_lemma : l:label -> 
    Lemma (ensures (eq_label l l))
	  [SMTPat (eq_label l l)]
	  
val eq_label_symmetric_lemma : l:label -> l':label -> 
    Lemma (ensures (eq_label l l' ==> eq_label l' l))
	  [SMTPat (eq_label l l')]

val eq_label_transitive_lemma : l:label -> l':label -> l'':label ->
    Lemma (ensures (eq_label l l' /\ eq_label l' l'' ==> eq_label l l''))
	  [SMTPat (eq_label l l'); SMTPat (eq_label l' l'')]

val join_and_meet_preserve_eq_label : l1:label -> l2:label -> l1':label -> l2':label ->
    Lemma (ensures ((eq_label l1 l1' /\ eq_label l2 l2') ==> (eq_label (join l1 l2) (join l1' l2') /\ eq_label (meet l1 l2) (meet l1' l2'))))
    
