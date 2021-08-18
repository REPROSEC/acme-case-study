/// DY.Labels (implementation)
/// ==========================
module DY.Labels
open DY.Principals
open Helpers

type label_:eqtype =
  | (* Label for values visible to everyone (including the attacker) *)
    Public: label_
  |(* Label for values "visible" to a limited set of vsessionids. *)
    ReadableBy: secret_intendees -> label_
  |(* Label for concatenated terms. Represents a laxer (can_flow a b is true more often)
    alternative to Meet, i.e., the labels are combined via union (if we concatenate two secrets
    meant for audiences a,b,c and c,d,e with Join, we effectively end up with a secret for
    audience a,b,c,d,e).  *) 
    Join: label_ -> label_ -> label_
  |(* Label for concatenated terms. Represents the intuitive notion, i.e., labels are combined via
    intersection (if we concatenate two secrets meant for audiences a,b,c and c,d,e with Meet,
    we effectively end up with a secret for audience c). *)
    Meet: label_ -> label_ -> label_

let label = label_

/// LESSTHANEQ OPERATIONS
/// ---------------------

(* Define <= relation for versionids; used for proving equality of symbolic DH terms. Uses <= relation on list of chars from Helpers *)
let vi_le (v1:versionid) (v2:versionid) : bool = 
  match v1, v2 with 
  | AnyVersion (AnySession p1), AnyVersion (AnySession p2) -> list_char_le (String.list_of_string p1) (String.list_of_string p2)
  | AnyVersion (AnySession _), _ -> true
  | _, AnyVersion (AnySession _) -> false
  | AnyVersion (Session p1 si1), AnyVersion (Session p2 si2) -> list_char_le (String.list_of_string p1) (String.list_of_string p2) &&
							       (if p1 = p2 then si1 <= si2 else true)
  | AnyVersion (Session _ _), _ -> true
  | _, AnyVersion (Session _ _) -> false
  | Version (AnySession p1) i1, Version (AnySession p2) i2 -> list_char_le (String.list_of_string p1) (String.list_of_string p2) &&
							     (if p1 = p2 then i1 <= i2 else true)
  | Version (AnySession _) _, _ -> true
  | _, Version (AnySession _) _ -> false
  | Version (Session p1 si1) i1, Version (Session p2 si2) i2 -> list_char_le (String.list_of_string p1) (String.list_of_string p2) &&
							       (if p1 = p2 then (si1 <= si2 && (if si1 = si2 then i1 <= i2 else true)) else true)
  | _, _ -> false

(* The <= relation on versionids is a total relation; for any two versionids v1, v2 either v1 <= v2 or v2 <= v1 *)
let vi_le_totality_lemma v1 v2 : Lemma (ensures (vi_le v1 v2 \/ vi_le v2 v1)) [SMTPat (vi_le v1 v2); SMTPat (vi_le v2 v1)] =  
  match v1, v2 with 
  | AnyVersion (AnySession p1), AnyVersion (AnySession p2) -> list_char_le_totality_lemma (String.list_of_string p1) (String.list_of_string p2)
  | AnyVersion (Session p1 si1), AnyVersion (Session p2 si2) -> list_char_le_totality_lemma (String.list_of_string p1) (String.list_of_string p2)
  | Version (AnySession p1) i1, Version (AnySession p2) i2 -> list_char_le_totality_lemma (String.list_of_string p1) (String.list_of_string p2)
  | Version (Session p1 si1) i1, Version (Session p2 si2) i2 -> list_char_le_totality_lemma (String.list_of_string p1) (String.list_of_string p2)
  | _, _ -> ()

(* The <=  relation on versionids is anti-symmetric; if v1 <= v2 and v2 <= v1, then v1 = v2 *)
let vi_le_anti_symmetry_lemma v1 v2 : Lemma (ensures (vi_le v1 v2 /\ vi_le v2 v1 ==> v1 = v2)) [SMTPat (vi_le v1 v2); SMTPat (vi_le v2 v1)] =  
  match v1, v2 with 
  | AnyVersion (AnySession p1), AnyVersion (AnySession p2)
  | AnyVersion (Session p1 _), AnyVersion (Session p2 _) 
  | Version (AnySession p1) _, Version (AnySession p2) _ 
  | Version (Session p1 _) _, Version (Session p2 _) _ -> list_char_le_anti_symmetry_lemma (String.list_of_string p1) (String.list_of_string p2);
							 String.string_of_list_of_string p1; String.string_of_list_of_string p2
  | _, _ -> ()

(* The ordering relation <=  on a list of versionids. Used to show equality of symbolic DH terms *)
let rec lvi_le (v1:list versionid) (v2:list versionid) : bool =
  match v1, v2 with 
  | [], _ -> true
  | hd::tl, hd'::tl' -> vi_le hd hd' && (if hd = hd' then lvi_le tl tl' else true)
  | _, _ -> false

(* the ordering relation <=  on a list of versionids is also total relation *)
let rec lvi_le_totality_lemma (v1:list versionid) (v2:list versionid) : Lemma (lvi_le v1 v2 \/ lvi_le v2 v1) =
  match v1, v2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> vi_le_totality_lemma hd hd'; lvi_le_totality_lemma tl tl' 
  | _, _ -> ()

(* the ordering relation <=  on a list of versionids is also an anti-symmetric relation *)
let rec lvi_le_anti_symmetry_lemma (v1:list versionid) (v2:list versionid) : Lemma (lvi_le v1 v2 /\ lvi_le v2 v1 ==> v1 = v2) =
  match v1, v2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> vi_le_anti_symmetry_lemma hd hd'; lvi_le_anti_symmetry_lemma tl tl' 
  | _, _ -> ()

(* the ordering relation <=  on secret_intendees type *)
let si_le (s1:secret_intendees) (s2:secret_intendees) : bool =
  lvi_le s1.issuers s2.issuers && (if s1.issuers = s2.issuers then lvi_le s1.readers s2.readers else true)

(* the ordering relation <=  on secret_intendees is also a total relation *)
let si_le_totality_lemma (s1:secret_intendees) (s2:secret_intendees) : Lemma (si_le s1 s2 \/ si_le s2 s1) =
  lvi_le_totality_lemma s1.issuers s2.issuers; lvi_le_totality_lemma s1.readers s2.readers 

(* the ordering relation <=  on secret_intendees is an anti-symmetric relation *)
let si_le_anti_symmetry_lemma (s1:secret_intendees) (s2:secret_intendees) : Lemma (si_le s1 s2 /\ si_le s2 s1 ==> s1 = s2) =
  lvi_le_anti_symmetry_lemma s1.issuers s2.issuers; lvi_le_anti_symmetry_lemma s1.readers s2.readers 

(* the ordering relation <=  on labels for showing equality of symbolic DH terms *)
let rec label_le (l1:label) (l2:label) : bool = 
  match l1, l2 with
  | Public, _ -> true
  | _, Public -> false 
  | ReadableBy a, ReadableBy b -> si_le a b
  | ReadableBy a, _ -> true
  | _, ReadableBy b -> false 
  | Join l1 l2, Join l1' l2' -> label_le l1 l1' && (if l1 = l1' then label_le l2 l2' else true)
  | Join l1 l2, _ -> true
  | _, Join l1 l2 -> false 
  | Meet l1 l2, Meet l1' l2' -> label_le l1 l1' && (if l1 = l1' then label_le l2 l2' else true)
  | _, _ -> false 

(* the ordering relation <=  on labels is also total relation *)
let rec label_le_totality_lemma l1 l2 : Lemma (ensures (label_le l1 l2 \/ label_le l2 l1)) [SMTPat (label_le l1 l2); SMTPat (label_le l2 l1)] = 
  match l1, l2 with
  | ReadableBy a, ReadableBy b -> si_le_totality_lemma a b
  | Join l1 l2, Join l1' l2' -> label_le_totality_lemma l1 l1'; label_le_totality_lemma l2 l2'
  | Meet l1 l2, Meet l1' l2' -> label_le_totality_lemma l1 l1'; label_le_totality_lemma l2 l2'
  | _, _ -> ()

(* the ordering relation <=  on labels is also an anti-symmetric relation *)
let rec label_le_anti_symmetry_lemma l1 l2 : Lemma (ensures (label_le l1 l2 /\ label_le l2 l1 ==> l1 = l2)) [SMTPat (label_le l1 l2); SMTPat (label_le l2 l1)] = 
  match l1, l2 with
  | ReadableBy a, ReadableBy b -> si_le_anti_symmetry_lemma a b
  | Join l1 l2, Join l1' l2' -> label_le_anti_symmetry_lemma l1 l1'; label_le_anti_symmetry_lemma l2 l2'
  | Meet l1 l2, Meet l1' l2' -> label_le_anti_symmetry_lemma l1 l1'; label_le_anti_symmetry_lemma l2 l2'
  | _, _ -> ()
  
/// OPERATIONS END
/// ============== 

(** Pretty-print a sessionid *)
let sprint_sessionid (si:sessionid) : string =
  match si with
  | AnySession prin -> prin
  | Session p si -> p^"("^string_of_int si^")"

(** Pretty-print a versionid *)
let sprint_versionid (vi:versionid) : string =
  match vi with
  | AnyVersion si -> sprint_sessionid si
  | Version si v -> sprint_sessionid si^"("^string_of_int v^")"

(** Pretty-print a Label *)
let rec sprint_label l =
  match l with
  | Public -> "Public"
  | ReadableBy si ->
	       (if si.issuers <> [] then
		"["^String.concat ";" (List.Tot.map sprint_versionid si.issuers)^
		" says "
		else "[")^
	       	String.concat ";" (List.Tot.map sprint_versionid si.readers)^"]"
  | Join l1 l2 -> "Join "^sprint_label l1^" "^sprint_label l2
  | Meet l1 l2 -> "Meet "^sprint_label l1^" "^sprint_label l2

(** Returns a iff a>=b. *)
let max (a:nat) (b:nat) = if a >= b then a else b

(**
    Returns the depth of a label. The depth of a 'Public' and 'ReadableBy' label is 0,
    of a 'Join' or 'Meet' label the maximum depth of each label increased by one.
*)
let rec depth (l:label) =
  match l with
  | Public -> 0
  | ReadableBy _ -> 0
  | Join l1 l2 -> 1 + (max (depth l1) (depth l2))
  | Meet l1 l2 -> 1 + (max (depth l1) (depth l2))

let public = Public
let readable_by (issuers_and_readers:secret_intendees) = ReadableBy issuers_and_readers

let readable_by_injective si1 si2 = ()

let join l1 l2 = Join l1 l2
let meet l1 l2 = Meet l1 l2

let rec eq_label l l' =
  match l, l' with 
  | Public, Public -> True
  | ReadableBy a, ReadableBy b -> a == b
  | Join l1 l2, Join l1' l2' 
  | Meet l1 l2, Meet l1' l2' -> (eq_label l1 l1' /\ eq_label l2 l2') \/
			       (eq_label l1 l2' /\ eq_label l2 l1')
  | _, _ -> False

let rec eq_label_reflexive_lemma l =
  match l with 
  | Public -> ()
  | ReadableBy a -> ()
  | Join l1 l2 -> eq_label_reflexive_lemma l1; eq_label_reflexive_lemma l2
  | Meet l1 l2 -> eq_label_reflexive_lemma l1; eq_label_reflexive_lemma l2
  | _ -> ()
  
let rec eq_label_symmetric_lemma l l' = 
  match l, l' with 
  | Public, Public -> ()
  | ReadableBy a, ReadableBy b -> ()
  | Join l1 l2, Join l1' l2' ->
	 eq_label_symmetric_lemma l1 l1'; eq_label_symmetric_lemma l2 l2';
	 eq_label_symmetric_lemma l1 l2'; eq_label_symmetric_lemma l2 l1'
  | Meet l1 l2, Meet l1' l2' -> 
	 eq_label_symmetric_lemma l1 l1'; eq_label_symmetric_lemma l2 l2';
	 eq_label_symmetric_lemma l1 l2'; eq_label_symmetric_lemma l2 l1'
  | _, _ -> ()

let rec eq_label_transitive_lemma l l' l'' = 
  match l, l', l'' with 
  | Public, Public, Public -> ()
  | ReadableBy a, ReadableBy b, ReadableBy c -> ()
  | Join l1 l2, Join l1' l2', Join l1'' l2'' ->
	 eq_label_transitive_lemma l1 l1' l1''; 
	 eq_label_transitive_lemma l2 l2' l2'';
	 eq_label_transitive_lemma l1 l2' l1''; 
	 eq_label_transitive_lemma l2 l1' l2'';
	 eq_label_transitive_lemma l1 l1' l2''; 
	 eq_label_transitive_lemma l2 l2' l1'';
	 eq_label_transitive_lemma l1 l2' l2''; 
	 eq_label_transitive_lemma l2 l1' l1''
  | Meet l1 l2, Meet l1' l2', Meet l1'' l2'' -> 
	 eq_label_transitive_lemma l1 l1' l1''; 
	 eq_label_transitive_lemma l2 l2' l2'';
	 eq_label_transitive_lemma l1 l2' l1''; 
	 eq_label_transitive_lemma l2 l1' l2'';
	 eq_label_transitive_lemma l1 l1' l2''; 
	 eq_label_transitive_lemma l2 l2' l1'';
	 eq_label_transitive_lemma l1 l2' l2''; 
	 eq_label_transitive_lemma l2 l1' l1''
  | _, _, _ -> ()

let join_and_meet_preserve_eq_label l1 l2 l1' l2' = ()

