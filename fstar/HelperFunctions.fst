/// HelperFunctions
/// ===============
module HelperFunctions

open DY.Crypto
open Helpers
module LC = Labeled.Crypto

(** Convert an [option bytes] to an [option string]. If the bytes is Error or does not represent a
string, None is returned. *)
let str x =
  match x with
  | Some x' -> (
    match DY.Crypto.bytes_to_string x' with
    | Success s -> Some s
    | _ -> None
    )
  | _ -> None


val eq_seq_bytes_i:  t1:Seq.seq bytes -> t2:Seq.seq bytes{Seq.length t1 = Seq.length t2}
  -> i:nat{i <= Seq.length t1}
  -> Tot (r:bool{r <==> (forall j. (j >= i /\ j < Seq.length t1) ==> (eq_bytes (Seq.index t1 j) (Seq.index t2 j)))})
    (decreases (Seq.length t1 - i))
let rec eq_seq_bytes_i t1 t2 i =
  if i = Seq.length t1 then true
  else
    if eq_bytes (Seq.index t1 i) (Seq.index t2 i) then eq_seq_bytes_i t1 t2 (i + 1)
    else false

(** compare list of bytes for pairwise equality *)
val eq_seq_bytes: t1:Seq.seq bytes -> t2:Seq.seq bytes -> bool

let eq_seq_bytes t1 t2 = if Seq.length t1 = Seq.length t2 then eq_seq_bytes_i t1 t2 0 else false

val eq_seq_bytes_reflexive_lemma:
  t:Seq.seq bytes ->
  Lemma (ensures (eq_seq_bytes t t))

let eq_seq_bytes_reflexive_lemma t = ()

val is_seq_bytes_publishable_i:
  #pr: LC.preds ->
  trace_idx:nat ->
  st: Seq.seq bytes ->
  i: nat ->
  Tot (l:Type0 {l <==> (forall j . j >= i /\ j < Seq.length st ==> LC.is_publishable_p pr trace_idx (Seq.index st j))})
  (decreases (Seq.length st - i))

let rec is_seq_bytes_publishable_i #pr trace_idx st i =
  if i >= (Seq.length st) then True
  else LC.is_publishable_p pr trace_idx (Seq.index st i) /\ is_seq_bytes_publishable_i #pr trace_idx st (i+1)

val is_seq_bytes_publishable:
  #pr: LC.preds ->
  trace_idx:nat ->
  st: Seq.seq bytes ->
  l: Type0 {l <==> (forall i . i < Seq.length st ==> LC.is_publishable_p pr trace_idx (Seq.index st i))}

let is_seq_bytes_publishable #pr trace_idx st = is_seq_bytes_publishable_i #pr trace_idx st 0

val is_seq_bytes_pairs_publishable_i:
  #pr: LC.preds ->
  trace_idx:nat ->
  qs: Seq.seq (bytes * bytes) ->
  i: nat ->
  Tot (l:Type0 {l <==> (forall j . j >= i /\ j < Seq.length qs ==> LC.is_publishable_p pr trace_idx (fst (Seq.index qs j)) /\ LC.is_publishable_p pr trace_idx (snd (Seq.index qs j)))})
  (decreases (Seq.length qs - i))

let rec is_seq_bytes_pairs_publishable_i #pr trace_idx st i =
  if i >= (Seq.length st) then True
  else LC.is_publishable_p pr trace_idx (fst (Seq.index st i)) /\ LC.is_publishable_p pr trace_idx (snd (Seq.index st i)) /\ is_seq_bytes_pairs_publishable_i #pr trace_idx st (i+1)

val is_seq_bytes_pairs_publishable:
  #pr: LC.preds ->
  trace_idx:nat ->
  qs: Seq.seq (bytes * bytes) ->
  l: Type0 {l <==> (forall i . i < Seq.length qs ==> LC.is_publishable_p pr trace_idx (fst (Seq.index qs i)) /\ LC.is_publishable_p pr trace_idx (snd (Seq.index qs i)))}

let is_seq_bytes_pairs_publishable #pr trace_idx st = is_seq_bytes_pairs_publishable_i #pr trace_idx st 0

val cons_seq_bytes_with_list: source_list: list bytes -> dest_seq: Seq.seq bytes -> Seq.seq bytes
let rec cons_seq_bytes_with_list source_list dest_seq =
  match source_list with
  | [] -> dest_seq
  | hd::tl ->
    let dest_seq' = Seq.cons hd dest_seq in
    cons_seq_bytes_with_list tl dest_seq'

(**
   Lemma stating that if some bytes is contained in a sequence,
   then the bytes is still contained after applying Seq.cons.
*)
let seq_cons_preserves_previously_contained_elements (#a:Type) (hd:a) (seq:Seq.seq a) (el:a):
    Lemma (Seq.contains seq el ==> Seq.contains (Seq.cons hd seq) el)
    [SMTPat (Seq.contains #a (Seq.cons hd seq) el) ]
    = Seq.Properties.contains_cons hd seq el

val init_seq_with_list :
  #a: Type ->
  source_list: list a ->
  Seq.seq a

let rec init_seq_with_list #a source_list =
  match source_list with
  | [] -> Seq.empty #a
  | hd::tl ->
          let tl_seq = init_seq_with_list tl in
          let result = Seq.cons hd tl_seq in
          Seq.Properties.contains_intro result 0 hd; //Seq.contains result hd
          (* due to seq_cons_preserves_previously_contained_elements, it follows that everything contained in tl_seq
          is also contained in result *)
          result

let init_seq_bytes_with_list = init_seq_with_list

(**
Lemma stating that the ouput sequence has the same length with the input list
*)
let rec init_seq_with_list_length_lemma #a (l:list a) : Lemma
  (Seq.length (init_seq_with_list l) = List.Tot.length l)
  =
  match l with
  | [] -> ()
  | _::tl -> init_seq_with_list_length_lemma tl


(**
  Lemma stating that every bytes contained in a list is also contained in the sequence created by init_seq_with_list.
*)
let rec init_seq_with_list_lemma #a (l:list a) : Lemma (forall el. List.Tot.memP el l ==> Seq.contains (init_seq_with_list l) el)
  = match l with
  | [] -> ()
  | hd::tl ->
          init_seq_with_list_lemma tl;
          let tl_seq = init_seq_with_list tl in
          let result = Seq.cons hd tl_seq in
          Seq.Properties.contains_intro result 0 hd

(**
  Copy of contains_cons for adding SMTPat.
*)
let contains_cons_smtpat (#a:Type) (hd:a) (tl:Seq.seq a) (x:a)
  : Lemma (Seq.contains (Seq.cons hd tl) x
           <==>
           (x==hd \/ Seq.contains tl  x))
   [SMTPat (Seq.contains (Seq.cons hd tl) x)]
  = Seq.contains_cons hd tl x

(**
  Lemma stating that every element contained in a sequence created by init_seq_with_list is also
  contained in the correpsonding list.
*)
let rec init_seq_with_list_sequence_part_of_list (#a:Type) (l:list a) : Lemma (forall el. Seq.contains (init_seq_with_list l) el ==> List.Tot.memP el l)
  =
  let seq = init_seq_with_list l in
  match l with
    | [] -> assert(Seq.length seq = 0); Seq.Properties.lemma_contains_empty #a; assert(forall e. ~(Seq.contains seq e))
  | hd::tl -> init_seq_with_list_sequence_part_of_list tl;
          let tl_seq = init_seq_with_list tl in
          assert(forall el. Seq.contains tl_seq el ==> List.Tot.memP el tl);
          assert(seq == Seq.cons hd tl_seq);
          assert(Seq.contains seq hd ==> List.Tot.memP hd l);
          assert(List.Tot.memP hd l)

(**
  Lemma stating that every bytes contained in a sequence created by init_seq_bytes_with_list is also
  contained in the correpsonding list and vice versa.
*)
let init_seq_with_list_equivalence_of_list_and_sequence (#a:Type) (l:list a) :
  Lemma (forall el. Seq.contains (init_seq_with_list l) el <==> List.Tot.memP el l)
  =
    init_seq_with_list_lemma l;
    init_seq_with_list_sequence_part_of_list l

