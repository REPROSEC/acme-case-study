/// Helpers
/// ===============
module Helpers

/// Redefine the ``b.[i]`` operation for sequences: Access the ``i``th element of sequence ``b``.
let op_String_Access #a b i = Seq.index #a b i

/// Redefine the ``b.[i] <- v`` operation for sequences: Overwrite the ``i``th element of sequence
/// ``b`` with value ``v``.
let op_String_Assignment #a b i v = Seq.upd #a b i v

/// The result type for functions with errors

type result (a:Type) =
  | Success : v:a -> result a
  | Error   : e:string -> result a

//Main goal for the following is for usage in SMTPat and predicate definitions.
(** [x == Some (a,b)] *)
let is_some2 x (a:'a) (b:'b) = x == Some (a,b)
let is_some x (a:'a) = x == Some a

(** [x == Success (a,b)] *)
let is_succ2 x (a:'a) (b:'b) = x == Success (a,b)
let is_succ x (a:'a) = x == Success a


let seq_snoc_length_lemma (#a:Type) (s:Seq.seq a) (x:a):Lemma
  ( forall (i:nat). i < Seq.length (Seq.snoc s x) ==>  i < Seq.length s \/ i = Seq.length s)
  = ()
  
let seq_snoc_length_plus_one_lemma (#a:Type) (s:Seq.seq a) (x:a):Lemma
  (Seq.length (Seq.snoc s x) = Seq.length s + 1)
  = ()

(* 
    An ordering relation on lists of UInt8. It checks if the list of integers in l1 is <= list of integers in l2. 
    Used for defining ordering relation for DH terms that are equivalent. 
*)
let rec list_u8_le (l1:list UInt8.t) (l2:list UInt8.t) : bool = 
  match l1, l2 with 
  | [], _ -> true
  | hd::tl, hd'::tl' -> FStar.UInt8.lte hd hd' && (if (hd = hd') then list_u8_le tl tl' else true)
  | _, _ -> false

(* 
    Show that the ordering relation list_u8_le is a total order, i.e., total, anti-symmetric and transitive 
*)
let rec list_u8_le_totality_lemma (l1:list UInt8.t) (l2:list UInt8.t) : Lemma (ensures (list_u8_le l1 l2 \/ list_u8_le l2 l1)) =
  match l1, l2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> list_u8_le_totality_lemma tl tl'
  | _ -> ()

let rec list_u8_le_anti_symmetry_lemma (l1:list UInt8.t) (l2:list UInt8.t) : Lemma (ensures (list_u8_le l1 l2 /\ list_u8_le l2 l1 ==> l1 = l2)) =
  match l1, l2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> list_u8_le_anti_symmetry_lemma tl tl'
  | _ -> ()

let rec list_u8_le_anti_symm_lemma (l1:list UInt8.t) (l2:list UInt8.t) : Lemma (ensures (list_u8_le l1 l2 /\ l1 <> l2 ==> not (list_u8_le l2 l1))) =
  match l1, l2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> list_u8_le_anti_symm_lemma tl tl'
  | _ -> ()

let rec list_u8_le_transitivity_lemma (l1:list UInt8.t) (l2:list UInt8.t) (l3:list UInt8.t) : 
    Lemma (ensures (list_u8_le l1 l2 /\ list_u8_le l2 l3 ==> list_u8_le l1 l3)) =
  match l1, l2, l3 with 
  | [], _, _ -> ()
  | hd::tl, hd'::tl', hd''::tl'' -> list_u8_le_transitivity_lemma tl tl' tl''
  | _ -> ()

(* 
    An ordering relation on lists of chars. It checks if the list of chars in l1 is <= list of chars in l2. Every char is represented as a UInt32.
    Used for defining ordering relation for DH terms that are equivalent. 
*) 
let rec list_char_le (l1:list String.char) (l2:list String.char) : bool = 
  match l1, l2 with 
  | [], _ -> true
  | hd::tl, hd'::tl' -> FStar.UInt32.lte (FStar.Char.u32_of_char hd) (FStar.Char.u32_of_char hd') && (if (hd = hd') then list_char_le tl tl' else true)
  | _, _ -> false

(* 
    Show that the ordering relation list_u8_le is a total order, i.e., total, anti-symmetric and transitive 
*)
let rec list_char_le_totality_lemma (l1:list String.char) (l2:list String.char) : Lemma (ensures (list_char_le l1 l2 \/ list_char_le l2 l1)) =
  match l1, l2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> list_char_le_totality_lemma tl tl'
  | _ -> ()

let rec list_char_le_anti_symmetry_lemma (l1:list String.char) (l2:list String.char) : Lemma (ensures (list_char_le l1 l2 /\ list_char_le l2 l1 ==> l1 = l2)) =
  match l1, l2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> list_char_le_anti_symmetry_lemma tl tl'
  | _ -> ()

let rec list_char_le_anti_symm_lemma (l1:list String.char) (l2:list String.char) : Lemma (ensures ((list_char_le l1 l2 /\ l1 <> l2) ==> not (list_char_le l2 l1))) =
  match l1, l2 with 
  | [], _ -> ()
  | hd::tl, hd'::tl' -> list_char_le_anti_symm_lemma tl tl'
  | _ -> ()

let rec list_char_le_transitivity_lemma (l1:list String.char) (l2:list String.char) (l3:list String.char) : 
    Lemma (ensures (list_char_le l1 l2 /\ list_char_le l2 l3 ==> list_char_le l1 l3)) =
  match l1, l2, l3 with 
  | [], _, _ -> ()
  | hd::tl, hd'::tl', hd''::tl'' -> list_char_le_transitivity_lemma tl tl' tl''
  | _ -> ()


val is_sub_set:#a:eqtype -> s1:Seq.seq a -> s2:Seq.seq a -> Tot bool 
  (decreases (Seq.length s1))

let rec is_sub_set #a s1 s2 =
  if Seq.length s1 = 0 then 
    true 
  else(
    let hd = Seq.head s1 in
    let tl = Seq.tail s1 in
     Seq.mem hd s2 && is_sub_set tl s2
  )

val is_sub_set_implies_membership: #a:eqtype -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma
  (requires is_sub_set s1 s2)
  (ensures forall x. Seq.mem x s1 ==> Seq.mem x s2)
  (decreases (Seq.length s1))

let rec is_sub_set_implies_membership #a s1 s2 =
  if Seq.length s1 = 0 then ()
  else(
     let tl = Seq.tail s1 in
     is_sub_set_implies_membership #a tl s2
  )

val membership_implies_is_sub_set: #a:eqtype -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma  
  (requires forall x. Seq.mem x s1 ==> Seq.mem x s2)
  (ensures is_sub_set s1 s2)
  (decreases (Seq.length s1))

let rec  membership_implies_is_sub_set #a s1 s2 =
  if Seq.length s1 = 0 then ()
  else(
     let tl = Seq.tail s1 in
     membership_implies_is_sub_set #a tl s2
  )


val is_sub_set_reflexive:#a:eqtype -> s1:Seq.seq a -> Lemma (ensures (is_sub_set s1 s1))


let is_sub_set_reflexive #a s1 = membership_implies_is_sub_set #a s1 s1

val is_sub_set_transitive: #a:eqtype -> s1:Seq.seq a -> s2:Seq.seq a ->s3:Seq.seq a -> Lemma 
 (requires is_sub_set s1 s2 /\ is_sub_set s2 s3)
 (ensures is_sub_set s1 s3)

let is_sub_set_transitive #a s1 s2 s3 = 
  is_sub_set_implies_membership #a s1 s2;
  is_sub_set_implies_membership #a s2 s3;
  membership_implies_is_sub_set #a s1 s3

val is_same_set:#a:eqtype -> s1:Seq.seq a -> s2:Seq.seq a -> bool
(*
the implementation only checks the membership
*)
let is_same_set #a s1 s2 = is_sub_set s1 s2 && is_sub_set s2 s1

val is_same_set_commutative:#a:eqtype -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma 
  (is_same_set s1 s2 <==> is_same_set s2 s1)
  [SMTPat (is_same_set s1 s2)]

let is_same_set_commutative #a s1 s2 = ()

val is_same_set_reflexive: #a:eqtype -> s1:Seq.seq a -> Lemma (is_same_set s1 s1)
  [SMTPat (is_same_set s1 s1)]

let is_same_set_reflexive #a s1 = is_sub_set_reflexive s1

val is_same_set_transitive: #a:eqtype -> s1:Seq.seq a -> s2:Seq.seq a ->s3:Seq.seq a -> Lemma 
 (requires is_same_set s1 s2 /\ is_same_set s2 s3)
 (ensures is_same_set s1 s3)

let is_same_set_transitive #a s1 s2 s3 = 
  is_sub_set_transitive s1 s2 s3;
  is_sub_set_transitive s3 s2 s1
