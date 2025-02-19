/// .. _dy_crypto_impl:
/// 
/// DY.Crypto (implementation)
/// ==========================
module DY.Crypto

open DY.Labels
friend DY.Labels

open Helpers

type usage_:eqtype =
  | PKE: usage_
  | AE: usage_
  | MAC: usage_
  | SIG: usage_
  | (** Usage for key derivation (see HKDF): The tuple is the label and usage assigned to the
        resulting bytes when doing "extract". The single usage_ is the usage assigned when doing
        "expand" (in that case, the label is taken from the next-deeper layer of usages).
        Note that due to how KDF is modeled, the creator of a key already has to specifiy how many
        derivations should be possible - each derivation removes a "layer" of KDF usage from the
        bytes's usage value. *)
    KDF: ((*extract_label*)label_ & (*extract_usage*)usage_) -> (*expand_usage*) usage_ -> usage_
  | NONCE: usage_
  | GUID: usage_
  | DHKey: usage_ -> usage_

(* Ordering on usages; uses the <= ordering on labels defined in DY.Labels *)
let rec usage_le u1 u2 : bool =
  match u1, u2 with
  | PKE, _ -> true
  | _, PKE -> false
  | AE, _ -> true
  | _, AE -> false
  | MAC, _ -> true
  | _, MAC -> false
  | SIG, _ -> true
  | _, SIG -> false
  | KDF (l, u1) u2, KDF (l', u1') u2' -> label_le l l' && (if l = l' then (usage_le u1 u1' && (if u1 = u1' then usage_le u2 u2' else true)) else true)
  | KDF _ _, _ -> true
  | _, KDF _ _ -> false
  | NONCE, _ -> true
  | _, NONCE -> false
  | GUID, _ -> true
  | _, GUID -> false
  | DHKey u1, DHKey u2 -> usage_le u1 u2
  | _, _ -> false

(* The <= ordering on usages is total *)
let rec usage_le_totality_lemma u1 u2 : Lemma (usage_le u1 u2 \/ usage_le u2 u1) =
  match u1, u2 with
  | KDF (l, u1) u2, KDF (l', u1') u2' -> label_le_totality_lemma l l'; usage_le_totality_lemma u1 u1'; usage_le_totality_lemma u2 u2'
  | DHKey u1, DHKey u2 -> usage_le_totality_lemma u1 u2
  | _ -> ()

(* The <= ordering on usages is anti-symmetric *)
let rec usage_le_anti_symmetry_lemma u1 u2 : Lemma (usage_le u1 u2 /\ usage_le u2 u1 ==> u1 = u2) =
  match u1, u2 with
  | KDF (l, u1) u2, KDF (l', u1') u2' -> label_le_anti_symmetry_lemma l l'; usage_le_anti_symmetry_lemma u1 u1'; usage_le_anti_symmetry_lemma u2 u2'
  | DHKey u1, DHKey u2 -> usage_le_anti_symmetry_lemma u1 u2
  | _, _ -> ()


(* Basic definition of what bytes is (in the symbolic model). *)
type bytes_ =
  | Literal: s:literal -> bytes_
  | Concat: bytes_ -> bytes_ -> bytes_
  | Nonce: n:nat -> l:label_ -> u:usage_ -> bytes_
  | (** Public key *)
    PK: secret:bytes_ -> bytes_
  | PKEnc: pk:bytes_ -> msg:bytes_ -> bytes_ // this also provides message integrity
  | (** Key derivation (from a key and a context). The boolean 'extract' records whether extract or expand was done (HKDF) *)
    Derive: k:bytes_ -> ctx:bytes_ -> extract:bool -> bytes_
  | (** Authenticated encryption with (optional) associated data *)
    AEnc: k:bytes_ -> msg:bytes_ -> ad:option bytes_ -> bytes_
  | Sig: sk:bytes_ -> msg:bytes_ -> bytes_
  | CEOgen: sig:bytes_ -> bytes_
  | DEOgen: msg:bytes_ -> sig:bytes_ -> bytes_
  | Mac: k:bytes_ -> msg:bytes_ -> bytes_
  | DH: k1:bytes_ -> k2:bytes_ -> bytes_
  | BadDH: k:bytes_ -> pk:bytes_ -> bytes_
  | Hash: m:bytes_ -> bytes_

(* Ordering on bytes - uses <= relations defined for lists of UInt8, lists of chars, usages and labels.
   The main use of this is to define the equality of bytes when using symbolic bytes like DH, XOR.
*)
let rec bytes_le (t1:bytes_) (t2:bytes_) : bool =
  match t1, t2 with
  | Literal a, Literal b -> (match a, b with
			   | ByteSeq b1, ByteSeq b2 -> list_u8_le (Seq.seq_to_list b1) (Seq.seq_to_list b2)
			   | Nat n1, Nat n2 -> n1 <= n2
			   | String s1, String s2 -> list_char_le (FStar.String.list_of_string s1) (FStar.String.list_of_string s2)
                           | Bool b1, Bool b2 -> b1=b2 || (b1 && (not(b2))) //true <= false
                           | Bool _, _ -> true
                           | ByteSeq _, Bool _ -> false
                           | Nat _, Bool _ -> false
			   | ByteSeq _, _ -> true
			   | Nat _, ByteSeq _ -> false
			   | Nat _, _ -> true
			   | String _, _ -> false)
  | Nonce n1 l1 u1, Nonce n2 l2 u2 -> n1 <= n2 && (if n1 = n2 then (label_le l1 l2 && (if l1 = l2 then usage_le u1 u2 else true)) else true)
  | Concat t1a t1b, Concat t2a t2b -> bytes_le t1a t2a && (if t1a = t2a then bytes_le t1b t2b else true)
  | PK s1, PK s2 -> bytes_le s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> bytes_le pk1 pk2 && (if pk1 = pk2 then bytes_le m1 m2 else true)
  | Derive k1 c1 e1, Derive k2 c2 e2 -> bytes_le k1 k2 && (if k1 = k2 then (bytes_le c1 c2 && (if c1 = c2 then (if e1 = e2 then true else if e1 then true else false) else true)) else true)
  | AEnc k1 m1 None, AEnc k2 m2 None -> bytes_le k1 k2 && (if k1 = k2 then bytes_le m1 m2 else true)
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> bytes_le k1 k2 && (if k1 = k2 then (bytes_le m1 m2 && (if m1 = m2 then bytes_le ad1 ad2 else true)) else true)
  | Sig k1 m1, Sig k2 m2 -> bytes_le k1 k2 && (if k1 = k2 then bytes_le m1 m2 else true)
  | CEOgen sig1, CEOgen sig2 -> bytes_le sig1 sig2
  | DEOgen msg1 sig1, DEOgen msg2 sig2 -> bytes_le msg1 msg2 && (if msg1 = msg2 then bytes_le sig1 sig2 else true)
  | Mac k1 m1, Mac k2 m2 -> bytes_le k1 k2 && (if k1 = k2 then bytes_le m1 m2 else true)
  | DH k1 k1', DH k2 k2' -> bytes_le k1 k2 && (if k1 = k2 then bytes_le k1' k2' else true)
  | BadDH k1 pk1, BadDH k2 pk2 -> bytes_le k1 k2 && (if k1 = k2 then bytes_le pk1 pk2 else true)
  | Hash m1, Hash m2 -> bytes_le m1 m2
  | Literal _, _ -> true
  | Nonce _ _ _, Literal _ -> false | Nonce _ _ _, _ -> true
  | Concat _ _, Literal _ | Concat _ _, Nonce _ _ _ -> false | Concat _ _, _ -> true
  | PK _, Literal _ | PK _, Nonce _ _ _ | PK _, Concat _ _ -> false | PK _, _ -> true
  | PKEnc _ _, Literal _ | PKEnc _ _, Nonce _ _ _ | PKEnc _ _, Concat _ _ | PKEnc _ _, PK _ -> false | PKEnc _ _, _ -> true
  | Derive _ _ _, Literal _ | Derive _ _ _, Nonce _ _ _ | Derive _ _ _, Concat _ _ | Derive _ _ _, PK _ | Derive _ _ _, PKEnc _ _ -> false | Derive _ _ _, _ -> true
  | AEnc _ _ None, Literal _ | AEnc _ _ None, Nonce _ _ _ | AEnc _ _ None, Concat _ _ | AEnc _ _ None, PK _ | AEnc _ _ None, PKEnc _ _ | AEnc _ _ None, Derive _ _ _ -> false | AEnc _ _ None, _ -> true
  | AEnc _ _ (Some ad), Sig _ _ | AEnc _ _ (Some ad), CEOgen _ | AEnc _ _ (Some ad), DEOgen _ _ | AEnc _ _ (Some ad), Mac _ _ | AEnc _ _ (Some ad), DH _ _ | AEnc _ _ (Some ad), BadDH _ _ | AEnc _ _ (Some ad), Hash _ -> true
  | AEnc _ _ (Some ad), _ -> false
  | Sig _ _, CEOgen _ | Sig _ _, DEOgen _ _ | Sig _ _, Mac _ _ | Sig _ _, DH _ _ | Sig _ _, BadDH _ _ | Sig _ _, Hash _ -> true | Sig _ _, _ -> false
  | CEOgen _, DEOgen _ _ | CEOgen _, Mac _ _ | CEOgen _, DH _ _ | CEOgen _, BadDH _ _ | CEOgen _, Hash _ -> true | CEOgen _, _ -> false
  | DEOgen _ _, Mac _ _ | DEOgen _ _, DH _ _ | DEOgen _ _, BadDH _ _ | DEOgen _ _, Hash _ -> true | DEOgen _ _, _ -> false
  | Mac _ _, DH _ _ | Mac _ _, BadDH _ _ | Mac _ _, Hash _ -> true | Mac _ _, _ -> false
  | DH _ _, BadDH _ _ | DH _ _, Hash _ -> true | DH _ _, _ -> false
  | BadDH _ _, Hash _ -> true | BadDH _ _, _ -> false
  | Hash _, _ -> false

(* The <= relation on bytes is also total *)
let rec bytes_le_totality_lemma t1 t2 : Lemma (ensures (bytes_le t1 t2 \/ bytes_le t2 t1)) [SMTPat (bytes_le t1 t2); SMTPat (bytes_le t2 t1)] =
  match t1, t2 with
  | Literal a, Literal b -> (match a, b with
			   | ByteSeq b1, ByteSeq b2 -> list_u8_le_totality_lemma (Seq.seq_to_list b1) (Seq.seq_to_list b2)
			   | String s1, String s2 -> list_char_le_totality_lemma (String.list_of_string s1) (String.list_of_string s2)
			   | _, _ -> ())
  | Nonce n1 l1 u1, Nonce n2 l2 u2 -> label_le_totality_lemma l1 l2; usage_le_totality_lemma u1 u2
  | Concat t1a t1b, Concat t2a t2b -> bytes_le_totality_lemma t1a t2a; bytes_le_totality_lemma t1b t2b
  | PK s1, PK s2 -> bytes_le_totality_lemma s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> bytes_le_totality_lemma pk1 pk2; bytes_le_totality_lemma m1 m2
  | Derive k1 c1 e1, Derive k2 c2 e2 -> bytes_le_totality_lemma k1 k2; bytes_le_totality_lemma c1 c2
  | AEnc k1 m1 None, AEnc k2 m2 None -> bytes_le_totality_lemma k1 k2; bytes_le_totality_lemma m1 m2
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> bytes_le_totality_lemma k1 k2; bytes_le_totality_lemma m1 m2; bytes_le_totality_lemma ad1 ad2
  | Sig k1 m1, Sig k2 m2 -> bytes_le_totality_lemma k1 k2; bytes_le_totality_lemma m1 m2
  | CEOgen sig1, CEOgen sig2 -> bytes_le_totality_lemma sig1 sig2
  | DEOgen msg1 sig1, DEOgen msg2 sig2 -> bytes_le_totality_lemma msg1 msg2; bytes_le_totality_lemma sig1 sig2
  | Mac k1 m1, Mac k2 m2 -> bytes_le_totality_lemma k1 k2; bytes_le_totality_lemma m1 m2
  | DH k1 k1', DH k2 k2' -> bytes_le_totality_lemma k1 k2; bytes_le_totality_lemma k1' k2'
  | BadDH k1 pk1, BadDH k2 pk2 -> bytes_le_totality_lemma k1 k2; bytes_le_totality_lemma pk1 pk2
  | Hash m1, Hash m2 -> bytes_le_totality_lemma m1 m2
  | _, _ -> ()

(* The <= relation on bytes is also anti-symmetric *)
let rec bytes_le_anti_symmetry_lemma t1 t2 : Lemma (ensures (bytes_le t1 t2 /\ bytes_le t2 t1 ==> t1 = t2)) [SMTPat (bytes_le t1 t2); SMTPat (bytes_le t2 t1)] =
  match t1, t2 with
  | Literal a, Literal b -> (match a, b with
			    | ByteSeq b1, ByteSeq b2 -> list_u8_le_anti_symmetry_lemma (Seq.seq_to_list b1) (Seq.seq_to_list b2);
						       Seq.lemma_seq_list_bij b1; Seq.lemma_seq_list_bij b2
			    | String s1, String s2 -> let l1 = (String.list_of_string s1) in let l2 = (String.list_of_string s2) in
						     list_char_le_anti_symmetry_lemma l1 l2; String.string_of_list_of_string s1;
						     String.string_of_list_of_string s2
			    | _, _ -> ())
  | Nonce n1 l1 u1, Nonce n2 l2 u2 -> label_le_anti_symmetry_lemma l1 l2; usage_le_anti_symmetry_lemma u1 u2
  | Concat t1a t1b, Concat t2a t2b -> bytes_le_anti_symmetry_lemma t1a t2a; bytes_le_anti_symmetry_lemma t1b t2b
  | PK s1, PK s2 -> bytes_le_anti_symmetry_lemma s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> bytes_le_anti_symmetry_lemma pk1 pk2; bytes_le_anti_symmetry_lemma m1 m2
  | Derive k1 c1 e1, Derive k2 c2 e2 -> bytes_le_anti_symmetry_lemma k1 k2; bytes_le_anti_symmetry_lemma c1 c2
  | AEnc k1 m1 None, AEnc k2 m2 None -> bytes_le_anti_symmetry_lemma k1 k2; bytes_le_anti_symmetry_lemma m1 m2
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> bytes_le_anti_symmetry_lemma k1 k2; bytes_le_anti_symmetry_lemma m1 m2; bytes_le_anti_symmetry_lemma ad1 ad2
  | Sig k1 m1, Sig k2 m2 -> bytes_le_anti_symmetry_lemma k1 k2; bytes_le_anti_symmetry_lemma m1 m2
  | CEOgen sig1, CEOgen sig2 -> bytes_le_anti_symmetry_lemma sig1 sig2
  | DEOgen msg1 sig1, DEOgen msg2 sig2 -> bytes_le_anti_symmetry_lemma msg1 msg2; bytes_le_anti_symmetry_lemma sig1 sig2
  | Mac k1 m1, Mac k2 m2 -> bytes_le_anti_symmetry_lemma k1 k2; bytes_le_anti_symmetry_lemma m1 m2
  | DH k1 k1', DH k2 k2' -> bytes_le_anti_symmetry_lemma k1 k2; bytes_le_anti_symmetry_lemma k1' k2'
  | BadDH k1 pk1, BadDH k2 pk2 -> bytes_le_anti_symmetry_lemma k1 k2; bytes_le_anti_symmetry_lemma pk1 pk2
  | Hash m1, Hash m2 -> bytes_le_anti_symmetry_lemma m1 m2
  | _, _ -> ()

// let bytes_le_transitivity_lemma t1 t2 t3 : Lemma (ensures (bytes_le t1 t2 /\ bytes_le t2 t3 ==> bytes_le t1 t3)) = ()

let usage = usage_
 let pke_key_usage = PKE
let ae_key_usage = AE
let mac_key_usage = MAC
let sig_key_usage = SIG

let kdf_usage f = KDF f
let nonce_usage = NONCE
let guid_usage = GUID
let dh_key_usage u = DHKey u

let get_dh_usage u = match u with | DHKey u' -> Some u' | _ -> None

let rec sprint_usage u =
  match u with
  | PKE -> "PKE"
  | AE -> "AE"
  | MAC -> "MAC"
  | SIG -> "SIG"
  | NONCE -> "NONCE"
  | GUID -> "GUID"
  | KDF (l,u) u' -> "KDF (ext->"^sprint_label l^","^sprint_usage u^") (exp->"^sprint_usage u'^")"
  | DHKey u -> "DHKey ("^sprint_usage u^")"

let rec is_pub_usage (u:usage) : Type0 =
  match u with
  | KDF (extract_label, extract_usage) expand_usage -> extract_label == public /\ is_pub_usage extract_usage /\ is_pub_usage expand_usage
  | DHKey u -> is_pub_usage u
  | _ -> True

(* A valid bytes in our model requires that the two bytes in DH are ordered as per the bytes_le relation *)
let rec is_valid_bytes_ t =
  match t with
  | Literal _ -> true
  | Concat t1 t2 -> is_valid_bytes_ t1 && is_valid_bytes_ t2
  | Nonce _ _ _ -> true
  | PK secret -> is_valid_bytes_ secret
  | PKEnc pk msg -> is_valid_bytes_ pk && is_valid_bytes_ msg
  | Derive k c e -> is_valid_bytes_ k && is_valid_bytes_ c
  | AEnc k m None -> is_valid_bytes_ k && is_valid_bytes_ m
  | AEnc k m (Some ad) -> is_valid_bytes_ k && is_valid_bytes_ m && is_valid_bytes_ ad
  | Sig sk msg -> is_valid_bytes_ sk && is_valid_bytes_ msg
  | CEOgen sig -> is_valid_bytes_ sig
  | DEOgen msg sig -> is_valid_bytes_ msg && is_valid_bytes_ sig
  | Mac k msg -> is_valid_bytes_ k && is_valid_bytes_ msg
  | DH k1 k2 -> bytes_le k1 k2 && is_valid_bytes_ k1 && is_valid_bytes_ k2
  | BadDH k pk -> is_valid_bytes_ k && is_valid_bytes_ pk
  | Hash m -> is_valid_bytes_ m

let bytes = t:bytes_{is_valid_bytes_ t}

let sprint_literal l =
  match l with
  | ByteSeq bs -> String.concat " " (List.Tot.map UInt8.to_string (Seq.seq_to_list bs))
  | String s -> s
  | Nat n -> string_of_int n
  | Bool n -> if n then "true" else "false"

let rec sprint_bytes_ t =
  match t with
  | Literal l -> sprint_literal l
  | Concat t1 t2 -> "("^sprint_bytes_ t1 ^ " | " ^ sprint_bytes_ t2^")"
  | Nonce i l NONCE -> "nonce("^string_of_int i^")"
  | Nonce i l GUID -> "guid("^string_of_int i^")"
  | Nonce i l PKE -> "dk("^string_of_int i^")"
  | Nonce i l AE -> "aek("^string_of_int i^")"
  | Nonce i l MAC -> "mk("^string_of_int i^")"
  | Nonce i l SIG -> "sk("^string_of_int i^")"
  | Nonce i l (KDF _ _) -> "kdfk("^string_of_int i^")"
  | Nonce i l (DHKey _) -> "dhkey("^string_of_int i^")"
  | PK s -> "pk("^sprint_bytes_ s^")"
  | PKEnc p m -> "pke_enc("^sprint_bytes_ p^","^sprint_bytes_ m^")"
  | Derive k ctx true -> "kdf_extract("^sprint_bytes_ k^","^sprint_bytes_ ctx^")"
  | Derive k ctx false -> "kdf_expand("^sprint_bytes_ k^","^sprint_bytes_ ctx^")"
  | AEnc p m None -> "ae_enc("^sprint_bytes_ p^","^sprint_bytes_ m^")"
  | AEnc p m (Some ad) -> "aead_enc("^sprint_bytes_ p^","^sprint_bytes_ m^","^sprint_bytes_ ad^")"
  | Sig k m -> "sign("^sprint_bytes_ k^","^sprint_bytes_ m^")"
  | CEOgen sig -> "ceogen("^sprint_bytes_ sig^")"
  | DEOgen msg sig -> "deogen("^sprint_bytes_ msg^","^sprint_bytes_ sig^")"
  | Mac k m -> "mac("^sprint_bytes_ k^","^sprint_bytes_ m^")"
  | DH k pk -> "dh("^sprint_bytes_ k^","^sprint_bytes_ pk^")"
  | BadDH k pk -> "baddh("^sprint_bytes_ k^","^sprint_bytes_ pk^")"
  | Hash m -> "hash("^sprint_bytes_ m^")"
  | _ -> ""

let sprint_bytes t = sprint_bytes_ t

let sprint_generated_nonce t =
    match t with
    | Nonce i l u -> "Generated "^sprint_bytes t^"\n    "^
		    "Label: "^sprint_label l^"\n    "^
		    "Usage: "^sprint_usage u
    | _ -> "Generated <unexpected non_nonce>"

(* strict label equality - requires same bytes, used only for nonces *)
let rec eq_label_strict (l:label) (l':label) : bool =
  match l, l' with
  | Public, Public -> true
  | ReadableBy a, ReadableBy b -> a = b
  | Join l1 l2, Join l1' l2'
  | Meet l1 l2, Meet l1' l2' -> (eq_label_strict l1 l1' && eq_label_strict l2 l2')
  | _, _ -> false

(* strictly equal labels satisfy eq_label *)
val eq_label_strict_are_eq : l:label -> l':label -> Lemma (ensures (eq_label_strict l l' == true <==> l == l'))
			 [SMTPat (eq_label_strict l l')]
let rec eq_label_strict_are_eq l l' =
  match l, l' with
  | Public, Public -> ()
  | ReadableBy a, ReadableBy b -> ()
  | Join l1 l2, Join l1' l2'
  | Meet l1 l2, Meet l1' l2' -> (eq_label_strict_are_eq l1 l1'; eq_label_strict_are_eq l2 l2')
  | _, _ -> ()

(* Boolean version of eq_label *)
let rec eq_label_ (l:label) (l':label) : bool =
  match l, l' with
  | Public, Public -> true
  | ReadableBy a, ReadableBy b -> a = b
  | Join l1 l2, Join l1' l2'
  | Meet l1 l2, Meet l1' l2' -> (eq_label_ l1 l1' && eq_label_ l2 l2') ||
			       (eq_label_ l1 l2' && eq_label_ l2 l1')
  | _, _ -> false

(* Join and meet preserve equality of eq_labels *)
let join_and_meet_preserve_eq_label_ (l1:label) (l2:label) (l1':label) (l2':label) :
    Lemma (ensures ((eq_label_ l1 l1' /\ eq_label_ l2 l2') ==> (eq_label_ (join l1 l2) (join l1' l2') /\ eq_label_ (meet l1 l2) (meet l1' l2')))) = ()

val eq_label_are_equal : l:label -> l':label -> Lemma (ensures (eq_label_ l l' == true <==> eq_label l l'))
			 [SMTPat (eq_label_ l l')]
let rec eq_label_are_equal l l' =
  match l, l' with
  | Public, Public -> ()
  | ReadableBy a, ReadableBy b -> ()
  | Join l1 l2, Join l1' l2'
  | Meet l1 l2, Meet l1' l2' -> (eq_label_are_equal l1 l1'; eq_label_are_equal l2 l2';
			       eq_label_are_equal l1 l2'; eq_label_are_equal l2 l1')
  | _, _ -> ()

(* Strict version of eq_usage *)
let rec eq_usage_strict u u' =
  match u, u' with
  | PKE, PKE
  | AE, AE
  | MAC, MAC
  | SIG, SIG
  | NONCE, NONCE
  | GUID, GUID -> true
  | DHKey u1, DHKey u2 -> eq_usage_strict u1 u2
  | KDF (l, u1) u2, KDF (l', u1') u2' -> eq_label_strict l l' && eq_usage_strict u1 u1' && eq_usage_strict u2 u2'
  | _, _ -> false

val eq_usage_strict_are_eq : u:usage -> u':usage -> Lemma (ensures (eq_usage_strict u u' == true <==> u == u')) 
			 [SMTPat (eq_usage_strict u u')]
let rec eq_usage_strict_are_eq u u' =
  match u, u' with
  | PKE, PKE
  | AE, AE
  | MAC, MAC
  | SIG, SIG
  | NONCE, NONCE
  | GUID, GUID -> ()
  | DHKey u1, DHKey u2 -> eq_usage_strict_are_eq u1 u2
  | KDF (l, u1) u2, KDF (l', u1') u2' -> eq_label_strict_are_eq l l'; eq_usage_strict_are_eq u1 u1'; eq_usage_strict_are_eq u2 u2'
  | _, _ -> ()

(* Definition of eq_usage used by outer functions *)
let rec eq_usage u u' =
  match u, u' with
  | PKE, PKE
  | AE, AE
  | MAC, MAC
  | SIG, SIG
  | NONCE, NONCE
  | GUID, GUID -> true
  | DHKey u1, DHKey u2 -> eq_usage u1 u2
  | KDF (l, u1) u2, KDF (l', u1') u2' -> eq_label_ l l' && eq_usage u1 u1' && eq_usage u2 u2'
  | _, _ -> false

let rec eq_usage_reflexive_lemma u u' =
  match u, u' with
  | PKE, PKE
  | AE, AE
  | MAC, MAC
  | SIG, SIG
  | NONCE, NONCE
  | GUID, GUID -> ()
  | DHKey u1, DHKey u2 -> eq_usage_reflexive_lemma u1 u2
  | KDF (l, u1) u2, KDF (l', u1') u2' -> eq_label_reflexive_lemma l; eq_usage_reflexive_lemma u1 u1'; eq_usage_reflexive_lemma u2 u2'
  | _ -> ()

let rec eq_usage_symmetric_lemma u u' =
  match u, u' with
  | PKE, PKE
  | AE, AE
  | MAC, MAC
  | SIG, SIG
  | NONCE, NONCE
  | GUID, GUID -> ()
  | DHKey u1, DHKey u2 -> eq_usage_symmetric_lemma u1 u2
  | KDF (l, u1) u2, KDF (l', u1') u2' -> eq_label_symmetric_lemma l l'; eq_usage_symmetric_lemma u1 u1'; eq_usage_symmetric_lemma u2 u2'
  | _, _ -> ()

let rec eq_usage_transitive_lemma u u' u'' =
  match u, u', u'' with
  | PKE, PKE, PKE
  | AE, AE, AE
  | MAC, MAC, MAC
  | SIG, SIG, SIG
  | NONCE, NONCE, NONCE
  | GUID, GUID, GUID -> ()
  | DHKey u1, DHKey u2, DHKey u3-> eq_usage_transitive_lemma u1 u2 u3
  | KDF (l, u1) u2, KDF (l', u1') u2', KDF (l'', u1'') u2'' ->
	    eq_label_transitive_lemma l l' l''; eq_usage_transitive_lemma u1 u1' u1''; eq_usage_transitive_lemma u2 u2' u2''
  | _, _, _ -> ()

(* Equality of symbolic bytes *)
let rec eq_bytes_ t1 t2 : bool =
  match t1,t2 with
  | Literal l1, Literal l2 -> l1 = l2
  | Concat t1a t1b, Concat t2a t2b -> eq_bytes_ t1a t2a && eq_bytes_ t1b t2b
  | Nonce n1 l1 u1, Nonce n2 l2 u2  -> n1 = n2 && l1 = l2 && u1 = u2
  | PK s1, PK s2 -> eq_bytes_ s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> eq_bytes_ pk1 pk2 && eq_bytes_ m1 m2
  | Derive k1 ctx1 b1, Derive k2 ctx2 b2 -> eq_bytes_ k1 k2 && eq_bytes_ ctx1 ctx2 && b1 = b2
  | AEnc k1 m1 None, AEnc k2 m2 None -> eq_bytes_ k1 k2 && eq_bytes_ m1 m2
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> eq_bytes_ k1 k2 && eq_bytes_ m1 m2 && eq_bytes_ ad1 ad2
  | Sig sk1 m1, Sig sk2 m2 -> eq_bytes_ sk1 sk2 && eq_bytes_ m1 m2
  | CEOgen sig1, CEOgen sig2 -> eq_bytes_ sig1 sig2
  | DEOgen msg1 sig1, DEOgen msg2 sig2 -> eq_bytes_ msg1 msg2 && eq_bytes_ sig1 sig2
  | Mac k1 m1, Mac k2 m2 -> eq_bytes_ k1 k2 && eq_bytes_ m1 m2
  // | DH k1 (PK k2'), DH k2 (PK k1') -> (eq_bytes k1 k2 && eq_bytes k2' k1') || (eq_bytes k1 k1' && eq_bytes k2' k2)
  | DH k1 k2, DH k1' k2' -> eq_bytes_ k1 k1' && eq_bytes_ k2 k2'
  | BadDH k1 k2, BadDH k1' k2' -> eq_bytes_ k1 k1' && eq_bytes_ k2 k2'
  | Hash m1, Hash m2 -> eq_bytes_ m1 m2
  | _, _ -> false

let rec eq_bytes_is_reflexive_ t1 t2 : Lemma (ensures (t1 == t2 ==> eq_bytes_ t1 t2)) =
  match t1,t2 with
  | Literal l1, Literal l2 -> ()
  | Concat t1a t1b, Concat t2a t2b -> eq_bytes_is_reflexive_ t1a t2a; eq_bytes_is_reflexive_ t1b t2b
  | Nonce n1 _ _, Nonce n2 _ _ -> ()
  | PK s1, PK s2 -> eq_bytes_is_reflexive_ s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> eq_bytes_is_reflexive_ pk1 pk2 ; eq_bytes_is_reflexive_ m1 m2
  | Derive k1 ctx1 b1, Derive k2 ctx2 b2 -> eq_bytes_is_reflexive_ k1 k2 ; eq_bytes_is_reflexive_ ctx1 ctx2
  | AEnc k1 m1 None, AEnc k2 m2 None -> eq_bytes_is_reflexive_ k1 k2 ; eq_bytes_is_reflexive_ m1 m2
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> eq_bytes_is_reflexive_ k1 k2 ; eq_bytes_is_reflexive_ m1 m2 ; eq_bytes_is_reflexive_ ad1 ad2
  | Sig sk1 m1, Sig sk2 m2 -> eq_bytes_is_reflexive_ sk1 sk2 ; eq_bytes_is_reflexive_ m1 m2
  | CEOgen sig1, CEOgen sig2 -> eq_bytes_is_reflexive_ sig1 sig2
  | DEOgen msg1 sig1, DEOgen msg2 sig2 -> eq_bytes_is_reflexive_ msg1 msg2 ; eq_bytes_is_reflexive_ sig1 sig2
  | Mac k1 m1, Mac k2 m2 -> eq_bytes_is_reflexive_ k1 k2 ; eq_bytes_is_reflexive_ m1 m2
  | DH k1 k2', DH k2 k1' -> eq_bytes_is_reflexive_ k1 k2; eq_bytes_is_reflexive_ k2' k1'
  | BadDH k1 k2, BadDH k1' k2' -> eq_bytes_is_reflexive_ k1 k1'; eq_bytes_is_reflexive_ k2 k2'
  | Hash m1, Hash m2 -> eq_bytes_is_reflexive_ m1 m2
  | _, _ -> ()

let rec eq_bytes_is_symmetric_ t1 t2 : Lemma (ensures (eq_bytes_ t1 t2 ==> eq_bytes_ t2 t1)) =
  match t1,t2 with
  | Literal s1, Literal s2 -> ()
  | Concat t1a t1b, Concat t2a t2b -> eq_bytes_is_symmetric_ t1a t2a; eq_bytes_is_symmetric_ t1b t2b
  | Nonce n1 _ _, Nonce n2 _ _ -> ()
  | PK s1, PK s2 -> eq_bytes_is_symmetric_ s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> eq_bytes_is_symmetric_ pk1 pk2 ; eq_bytes_is_symmetric_ m1 m2
  | Derive k1 ctx1 b1, Derive k2 ctx2 b2 -> eq_bytes_is_symmetric_ k1 k2 ; eq_bytes_is_symmetric_ ctx1 ctx2
  | AEnc k1 m1 None, AEnc k2 m2 None -> eq_bytes_is_symmetric_ k1 k2 ; eq_bytes_is_symmetric_ m1 m2
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> eq_bytes_is_symmetric_ k1 k2 ; eq_bytes_is_symmetric_ m1 m2 ; eq_bytes_is_symmetric_ ad1 ad2
  | Sig sk1 m1, Sig sk2 m2 -> eq_bytes_is_symmetric_ sk1 sk2 ; eq_bytes_is_symmetric_ m1 m2
  | CEOgen sig1, CEOgen sig2 -> eq_bytes_is_symmetric_ sig1 sig2
  | DEOgen msg1 sig1, DEOgen msg2 sig2 -> eq_bytes_is_symmetric_ msg1 msg2 ; eq_bytes_is_symmetric_ sig1 sig2
  | Mac k1 m1, Mac k2 m2 -> eq_bytes_is_symmetric_ k1 k2 ; eq_bytes_is_symmetric_ m1 m2
  | DH k1 k2', DH k2 k1' -> eq_bytes_is_symmetric_ k1 k2 ; eq_bytes_is_symmetric_ k2' k1'
  | BadDH k1 k2, BadDH k1' k2' -> eq_bytes_is_symmetric_ k1 k1' ; eq_bytes_is_symmetric_ k2 k2'
  | Hash m1, Hash m2 -> eq_bytes_is_symmetric_ m1 m2
  | _, _ -> ()

let rec eq_bytes_is_transitive_ t1 t2 t3 : Lemma (ensures (eq_bytes_ t1 t2 /\ eq_bytes_ t2 t3 ==> eq_bytes_ t1 t3)) =
  match t1,t2,t3 with
  | Literal s1, Literal s2, Literal s3 -> ()
  | Concat t1a t1b, Concat t2a t2b, Concat t3a t3b -> eq_bytes_is_transitive_ t1a t2a t3a; eq_bytes_is_transitive_ t1b t2b t3b
  | Nonce n1 _ _, Nonce n2 _ _, Nonce n3 _ _ -> ()
  | PK s1, PK s2, PK s3 -> eq_bytes_is_transitive_ s1 s2 s3
  | PKEnc pk1 m1, PKEnc pk2 m2, PKEnc pk3 m3 -> eq_bytes_is_transitive_ pk1 pk2 pk3; eq_bytes_is_transitive_ m1 m2 m3
  | Derive k1 ctx1 b1, Derive k2 ctx2 b2, Derive k3 ctx3 b3 -> eq_bytes_is_transitive_ k1 k2 k3; eq_bytes_is_transitive_ ctx1 ctx2 ctx3
  | AEnc k1 m1 None, AEnc k2 m2 None, AEnc k3 m3 None -> eq_bytes_is_transitive_ k1 k2 k3; eq_bytes_is_transitive_ m1 m2 m3
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2), AEnc k3 m3 (Some ad3) -> eq_bytes_is_transitive_ k1 k2 k3; eq_bytes_is_transitive_ m1 m2 m3; eq_bytes_is_transitive_ ad1 ad2 ad3
  | Sig sk1 m1, Sig sk2 m2, Sig sk3 m3 -> eq_bytes_is_transitive_ sk1 sk2 sk3; eq_bytes_is_transitive_ m1 m2 m3
  | CEOgen sig1, CEOgen sig2, CEOgen sig3 -> eq_bytes_is_transitive_ sig1 sig2 sig3
  | DEOgen msg1 sig1, DEOgen msg2 sig2, DEOgen msg3 sig3 -> eq_bytes_is_transitive_ msg1 msg2 msg3; eq_bytes_is_transitive_ sig1 sig2 sig3
  | Mac k1 m1, Mac k2 m2, Mac k3 m3 -> eq_bytes_is_transitive_ k1 k2 k3 ; eq_bytes_is_transitive_ m1 m2 m3
  | DH k1 k1', DH k2 k2', DH k3 k3' ->
	  eq_bytes_is_transitive_ k1 k2 k3;
	  eq_bytes_is_transitive_ k1' k2' k3'
  | BadDH k1 k1', BadDH k2 k2', BadDH k3 k3' ->
	  eq_bytes_is_transitive_ k1 k2 k3;
	  eq_bytes_is_transitive_ k1' k2' k3'
  | Hash m1, Hash m2, Hash m3 -> eq_bytes_is_transitive_ m1 m2 m3
  | _, _, _ -> ()

(* Lemma to show that eq_bytes are "==" *)
let rec eq_bytes_is_equal_ t1 t2 : Lemma (ensures (eq_bytes_ t1 t2 <==> t1 = t2)) =
  match t1,t2 with
  | Literal s1, Literal s2 -> ()
  | Concat t1a t1b, Concat t2a t2b -> eq_bytes_is_equal_ t1a t2a; eq_bytes_is_equal_ t1b t2b
  | Nonce n1 _ _, Nonce n2 _ _ -> ()
  | PK s1, PK s2 -> eq_bytes_is_equal_ s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> eq_bytes_is_equal_ pk1 pk2 ; eq_bytes_is_equal_ m1 m2
  | Derive k1 ctx1 b1, Derive k2 ctx2 b2 -> eq_bytes_is_equal_ k1 k2 ; eq_bytes_is_equal_ ctx1 ctx2
  | AEnc k1 m1 None, AEnc k2 m2 None -> eq_bytes_is_equal_ k1 k2 ; eq_bytes_is_equal_ m1 m2
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> eq_bytes_is_equal_ k1 k2 ; eq_bytes_is_equal_ m1 m2 ; eq_bytes_is_equal_ ad1 ad2
  | Sig sk1 m1, Sig sk2 m2 -> eq_bytes_is_equal_ sk1 sk2 ; eq_bytes_is_equal_ m1 m2
  | CEOgen sig1, CEOgen sig2 -> eq_bytes_is_equal_ sig1 sig2
  | DEOgen msg1 sig1, DEOgen msg2 sig2 -> eq_bytes_is_equal_ msg1 msg2 ; eq_bytes_is_equal_ sig1 sig2
  | Mac k1 m1, Mac k2 m2 -> eq_bytes_is_equal_ k1 k2 ; eq_bytes_is_equal_ m1 m2
  | DH k1 k2', DH k2 k1' -> eq_bytes_is_equal_ k1 k2 ; eq_bytes_is_equal_ k2' k1'
  | BadDH k1 k2, BadDH k1' k2' -> eq_bytes_is_equal_ k1 k1' ; eq_bytes_is_equal_ k2 k2'
  | Hash m1, Hash m2 -> eq_bytes_is_equal_ m1 m2
  | _, _ -> ()

let eq_bytes t1 t2 = eq_bytes_ t1 t2
let eq_bytes_lemma t1 t2 : Lemma (ensures (eq_bytes_ t1 t2 <==> eq_bytes t1 t2)) [SMTPat (eq_bytes_ t1 t2); SMTPat (eq_bytes t1 t2)] = ()

let eq_bytes_is_reflexive t1 t2 = eq_bytes_is_reflexive_ t1 t2
let eq_bytes_is_symmetric t1 t2 = eq_bytes_is_symmetric_ t1 t2
let eq_bytes_is_transitive t1 t2 = eq_bytes_is_transitive_ t1 t2
let eq_bytes_is_equal t1 t2 = eq_bytes_is_equal_ t1 t2
let eq_bytes_is_equal_bool t1 t2 : Lemma (eq_bytes t1 t2 <==> t1 = t2) [SMTPat (eq_bytes t1 t2)] = eq_bytes_is_equal_ t1 t2

noeq
type usage_pred_ =
  | NONCE_PRED: usage_pred_
  | GUID_PRED: usage_pred_
  | PKE_PRED: up:(payload:nat -> bytes -> Type0) -> usage_pred_
  | AE_PRED: up:(payload:nat -> bytes -> ad:option bytes -> Type0) -> usage_pred_
  | MAC_PRED: up:(macval:nat -> bytes -> Type0) -> usage_pred_
  | SIG_PRED: up:(sigval:nat -> bytes -> Type0) -> usage_pred_
  | KDF_PRED: up1:usage_pred_ -> up2:usage_pred_ -> usage_pred_
  | DH_PRED: up:usage_pred_ -> usage_pred_

let rec is_valid_usage_pred (u:usage) (up:usage_pred_) : Type0 =
  match u, up with
  | NONCE,NONCE_PRED
  | GUID,GUID_PRED -> True
  | PKE, PKE_PRED p
  | MAC, MAC_PRED p
  | SIG, SIG_PRED p -> is_payload_pred p
  | AE, AE_PRED p -> is_payload_ad_pred p
  | DHKey u,DH_PRED p -> is_valid_usage_pred u p
  | KDF (l1,u1) u2, KDF_PRED up1 up2 -> is_valid_usage_pred u1 up1 /\ is_valid_usage_pred u2 up2
  | _ -> False

let rec is_valid_usage_pred_eq u up u' =
  match u,u',up with
  | DHKey u1, DHKey u2, DH_PRED up ->
    is_valid_usage_pred_eq u1 up u2
  | KDF (l,u1) u2, KDF (l',u1') u2', KDF_PRED up1 up2 ->
    is_valid_usage_pred_eq u1 up1 u1';
    is_valid_usage_pred_eq u2 up2 u2'
  | _ -> ()


let pke_key_usage_pred p = PKE_PRED p
let ae_key_usage_pred p = AE_PRED p
let mac_key_usage_pred p = MAC_PRED p
let sig_key_usage_pred p = SIG_PRED p
let kdf_usage_pred l u u' p p' = KDF_PRED p p'
let dh_usage_pred u up = DH_PRED up
let rec default_usage_pred u =
  match u with
  | PKE -> PKE_PRED (fun i (t:bytes) -> True)
  | AE -> AE_PRED (fun i (t:bytes) (ad:option bytes) -> True)
  | MAC -> MAC_PRED (fun i (t:bytes) -> True)
  | SIG -> SIG_PRED (fun i (t:bytes) -> True)
  | KDF (l,u) u' -> KDF_PRED (default_usage_pred u) (default_usage_pred u')
  | NONCE -> NONCE_PRED
  | GUID -> GUID_PRED
  | DHKey u -> DH_PRED (default_usage_pred u)

// Implicit match statements in the first argument to get the actual predicate function
let pke_pred (PKE_PRED up) i t = (exists j. j <= i /\ up j t)
let ae_pred (AE_PRED up) i t t' = (exists j. j <= i /\ up j t t')
let mac_pred (MAC_PRED up) i t = (exists j. j <= i /\ up j t)
let sign_pred (SIG_PRED up) i t = (exists j. j <= i /\ up j t)

let pke_pred_default i t = ()
let ae_pred_default i t to = ()
let mac_pred_default i t = ()
let sign_pred_default i t = ()

let pke_key_usage_pred_lemma up i t = ()
let pke_key_usage_pred_monotonic_lemma up i t = ()
let ae_key_usage_pred_lemma up i t ad = ()
let ae_key_usage_pred_monotonic_lemma up i t ad = ()
let mac_key_usage_pred_lemma up i t = ()
let mac_key_usage_pred_monotonic_lemma up i t = ()
let sig_key_usage_pred_lemma up i t = ()
let sig_key_usage_pred_monotonic_lemma up i t = ()


let literal_to_bytes s = Literal s
let bytes_to_literal t =
  match t with
  | Literal s -> Success s
  | _ -> Error "bytes_to_literal: not a literal"
let to_literal_lemma s = ()
let literal_eq_fun_lemma t1 t2 = ()

let from_string_lemma t = ()
let string_to_bytes_equal_lemma a b = ()
let string_to_bytes_eqbytes_lemma a b = ()
let bytes_to_string_eqbytes_lemma a b = ()

let mk_nonce i l u = Nonce i l u
let gnonce i l u = Nonce i l u
let gnonce_eq_fun_lemma i l1 l2 u1 u2 = ()
let gnonce_inj_lemma i1 i2 l1 l2 u1 u2 = ()

val gnonce_eq_inj_lemma_ (i:nat) (l1:DY.Labels.label) (u1:usage) (t2:bytes) :
  Lemma (requires (eq_bytes (gnonce i l1 u1) t2))
	(ensures (exists l2 u2. l1 == l2 /\ u1 == u2 /\ t2 == gnonce i l2 u2))
  [SMTPat (eq_bytes (gnonce i l1 u1) t2)]
let gnonce_eq_inj_lemma_ i1 l1 u1 t2 =
  match t2 with
  | Nonce i2 l2 u2 ->
    assert (l1 == l2 /\ u1 == u2 /\ t2 == gnonce i1 l2 u2);
    ()
  | _ -> ()

let gnonce_eq_inj_lemma i l1 u2 t2 = ()

let concat b1 b2 = Concat b1 b2
let concat_eq_fun_lemma t10 t11 t20 t22 =()
let concat_inj_lemma t10 t11 t20 t23 = ()
val concat_eq_inj_lemma_ (t10 t11 t2: bytes) :
  Lemma (requires (eq_bytes (concat t10 t11) t2))
	(ensures (exists t20 t21. t2 == concat t20 t21 /\ eq_bytes t10 t20 /\ eq_bytes t11 t21))
  [SMTPat (eq_bytes (concat t10 t11) t2)]
let concat_eq_inj_lemma_ t10 t11 t2 =
  match t2 with
  | Concat t20 t21 ->
    assert (t2 == concat t20 t21 /\ eq_bytes t10 t20 /\ eq_bytes t11 t21)
  | _ -> ()
let concat_eq_inj_lemma t10 t11 t2 = ()
let concat_eq_inj_forall_lemma t10 t11 = ()

let split c =
  match c with
  | Concat b1 b2 -> Success (b1,b2)
  | _ -> Error "split: not a concat"

let split_inj_lemma t1 t2 =
  match split t1, split t2 with
  | Success (t10,t11), Success (t20,t21) ->
    assert (t1 == concat t10 t11);
    assert (t2 == concat t20 t21)
  | Error _, Error _ -> ()
  | _, _ -> ()
let split_eq_inj_lemma t1 t2 = ()
let split_concat_lemma a b = ()
let concat_split_lemma t = ()

let cannot_split_string_bytes a = ()
let concat_bytes_is_not_a_string_bytes a = ()

let pk s = (PK s)
let pk_eq_fun_lemma t1 t2 = ()

let is_pk t = match t with | PK s -> true | _ -> false

let pke_enc p s = (PKEnc p s)
let pke_enc_eq_fun_lemma p1 m1 p2 m2 = ()

let pke_enc_inj_lemma pub msg1 msg2 = ()
let pke_enc_eq_inj_lemma pub1 msg1 pub2 msg2 = ()

let pke_dec s c =
  match c with
  | PKEnc (PK s') m ->
    if eq_bytes s s' then Success m
    else Error "pke_dec: key mismatch"
  | _ -> Error "pke_dec: not a pke ciphertext"


let pke_dec_enc_lemma s b =
  let c = pke_enc (pk s) b in
  match c with
  | PKEnc (PK s') m -> ()
  | _ -> ()

let pke_enc_dec_lemma s c =
  match c with
  | PKEnc (PK s') m ->
     if eq_bytes s s' then ()
     else ()
  | _ -> ()

let aead_enc k p ad = (match ad with | None -> AEnc k p None | Some ad' -> AEnc k p (Some ad'))
let aead_enc_eq_fun_lemma key1 msg1 key2 msg2 ad1 ad2 = ()
let ae_enc_eq_fun_lemma key1 msg1 key2 msg2 = ()
let aead_enc_inj_lemma key msg1 msg2 ad1 ad2 = ()
let ae_enc_inj_lemma key msg1 msg2 ad1 ad2 = ()
let ae_enc_eq_inj_lemma key1 key2 msg1 msg2 = ()
let aead_enc_eq_inj_lemma key1 key2 msg1 msg2 ad1 ad2 = ()

let aead_dec k c ad =
  match ad, c with
  | Some ad, AEnc k' m (Some ad') ->
    if eq_bytes k k' && eq_bytes ad ad' then Success m
    else Error "aead_dec: key or ad mismatch"
  | None, AEnc k' m None ->
    if eq_bytes k k' then Success m
    else Error "aead_dec: key or ad mismatch"
  | _ -> Error "aead_dec: not an aead ciphertext"

let aead_dec_enc_lemma k p ad = ()
let ae_enc_dec_lemma s c = ()

#push-options "--z3rlimit 50"
let aead_enc_dec_lemma s c ad =
  match c with
  | AEnc s' p' (Some ad') ->
    if eq_bytes s s' && eq_bytes ad ad' then (
      assert (c == aead_enc s' p' (Some ad') /\
	      eq_bytes s s' /\ eq_bytes ad ad'))
    else ()
  | _ -> ()
#pop-options

let vk k = PK k
let vk_eq_fun_lemma t1 t2 = ()

let sign s m = (Sig s m)
let sign_eq_fun_lemma priv1 msg1 priv2 msg2 = ()

let verify p m t =
  match t with
  | Sig s m' ->
    //( match p with
    //  | PK s -> if eq_bytes m m' then true else false
    //  //| PK (DEOgen m'' t) -> if eq_bytes m m'' then true else false
    //  | _ -> false )
    if eq_bytes p (PK s) && eq_bytes m m' then true else (
      match p with
      | PK (CEOgen (Sig s' m'')) -> if eq_bytes s s' && eq_bytes m m' && eq_bytes m' m'' then true else false
      | PK (DEOgen m'' t') -> if eq_bytes m m'' && eq_bytes t t' then true else false
      | _ -> false
    )
  | _ -> false

val verify_eq_fun_lemma_ (pub1 pub2 msg1 msg2: bytes) (tag:bytes):
  Lemma (requires (eq_bytes pub1 pub2 /\ eq_bytes msg1 msg2))
	(ensures (verify pub1 msg1 tag == verify pub2 msg2 tag))
  [SMTPat (verify pub1 msg1 tag); SMTPat (verify pub2 msg2 tag)]

let verify_eq_fun_lemma_ pub1 pub2 msg1 msg2 tag =
  match tag with
  | Sig s' m' ->
    if eq_bytes pub1 (PK s') && eq_bytes msg1 m' then (
      assert (eq_bytes pub1 (PK s'));
      eq_bytes_is_symmetric pub1 pub2;
      eq_bytes_is_transitive pub2 pub1 (PK s');
      eq_bytes_is_symmetric msg1 msg2;
      eq_bytes_is_transitive msg2 msg1 m';
      assert (eq_bytes pub2 (PK s'));
      assert (eq_bytes msg2 m'))
    else (
      eq_bytes_is_transitive pub1 pub2 (PK s');
      eq_bytes_is_transitive msg1 msg2 m'
    )
  | _ -> ()

let verify_eq_fun_lemma pub1 pub2 msg1 msg2 tag = ()
let verify_sign_lemma s b = ()
//let sign_verify_lemma p msg tag =
//  match tag with
//  | Sig s' m' ->
//    if eq_bytes p (PK s') && eq_bytes msg m' then
//      assert (tag == sign s' m' /\ eq_bytes p (pk s') /\ eq_bytes msg m')
//    else ()
//  | _ -> ()

let ceo_gen sig = CEOgen sig
let ceo_gen_verify_lemma m sk = ()

let deo_gen msg sig = DEOgen msg sig
let deo_gen_verify_lemma m1 m2 sk = ()

let kdf t1 t2 b = Derive t1 t2 b
let kdf_eq_fun_lemma key1 key2 context1 context2 extract = ()
let kdf_inj_lemma key1 key2 context1 context2 extract = ()

val kdf_eq_inj_lemma_ (key1 context1 t2: bytes) (extract:bool):
  Lemma (requires (eq_bytes (kdf key1 context1 extract) t2))
	(ensures (exists key2 context2. t2 == kdf key2 context2 extract /\
			   eq_bytes key1 key2 /\ eq_bytes context1 context2))
  [SMTPat (eq_bytes (kdf key1 context1 extract) t2)]

let kdf_eq_inj_lemma_ key1 context1 t2 extract =
  match t2 with
  | Derive key2 context2 extract' ->
    assert (t2 == kdf key2 context2 extract /\
  	    eq_bytes key1 key2 /\ eq_bytes context1 context2)
  | _ -> ()
let kdf_eq_inj_lemma key1 context1 t2 extract = ()

let mac k m = Mac k m
let mac_eq_fun_lemma k1 k2 m1 m2 = ()
let mac_inj_lemma k1 k2 m1 m2 = ()

val mac_eq_inj_lemma_ (key1 msg1 t2: bytes):
  Lemma (requires (eq_bytes (mac key1 msg1) t2))
	(ensures (exists key2 msg2. t2 == mac key2 msg2 /\
		       eq_bytes key1 key2 /\ eq_bytes msg1 msg2))
  [SMTPat (eq_bytes (mac key1 msg1) t2)]
let mac_eq_inj_lemma_ k1 m1 t2 =
  match t2 with
  | Mac k2 m2 ->
    assert (t2 == mac k2 m2 /\
	    eq_bytes k1 k2 /\ eq_bytes m1 m2)
  | _ -> ()

let mac_eq_inj_lemma k1 m1 t2 = ()

let verify_mac k m t =
  match t with
  | Mac k' m' -> if eq_bytes k k' && eq_bytes m m' then true else false
  | _ -> false
let verify_mac_lemma k m t = ()

let hash m = Hash m
let hash_eq_fun_lemma m1 m2 = ()
let hash_inj_lemma m1 m2 = ()
let hash_eq_inj_lemma m1 m2 = ()

/// Generate a Diffie-Hellman shared secret from a private component :math:`k` and a public
/// component :math:`pk`.  In essence, this models calculating :math:`pk^k`.  However, because the
/// :math:`g^{ab} = g^{ba}` equality underlying DH is modeled with an ordering relation on the
/// private components, we need to "unpack" the public input to get back the secret input.  This may
/// of course fail when :math:`pk` is not a public key, i.e., in the real world :math:`\not\exists
/// a: g^a = pk`.  In that case, we return a "garbage" result (that still depends on the inputs).
let dh k pk = match pk with
              | PK k' -> if bytes_le k k' then DH k k' else DH k' k
              | _ -> BadDH k pk

let dh_eq_fun_lemma s1 s2 p1 p2 = ()
let dh_shared_secret_lemma x y = ()
let dh_shared_secret_eq_bytes_lemma u = ()

let rec bytes_depth_ t : nat =
  match t with
  | Literal _
  | Nonce _ _ _ -> 1
  | Hash t1
  | PK t1
  | CEOgen t1 -> bytes_depth_ t1 + 1
  | Derive t1 t2 _
  | Sig t1 t2
  | DEOgen t1 t2
  | PKEnc t1 t2
  | Concat t1 t2
  | Mac t1 t2
  | DH t1 t2
  | BadDH t1 t2
  | AEnc t1 t2 None -> bytes_depth_ t1 + bytes_depth_ t2 + 1
  | AEnc t1 t2 (Some t3) -> bytes_depth_ t1 + bytes_depth_ t2 + bytes_depth_ t3 + 1

let bytes_depth t = bytes_depth_ t
let bytes_depth_decreases_when_splitting t = ()

let pk_injective_lemma t1 t2 = ()
let pk_injective_lemma_forall t = ()

let eq_bytes_concat_split_lemma t1 t2 t = ()

