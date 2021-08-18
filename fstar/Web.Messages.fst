/// Web.Messages (implementation)
/// ==============================
module Web.Messages
open DY.Crypto
open FStar.String
open FStar.Seq.Base
open HelperFunctions

let rec domain_to_string dom =
  match dom with
  |Root s -> s
  |Sub s d -> domain_to_string d ^ "." ^ s

let rec eq_querystring (q1:seq (bytes * bytes)) (q2:seq (bytes * bytes)) : Tot bool
 (decreases (length q1)) =
  if(length q1 <> length q2) then false
  else if(length q1 = 0) then true
  else (
    let q1_fst = fst (index q1 0) in
    let q2_fst = fst (index q2 0) in
    let q1_snd = snd (index q1 0) in
    let q2_snd = snd (index q2 0) in
    if ((eq_bytes q1_fst q2_fst) && (eq_bytes q1_snd q2_snd)) then
      eq_querystring (tail q1) (tail q2)
    else false
    )

#push-options "--z3rlimit 20"
(**
    Helper lemma for eq_querystring_lemma.
*)
let rec eq_querystring_lemma_helper_1 (a:seq (bytes * bytes)) (b:seq (bytes * bytes)) : Lemma
    (ensures(
      eq_querystring a b
      ==>
      ((length a) = (length b))
      /\ (forall (i: nat {i < length a} ) . i < (length a)
         ==>  (eq_bytes (fst (Seq.index a i))  (fst (Seq.index b i))
           /\  eq_bytes (snd (Seq.index a i))  (snd (Seq.index b i)))
         )))
    (decreases (length a))
    =
      match length a with
      | 0 -> ()
      | _ ->
        if(eq_querystring a b) then (
          assert(eq_bytes (fst (Seq.index a 0))  (fst (Seq.index b 0))) ;
          eq_querystring_lemma_helper_1 (tail a) (tail b);
          assert(forall (i:nat). i < length (tail a) ==>
            eq_bytes (fst (Seq.index (tail a) i))  (fst (Seq.index (tail b) i))) ;
          lemma_tl (Seq.index a 0) (tail a)
        )
        else ()
#pop-options

(**
    Helper lemma for eq_querystring_lemma.
*)
let rec eq_querystring_lemma_helper_2 (a:seq (bytes * bytes)) (b:seq (bytes * bytes)) : Lemma
    (ensures ((length a) = (length b))
             /\ (forall (i: nat {i < length a} ) . i < (length a)
                ==> ( eq_bytes (fst (Seq.index a i))  (fst (Seq.index b i))
                /\ eq_bytes (snd (Seq.index a i))  (snd (Seq.index b i))
               ))
             ==> eq_querystring a b)
    (decreases (length a))
    =
        match length a with
        | 0 -> ()
        | _ ->
          if(length a <> length b) then ()
          else eq_querystring_lemma_helper_2 (tail a) (tail b)

let eq_querystring_lemma (a:seq (bytes * bytes)) (b:seq (bytes * bytes))
 : Lemma (
     eq_querystring a b <==>
     ((length a) = (length b))
      /\ (forall (i: nat {i < length a} ) . i < (length a)
         ==> ( eq_bytes (fst (Seq.index a i))  (fst (Seq.index b i)) /\ eq_bytes (snd (Seq.index a i))  (snd (Seq.index b i))))) =
         eq_querystring_lemma_helper_1 a b;
         eq_querystring_lemma_helper_2 a b

let eq_querystring_reflexive_lemma a = eq_querystring_lemma a a

let eq_request_uri_reflexive_lemma a = ()

let is_request_uri_publishable #pr trace_idx r =
  is_seq_bytes_publishable #pr trace_idx r.uri_path /\ is_seq_bytes_pairs_publishable #pr trace_idx r.uri_querystring /\ (Some? r.uri_fragment ==> LC.is_publishable_p pr trace_idx (Some?.v r.uri_fragment))

let eq_url_reflexive_lemma a = ()

let rec eq_sequence_url s_url1 s_url2 =
  if Seq.length s_url1 = Seq.length s_url2 then(
    if Seq.length s_url1 > 0 then (
      eq_url (Seq.head s_url1) (Seq.head s_url2) &&
      eq_sequence_url (Seq.tail s_url1) (Seq.tail s_url2)
    )else true
  )else false

let rec get_header_from_headers header_name headers current_index =
  if current_index >= Seq.length headers then None
  else
  if eq_bytes (fst (Seq.index headers current_index)) (string_to_bytes header_name) then
    let result = Seq.index headers current_index in
    Seq.Properties.contains_intro headers current_index result;
    Some result
  else
    get_header_from_headers header_name headers (current_index + 1)


let get_header_from_headers_singleton s t = ()

let rec is_mem_of_seq_urls (u:url) (s:Seq.seq url): Tot bool (decreases (length s)) =
  if length s = 0 then 
    false 
  else(
    let hd = Seq.head s in
    let tl = Seq.tail s in
    if eq_url hd u then
      true
    else
      is_mem_of_seq_urls u tl
  )

let rec is_subset_of_seq_urls (s1:Seq.seq url) (s2:Seq.seq url): Tot bool (decreases (length s1)) =
  if length s1 = 0 then 
    true
  else(
    let hd = Seq.head s1 in
    let tl = Seq.tail s1 in
    is_mem_of_seq_urls hd s2 && is_subset_of_seq_urls tl s2
  )

let is_same_set_of_urls s1 s2 =
  is_subset_of_seq_urls s1 s2 && is_subset_of_seq_urls s2 s1
  
