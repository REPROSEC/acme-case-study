/// DY.AttackerAPI (implementation)
/// ===============================
module DY.AttackerAPI

(* A Dolev-Yao Model Using Monotonic State *)

module P = DY.Principals
module L = DY.Labels
module C = DY.Crypto
open DY.Entry
open DY.Monad
open DY.Trace

#set-options "--max_fuel 2 --max_ifuel 2 --z3rlimit 50"
let attacker_can_query_compromised_state idx_state idx_corrupt idx_query principal si sv tag res =
  assert (query_result idx_state principal si sv tag res);
  assert (exists tag. query_result idx_state principal si sv tag res)

let rec attacker_can_derive_in_more_steps i steps1 steps2 =
  if steps2 = 0 then ()
  else if steps1 = steps2 then ()
       else (attacker_can_derive_in_more_steps i steps1 (steps2 - 1))


let rec attacker_can_derive_later i steps j =
  if steps = 0 then ()
  else (attacker_can_derive_later i (steps - 1) j)

let attacker_knows_later i j =
  let attacker_knows_later_steps (steps:nat) (a:bytes):
    Lemma (ensures (attacker_can_derive i steps a ==> attacker_can_derive j steps a))
          [SMTPat (attacker_can_derive i steps a); SMTPat (attacker_can_derive j steps a)] =
          attacker_can_derive_later i steps j in 
  ()


let literal_to_pub_bytes l : pub_bytes 0 =
  let t = C.literal_to_bytes l in
  assert (attacker_can_derive 0 0 t);
  assert (attacker_knows_at 0 t);
  t

let from_literal_lemma l = ()

let bytes_to_string #i t =
    match C.bytes_to_string t with
    | Success s -> s
    | Error e -> err e


(* Generate public fresh (random) values *)

let max a b = if a < b then b else a
val meet_derives: i:nat -> j:nat -> steps1:nat -> steps2:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2) t1 /\
                  attacker_can_derive (max i j) (max steps1 steps2) t2))
let meet_derives i j steps1 steps2 t1 t2 =
  (if steps1 < steps2 then
    attacker_can_derive_in_more_steps i steps1 steps2
   else
    attacker_can_derive_in_more_steps j steps2 steps1);
  (if i < j then
    attacker_can_derive_later i (max steps1 steps2) j
   else
    attacker_can_derive_later j (max steps1 steps2) i);
   assert (attacker_can_derive (max i j) (max steps1 steps2) t1);
   assert (attacker_can_derive (max i j) (max steps1 steps2) t2)


(* Concatenate and split bytestrings *)
let incr a  = a + 1

#push-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 0"
let concat #i t1 t2 =
  let concat_pub_lemma0 (i:nat) (t1:C.bytes) (t2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (C.concat t1 t2)))
        [SMTPat (attacker_can_derive i steps t1); SMTPat (attacker_can_derive i steps t2)] =
        () in
  let concat_pub_lemma (i:nat) (j:nat) (t1:C.bytes) (t2:C.bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.concat t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.concat t1 t2));
   () in
let c = C.concat t1 t2 in
c
#pop-options

let concat_lemma #i t1 t2 = ()

let split #i t =
  let split_pub_lemma1 (i:nat) (a1:C.bytes) (a:C.bytes) (a2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps a1 /\ is_succ2 (C.split a1) a a2))
        (ensures (attacker_can_derive i (steps + 1) a))
        [SMTPat (attacker_can_derive i steps a1); SMTPat (is_succ2 (C.split a1) a a2)] =  () in
  let split_pub_lemma2 (i:nat) (a1:C.bytes) (a:C.bytes) (a2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps a1 /\ is_succ2 (C.split a1) a2 a))
        (ensures (attacker_can_derive i (steps + 1) a))
        [SMTPat (attacker_can_derive i steps a1); SMTPat (is_succ2 (C.split a1) a2 a)] =  () in
  match C.split t with
  | Success (a1,a2) -> (
    assert (is_succ2 (C.split t) a1 a2);
    let p1:pub_bytes i = a1 in
    let p2:pub_bytes i = a2 in
    assert (C.split t == Success (a1,a2));
    (a1,a2))
  | Error s -> (assert (match C.split t with | Error s -> True | Success _ -> False); err s)

(* Public key corresponding to a secret key *)
let pk #i k =
  let pk_pub_lemma (i:nat) (s:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps s))
        (ensures (attacker_can_derive i (steps + 1) (C.pk s)))
        [SMTPat (attacker_can_derive i steps s)] = () in
  C.pk k
let pk_lemma #i s = ()

(* Public key encryption *)

let pke_enc #i t1 t2 =
  let pke_enc_pub_lemma0 (i:nat) (t1:C.bytes) (t2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (C.pke_enc t1 t2)))
        [SMTPat (attacker_can_derive i steps t1); SMTPat (attacker_can_derive i steps t2)] = () in
  let pke_enc_pub_lemma (i:nat) (j:nat) (t1:C.bytes) (t2:C.bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.pke_enc t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.pke_enc t1 t2)) in
  C.pke_enc t1 t2

let pke_enc_lemma #i t1 t2 = ()

#push-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2"
let pke_dec #i k e =
  let pke_dec_pub_lemma0 (i:nat) (k:C.bytes) (e:C.bytes) (p:C.bytes) (steps:nat):
  Lemma (requires (attacker_can_derive i steps k /\
                   attacker_can_derive i steps e /\
                   is_succ (C.pke_dec k e) p))
        (ensures (attacker_can_derive i (steps + 1) p))
        [SMTPat (attacker_can_derive i steps k);
         SMTPat (attacker_can_derive i steps e);
         SMTPat (is_succ (C.pke_dec k e) p)] = () in
  let pke_dec_pub_lemma (i:nat) (j:nat) (k:C.bytes) (e:C.bytes) (p:C.bytes) (steps1:nat) (steps2:nat):
  Lemma (requires (attacker_can_derive i steps1 k /\
                   attacker_can_derive j steps2 e /\
                   is_succ (C.pke_dec k e) p))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) p))
        [SMTPat (attacker_can_derive i steps1 k);
         SMTPat (attacker_can_derive j steps2 e);
         SMTPat (is_succ (C.pke_dec k e) p)] =
         meet_derives i j steps1 steps2 k e;
         assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) p) in
  match C.pke_dec k e  with
  | Success p ->
    assert (is_succ (C.pke_dec k e) p);
    let p:pub_bytes i = p in
    p
  | Error s -> err s
#pop-options

let ae_enc #i t1 t2 =
  let ae_enc_pub_lemma0 (i:nat) (t1:C.bytes) (t2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (C.aead_enc t1 t2 None)))
        [SMTPat (attacker_can_derive i steps t1); SMTPat (attacker_can_derive i steps t2)] = () in
  let ae_enc_pub_lemma (i:nat) (j:nat) (t1:C.bytes) (t2:C.bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.aead_enc t1 t2 None)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.aead_enc t1 t2 None)) in
  C.aead_enc t1 t2 None

let ae_enc_lemma #i t1 t2 = ()


let ae_dec #i k e =
  let ae_dec_pub_lemma0 (i:nat) (k:C.bytes) (e:C.bytes) (p:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps k /\
                   attacker_can_derive i steps e /\
                   is_succ (C.aead_dec k e None) p))
        (ensures (attacker_can_derive i (steps + 1) p))
        [SMTPat (attacker_can_derive i steps k);
         SMTPat (attacker_can_derive i steps e);
         SMTPat (is_succ (C.aead_dec k e None) p)] = () in
  let ae_dec_pub_lemma (i:nat) (j:nat) (k:C.bytes) (e:C.bytes) (p:C.bytes) (steps1:nat) (steps2:nat):
  Lemma (requires (attacker_can_derive i steps1 k /\
                   attacker_can_derive j steps2 e /\
                   is_succ (C.aead_dec k e None) p))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) p))
        [SMTPat (attacker_can_derive i steps1 k);
         SMTPat (attacker_can_derive j steps2 e);
         SMTPat (is_succ (C.aead_dec k e None) p)] =
         meet_derives i j steps1 steps2 k e;
        assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) p) in
  match C.aead_dec k e None with
  | Success p ->
    assert (is_succ (C.aead_dec k e None) p);
    let p:pub_bytes i = p in
    p
  | Error s -> err s

let sign #i t1 t2 =
  let sign_pub_lemma0 (i:nat) (t1:C.bytes) (t2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (C.sign t1 t2)))
         = () in
  let sign_pub_lemma (i:nat) (j:nat) (t1:C.bytes) (t2:C.bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.sign t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        sign_pub_lemma0 (max i j) t1 t2 (max steps1 steps2) in
  C.sign t1 t2

let sign_lemma #i t1 t2 = ()

let verify #i t1 t2 t3 = C.verify t1 t2 t3
let verify_lemma #i t1 t2 t3 = ()

let ceo_gen #i t1 =
  let ceo_gen_pub_lemma (i:nat) (t1:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1))
        (ensures (attacker_can_derive i (steps + 1) (C.ceo_gen t1)))
	[SMTPat (attacker_can_derive i steps t1)]
         = () in
  C.ceo_gen t1

let ceo_gen_lemma #i t1 = ()

let deo_gen #i t1 t2 =
  let deo_gen_pub_lemma0 (i:nat) (t1:C.bytes) (t2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (C.deo_gen t1 t2)))
         = () in
  let deo_gen_pub_lemma (i:nat) (j:nat) (t1:C.bytes) (t2:C.bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.deo_gen t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        deo_gen_pub_lemma0 (max i j) t1 t2 (max steps1 steps2) in
  C.deo_gen t1 t2

let deo_gen_lemma #i t1 t2 = ()


let mac #i t1 t2 =
  let mac_pub_lemma0 (i:nat) (t1:C.bytes) (t2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (C.mac t1 t2)))
         = () in
  let mac_pub_lemma (i:nat) (j:nat) (t1:C.bytes) (t2:C.bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.mac t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        mac_pub_lemma0 (max i j) t1 t2 (max steps1 steps2) in
  C.mac t1 t2
let mac_lemma #i t1 t2 = ()

let verify_mac #i t1 t2 t3 = C.verify_mac t1 t2 t3
let verify_mac_lemma #i t1 t2 t3 = ()

let hash #i t1 =
  let hash_pub_lemma0 (i:nat) (t1:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1))
        (ensures (attacker_can_derive i (steps + 1) (C.hash t1)))
         = () in
  let hash_pub_lemma (i:nat) (t1:C.bytes) (steps1:nat):
  Lemma (requires (attacker_can_derive i steps1 t1))
        (ensures (attacker_can_derive i (steps1 + 1) (C.hash t1)))
        [SMTPat (attacker_can_derive i steps1 t1)] =
        hash_pub_lemma0 i t1 steps1 in
  C.hash t1
let hash_lemma #i t1 = ()

let dh #i t1 t2 =
  let dh_pub_lemma0 (i:nat) (t1:C.bytes) (t2:C.bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2 /\ C.is_pk t2))
        (ensures (attacker_can_derive i (steps + 1) (C.dh t1 t2)))
         = () in
  let dh_pub_lemma (i:nat) (j:nat) (t1:C.bytes) (t2:C.bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2 /\ C.is_pk t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (C.dh t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        dh_pub_lemma0 (max i j) t1 t2 (max steps1 steps2) in
  C.dh t1 t2
let dh_lemma #i t1 t2 = ()

let current_trace_len () = current_trace_len ()

#push-options "--max_ifuel 2 --z3rlimit 200"
let pub_gen u =
  let t0 = get () in
  let n = gen L.public u (C.default_usage_pred u) in
  let t1 = get() in
  let i = send "*" "*" n in
  let t2 = get() in
  assert (is_published_at (trace_len t0 + 1) n);
  assert (attacker_can_derive (trace_len t0+2) 0 n);
  let i = current_trace_len () in
  assert (i == trace_len  t2);
  (|i, n|)

let send #i p1 p2 a = send p1 p2 a

let receive_i i p2 =
  let (_,m) = receive_i i p2 in
  let n = current_trace_len () in
  assert (is_published_at i m);
  assert (is_published_before i m);
  assert (attacker_can_derive (i+1) 0 m);
  assert (attacker_knows_at (i+1) m);
  let m' : pub_bytes (i+1) = m in
  (| n, m |)

let compromise p s v =
  let n = current_trace_len () in
  compromise p s v;
  n

let query_state_i idx_state idx_corrupt idx_query p si sv tag =
  let (v,s) = get_state_i idx_state p in
  assert (is_set_state_at idx_state p v s);
  if Seq.length v <= si || Seq.index v si <> sv || Seq.length s <> Seq.length v
  then error "cannot query state"
  else
    let n = current_trace_len () in
    match lookup s.[si] tag with
    | None -> error "lookup of tag failed"
    | Some x ->
        attacker_can_query_compromised_state idx_state idx_corrupt idx_query p si sv tag x;
        let v : pub_bytes n = x in
        v

let authenticated_receive_i i p2 =
  let (message,sender) = authenticated_receive_i i p2 in
  let n = current_trace_len () in
  assert (is_auth_published_at i message);
  assert (attacker_can_derive (i+1) 0 message);
  assert (attacker_knows_at (i+1) message);
  (| n, message, sender |)

let authenticated_send #i p1 p2 a =
  authenticated_send p1 p2 a

