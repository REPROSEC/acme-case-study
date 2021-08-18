/// DY.Trace (implementation)
/// =========================

module DY.Trace
open DY.Crypto
open DY.Principals
open DY.Labels
open DY.Entry
open DY.Monad
open Helpers
friend DY.Crypto

val discard: bool -> DY unit
  (requires (fun _ -> True))  (ensures (fun t0 _ t1 -> t0 == t1))
let discard _ = ()
let tot_print_string s = IO.debug_print_string s

let print_string s = discard (IO.debug_print_string s)

let print_bytes t = print_string (sprint_bytes t)

val print_seq_entry: i:nat -> s:Seq.seq entry_t -> DY unit
		     (requires fun t0 -> True)
		     (ensures fun t0 _ t1 -> t0 == t1)
		     (decreases (Seq.length s - i))
let rec print_seq_entry (i:nat) (s:Seq.seq entry_t) =
  if i >= Seq.length s then ()
  else (print_string (sprint_entry i s.[i]);
	print_string "\n";
        print_seq_entry (i+1) s)

let print_trace () =
  let t = get () in
  print_seq_entry 0 t


let init () = ()

let current_trace_len () = current_trace_len ()

#push-options "--z3rlimit 200"//--max_fuel 2 --max_ifuel 2  --z3cliopt 'smt.qi.eager_threshold=40'"
let gen l u up =
  let t0 = get() in
  let n = Seq.length t0 in
  let t = mk_nonce n l u in
  write_at_end (Gen t l u up);
  let t1 = get() in
  assert (trace_len t1 = trace_len t0 + 1);
  Seq.un_snoc_snoc t0 (Gen t l u up);
  assert (Seq.index t1 (Seq.length t0) == (Gen t l u up));
  let p = entry_at_pred n (Gen t l u up) in
  assert (p t1);
  let _ = witness p in
  assert (witnessed p);
  assert (entry_at n (Gen t l u up));
  assert (is_nonce_generated_at n t l u up);
  assert (forall t'. is_published_at n t' ==> False);
  t
#pop-options

let trigger_event p ev =
  let t0 = get () in
  write_at_end (Event p ev);
  Seq.un_snoc_snoc t0 (Event p ev);
  let pr = entry_at_pred (Seq.length t0) (Event p ev) in
  witness pr; assert (witnessed pr);
  assert (did_event_occur_at (Seq.length t0) p ev);
  assert (forall t'. is_published_at (Seq.length t0) t' ==> False)


let send p1 p2 t =
  let t0 = get() in
  let i = Seq.length t0 in
  write_at_end (Message p1 p2 t);
  let t1 = get() in
  assert (t1 == Seq.snoc t0 (Message p1 p2 t));
  Seq.un_snoc_snoc t0 (Message p1 p2 t);
  let pr = entry_at_pred (Seq.length t0) (Message p1 p2 t) in
  witness pr; assert (witnessed pr);
  assert (is_published_at i t);
  i


let authenticated_send p1 p2 t =
  let t0 = get() in
  let i = Seq.length t0 in
  write_at_end (AuthenticatedMessage p1 p2 t);
  let t1 = get() in
  assert (t1 == Seq.snoc t0 (AuthenticatedMessage p1 p2 t));
  Seq.un_snoc_snoc t0 (AuthenticatedMessage p1 p2 t);
  let pr = entry_at_pred (Seq.length t0) (AuthenticatedMessage p1 p2 t) in
  witness pr; assert (witnessed pr);
  assert (is_auth_published_at i t);
  i


let receive_i i p2 =
  let t0 = get() in
  match Seq.index t0 i with
  | Message p1 p' m ->
// We could check for intended target, but this is unauthenticated
	let pr = entry_at_pred i (Message p1 p' m) in
	assert (pr t0);
	witness pr; assert (witnessed pr);
        assert(entry_at i (Message p1 p' m));
        assert(t0.[i] == Message p1 p' m);
        assert(is_message_sent_at i p1 p' m);
        (p1,m)
  | e -> error "message not found"


let authenticated_receive_i i p2 =
  let t0 = get() in
  match Seq.index t0 i with
  | AuthenticatedMessage p1 p' m ->
	let pr = entry_at_pred i (AuthenticatedMessage p1 p' m) in
	assert (pr t0);
	witness pr; assert (witnessed pr);
        assert(entry_at i (AuthenticatedMessage p1 p' m));
        assert(t0.[i] == AuthenticatedMessage p1 p' m);
        assert(is_authenticated_message_sent_at i p1 p' m);
        (m, p1)
  | e -> error "message not found"


let set_state p v s =
  let t0 = get() in
  let i = Seq.length t0 in
  write_at_end (SetState p v s);
  let t1 = get() in
  assert (t1 == Seq.snoc t0 (SetState p v s));
  Seq.un_snoc_snoc t0 (SetState p v s);
  let pr = entry_at_pred (Seq.length t0) (SetState p v s) in
  witness pr; assert (witnessed pr);
  assert (is_set_state_at i p v s);
  assert (forall t'. is_published_at i t' ==> False);
  ()

let get_state_i i p =
  let t0 = get() in
  match Seq.index t0 i with
  | SetState p' v s ->
     let pr = entry_at_pred i (SetState p' v s) in
     assert (pr t0); witness pr; assert (witnessed pr);
     assert (is_set_state_at i p' v s);
     if p = p' then (v,s)
     else error "state stored by incorrect principal"
  | e -> error "no state stored at given index"



/// get_last_state_before
/// ---------------------

let rec get_last_state_before i p =
  let t0 = get() in
  match Seq.index t0 i with
  | SetState p' v s ->
      let pr = entry_at_pred i (SetState p' v s) in
      assert (pr t0); witness pr; assert (witnessed pr);
      assert (is_set_state_at i p' v s);
      if p = p' then ( // Check whether this is actually an update for the correct principal
        assert(is_set_state_at i p v s);
        Some (i,v,s)
      ) else if i > 0 then ( // Is wasn't an update for the correct pricipal
        let jo = get_last_state_before (i-1) p in
        match jo with
        | Some (j,v',s') -> assert (is_set_state_at j p v' s');
			   assert (forall v' s'. ~ (is_set_state_at i p v' s'));
			   Some (j,v',s')
        | None -> (assert (forall j s. j <= (i-1) ==> ~ (is_set_state_at j p v s));
		  assert (is_set_state_at i p' v s);
                  None)
      ) else (
        assert (is_set_state_at i p' v s);
        None //error "update for wrong principal"
      )
  | e ->
      let pr = entry_at_pred i e in
      witness pr; assert (witnessed pr);
      assert(entry_at i e);
      if i > 0 then
        get_last_state_before (i-1) p
      else
        None //error "update not found"

let compromise p s v =
  let t0 = get() in
  let i = Seq.length t0 in
  write_at_end (Corrupt p s v);
  let t1 = get() in
  assert (t1 == Seq.snoc t0 (Corrupt p s v));
  Seq.un_snoc_snoc t0 (Corrupt p s v);
  let pr = entry_at_pred i (Corrupt p s v) in
  assert (pr t1); witness pr; assert (witnessed pr);
  assert (is_corrupted_at i p s v)
