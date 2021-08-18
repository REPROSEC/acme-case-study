/// Labeled.ApplicationAPI (implementation)
/// =======================================
module Labeled.ApplicationAPI

#set-options "--max_fuel 2 --max_ifuel 2 --z3rlimit 300"

let valid_trace (tr:trace) =
  (forall (i:nat) (t:bytes). i < trace_len tr ==> (is_published_at i t ==> (L.is_publishable_p app_preds i t))) /\
  (forall (i:nat) (t:bytes). i < trace_len tr ==> (is_auth_published_at i t ==> (L.is_publishable_p app_preds i t))) /\
  (forall (i:nat) (t:bytes) (l:label) (u:usage) (up:usage_pred u). i < trace_len tr ==> (is_nonce_generated_at i t l u up ==> L.are_kdf_labels_increasing L.(app_preds.model.corrupt_at i) l u)) /\
  (forall (i:nat) (p:principal) (v:version_vec) (s:principal_state). i < trace_len tr ==> (is_set_state_at i p v s ==> (is_principal_state_readable i p v s /\ state_inv i p v s))) /\
  (forall (i:nat) (s:principal) (r:principal) (msg:bytes). i < trace_len tr ==>
  (is_authenticated_message_sent_at i s r msg ==>
    (corrupt_at i (any s) \/ authenticated_send_pred i s r msg))) /\
  (forall (i:nat) (s:principal) (e:event). i < trace_len tr ==> (did_event_occur_at i s e ==> (event_pred i s e)))

let valid_trace_event_lemma t i s e = ()

let valid_trace_respects_state_inv trace i p v s = ()

let corrupt_principals_have_publishable_state_at tr i =
  let corrupt_principal_has_publishable_state (i:nat) (j:nat) (p:principal) (v:version_vec) (s:principal_state) (session_index:nat) (t:string) (x:bytes) :
    Lemma (requires (
          is_principal_state_readable i p v s /\
          Seq.length v = Seq.length s /\
          session_index < Seq.length v /\
          is_some (lookup s.[session_index] t) x /\
	  i <= j /\
          corrupt_at j (sess_ver p session_index (Seq.index v session_index))
        ))
        (ensures (L.is_publishable_p app_preds j x))
	[SMTPat (is_principal_state_readable i p v s);
	 SMTPat (lookup s.[session_index] t);
	 SMTPat (L.is_publishable_p app_preds j x)] = corrupt_principal_has_publishable_state i j p v s session_index t x in
  assert (valid_trace tr);
  assert (forall j p v s si k x.
    (j < i /\ is_set_state_at j p v s /\
     si < Seq.length v /\ corrupt_at i (sess_ver p si v.[si]) /\ is_some (lookup s.[si] k) x) ==> (is_principal_state_readable j p v s /\ Seq.length v = Seq.length s));
  assert (forall j p v s si k x.
    (j < i /\ is_set_state_at j p v s /\
     si < Seq.length v /\ corrupt_at i (sess_ver p si v.[si]) /\ is_some (lookup s.[si] k) x) ==> L.is_publishable_p app_preds i x);
  L.can_label_of_bytes_flow_later_forall app_preds;
  ()


let published_value_at_is_publishable tr i t = L.can_label_of_bytes_flow_later_forall app_preds

let published_value_is_publishable tr i t = L.can_label_of_bytes_flow_later_forall app_preds

let auth_published_value_at_is_publishable tr i t = L.can_label_of_bytes_flow_later_forall app_preds

let auth_published_value_is_publishable tr i t = L.can_label_of_bytes_flow_later_forall app_preds

(* Crypto API *)


/// Labeled bytes API for applications
/// ----------------------------------

let literal_to_bytes s =
  assert (L.is_labeled_p app_preds 0 (C.literal_to_bytes s) public);
  C.literal_to_bytes s

let literal_to_bytes_lemma s = ()

let bytes_to_literal #l s =
    match C.bytes_to_literal s with
    | Success s -> s
    | Error s -> err s

let bytes_to_literal_lemma s = ()

let string_to_bytes_lemma s = ()

let bytes_to_string #l s =
  match C.bytes_to_string s with
  | Success s -> s
  | Error s -> err s

let bytes_to_string_lemma s = ()

let nat_to_bytes_lemma s = ()

let bytes_to_nat #l s =
  match C.bytes_to_nat s with
  | Success s -> s
  | Error s -> err s

let bytes_to_nat_lemma pr s = ()

let concat #i #l t1 t2 =
  L.can_label_of_bytes_flow_later_forall app_preds;
  assert (exists k. L.can_label_of_bytes_flow_to app_preds k t1 l /\
	       L.can_label_of_bytes_flow_to app_preds k t2 l);
  C.concat t1 t2

let concat_lemma #i #l t1 t2 = ()

let split #i #l t =
  match C.split t with
  | Success (a,b) -> (a,b)
  | Error s -> err s


let split_lemma #i #l t = ()

let pk #i #l #up s = C.pk s

let pk_lemma #i #l #up s = ()

let vk #i #l #up s = C.pk s

let vk_lemma #i #l #up s = ()

let pk_un #i #l s = C.pk s

let pk_un_lemma #i #l s = ()

let dh_pk #i #l #up s = C.pk s

let dh_pk_lemma #i #l #up s = ()

let pke_enc #i #l #up p m =
  L.pke_pred_later_forall ();
  L.can_label_of_bytes_flow_later_forall app_preds;
  assert (exists k. L.is_public_enc_key_p app_preds k p l up /\
	       L.can_label_of_bytes_flow_to app_preds k m l /\ C.pke_pred up k m);
  C.pke_enc p m

let pke_enc_lemma #i #l #up p m = ()

let pke_dec #i #l #up s c =
  match C.pke_dec s c with
  | Success m -> m
  | Error s -> err s

let sign #i #l1 #up #l2 k m =
  sign k m

let sign_lemma #i #l1 #up #ps k m = ()

let verify #i #l1 #up #l2 p m t = C.verify p m t

let verify_lemma #i #l1 #up #l2 p m t = ()

let aead_enc #l #up k m ad = C.aead_enc k m (to_opt_bytes ad)

let aead_enc_lemma #ps #up k m ad = ()

let aead_dec #i #l #up k c ad =
  L.aead_dec_labeled_lemma #app_preds #i #l #up k c (to_opt_bytes ad);
  match C.aead_dec k c (to_opt_bytes ad) with
  | Success p -> p
  | Error s -> err s

let mac #l1 #up #l2 k m = C.mac k m

let mac_lemma #l1 #up #l2 k m = ()

let verify_mac #l1 #up #l2 k m t =
  C.verify_mac k m t

let verify_mac_lemma #l1 #up #l2 k m t = ()

let dh #l #u #up #l' priv pub = C.dh priv pub

let dh_lemma #l #u #up #l' k pk = ()

let dh_un #i #l #u #up k pk = 
  let c = L.dh_un #app_preds #i #l #u #up k pk in
  assert (C.is_pk pk ==> (c == C.dh k pk /\ L.can_label_of_bytes_flow_to app_preds i c l /\ 
			  (match L.get_label_of_secret c with 
			  | Some l' -> l' == (L.get_label c) 
			  | None -> L.get_label c == public) /\
			  (match L.get_label_and_usage_of_private_key pk with  
			  | Some (l', u') -> if C.eq_usage u' (C.dh_key_usage u) then 
					       (L.get_usage_of_secret c == Some u \/ 
						 L.get_usage_of_secret c == C.get_dh_usage u') /\ 
						   (eq_label (L.get_label c) (join l l'))
					    else True 
			  | None -> True)));
  c
  
let hash #l m = hash m

let kdf_extract #l1 #l2 #u1 #u2 #up1 #up2 k c = C.kdf k c true
let kdf_expand #l1 #l2 #u1 #u2 #up1 #up2 k c = C.kdf k c false

let kdf_extract_lemma #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()
let kdf_expand_lemma #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()

let kdf_extract_usage_lemma #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()
let kdf_expand_usage_lemma #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()

(* Stateful Trace API *)

let secret_gen l u (up:usage_pred u) =
  let tr0 = get() in
  let n = current_trace_len () in
  let t = gen l u up in
  L.labeled_nonce_forall app_preds;
  assert L.(app_preds.model.is_generated n t l u up);
  assert (t == gnonce n l u);
  assert L.(get_usage_of_secret t == Some u);
  assert (is_secret_at n t l u up);
  (|n,t|)

let guid_gen () =
  let tr0 = get() in
  let idx = current_trace_len () in
  let up = default_usage_pred guid_usage in
  let n = gen public guid_usage up in
  assert L.(app_preds.model.is_generated (trace_len tr0) n public guid_usage up);
  assert (can_flow_at idx public public);
  let i = send "*" "*" n in
  assert (is_published_at (trace_len tr0 + 1) n);
  assert (DY.AttackerAPI.attacker_can_derive (trace_len tr0+2) 0 n);
  L.labeled_nonce_forall app_preds;
  let n:lbytes_at idx public = n in
  (|idx,n|)

let trigger_event p (ev,pl) =
  let t0 = get() in
  trigger_event p (ev,pl);
  let t1 = get() in
  assert (trace_len t1 = trace_len t0 + 1);
  assert (did_event_occur_at (trace_len t0) p (ev,pl));
  assert (valid_trace t1)

let send #i p1 p2 m =
  L.can_label_of_bytes_flow_later_forall app_preds;
  let i = send p1 p2 m in
  i

let authenticated_send #i p1 p2 m =
  L.can_label_of_bytes_flow_later_forall app_preds;
  let i = authenticated_send p1 p2 m in
  i

let receive_i i p =
 let now = current_trace_len () in
 let t0 = get() in
 assert (now == trace_len t0);
 if i < now then
   let (s,t) = receive_i i p in
   assert (is_published_at i t);
   (|now,s,t|)
 else error "given index >= trace_len"

let authenticated_receive_i i p =
  let now = current_trace_len () in
  if i < now then
  let (t,s) = authenticated_receive_i i p in
  (|now,s,t|)
  else error "wrong message index"

let set_state p v s = set_state p v s

let get_state_i i p =
  let now = current_trace_len () in
  if i < now then (
    let (v,s) = get_state_i i p in
    let tr = get() in
    existing_current_state_implies_state_was_set i p v s;
    assert (exists j. j < trace_len tr /\ is_set_state_at j p v s);
    state_inv_later i now p v s;
    (|now,v,s|))
  else error "wrong set_state index"

let get_last_state p =
  let now = current_trace_len () in
  if now = 0 then error "no last state found" else
  match get_last_state_before (now - 1) p with
  | None -> error "no last state found"
  | Some (i,v,st) ->
    state_inv_later i now p v st;
    (| now, v, st |)

let has_state_set p =
  let now = current_trace_len () in
  if now = 0 then false else
  match get_last_state_before (now - 1) p with
  | None -> false
  | Some _ -> true

let publishable_of_secret_implies_corruption #i #l #u #up s =
  L.publishable_of_secret_implies_corruption #app_preds #i #l #u #up s

let restrict #i #l1 t l2 =
  L.restrict #app_preds #i #l1 t l2
    
let is_set_state_at_implies_set_state_before_now i p v st = entry_at_before_now i (SetState p v st)
