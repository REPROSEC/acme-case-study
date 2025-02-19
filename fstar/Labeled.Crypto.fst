/// Labeled.Crypto (implementation)
/// ===============================
module Labeled.Crypto
open DY.Labels
friend DY.Labels
open DY.Crypto
friend DY.Crypto
#set-options "--z3rlimit 100 --max_fuel 2"

let includes_is_reflexive l = ()

/// ``can_flow`` predicate for labels
/// ---------------------------------

let rec can_flow c l1 l2 : Type0 =
  match l1,l2 with
      // Public can flow to anything
      | Public, _ -> True
      // Labels with corrupt vsessionids flow to public
      | ReadableBy ps, Public -> contains_corrupt_principal c ps
      // [l1] flows to [l2] if [l1] is a superset of [l2] or some vsessionid in [l1] is corrupt
      | ReadableBy ps1, ReadableBy ps2 -> contains_corrupt_principal c ps1 \/ includes ps1 ps2
      // [ReadableBy ps] flows to [Meet a b] if [ReadableBy ps] flows to at least one of [a] or [b]
      | ReadableBy ps, Meet l21 l22 -> can_flow c l1 l21 \/ can_flow c l1 l22
      // [ReadableBy ps] flows to [Join a b] if [ReadableBy ps] flows to both [a] and [b]
      | ReadableBy ps, Join l21 l22 -> can_flow c l1 l21 /\ can_flow c l1 l22
      | Join l11 l12, Public -> can_flow c l11 l2 \/ can_flow c l12 l2
      | Join l11 l12, ReadableBy _ -> can_flow c l11 l2 \/ can_flow c l12 l2
      | Meet l11 l12, Public ->  can_flow c l11 l2 /\ can_flow c l12 l2
      | Meet l11 l12, ReadableBy _ ->  can_flow c l11 l2 /\ can_flow c l12 l2
      | Join l11 l12, Meet l21 l22 -> can_flow c l1 l21 \/ can_flow c l1 l22 \/ can_flow c l11 l2 \/ can_flow c l12 l2
      | Meet l11 l12, Meet l21 l22 -> can_flow c l1 l21 \/ can_flow c l1 l22 \/ (can_flow c l11 l2 /\ can_flow c l12 l2)
      | Meet l11 l12, Join l21 l22 -> can_flow c l1 l21 /\ can_flow c l1 l22 \/ (can_flow c l11 l2 /\ can_flow c l12 l2)
      | Join l11 l12, Join l21 l22 -> can_flow c l1 l21 /\ can_flow c l1 l22 \/ (can_flow c l11 l2 \/ can_flow c l12 l2)


let corrupt_can_flow_to_public c ps = ()

val corrupt_prin_with_more_corruption: c1:T.corrupt_pred -> c2:T.corrupt_pred -> ps: secret_intendees ->
  Lemma (requires (forall p. c1 p ==> c2 p))
        (ensures (contains_corrupt_principal c1 ps ==> contains_corrupt_principal c2 ps))
let corrupt_prin_with_more_corruption c1 c2 ps =  ()

let rec can_flow_with_more_corruption c1 c2 l1 l2 =
  match l1,l2 with
      | Public, _ -> ()
      | ReadableBy ps, Public -> corrupt_prin_with_more_corruption c1 c2 ps
      | ReadableBy ps1, ReadableBy ps2 -> corrupt_prin_with_more_corruption c1 c2 ps1
      | ReadableBy ps, Meet l21 l22 -> can_flow_with_more_corruption c1 c2 l1 l21; can_flow_with_more_corruption c1 c2 l1 l22
      | ReadableBy ps, Join l21 l22 -> can_flow_with_more_corruption c1 c2 l1 l21; can_flow_with_more_corruption c1 c2 l1 l22
      | Join l11 l12, Public
      | Join l11 l12, ReadableBy _ ->
                           can_flow_with_more_corruption c1 c2 l11  l2;
                           can_flow_with_more_corruption c1 c2 l12 l2
      | Meet l11 l12, Public
      | Meet l11 l12, ReadableBy _ -> can_flow_with_more_corruption c1 c2 l11  l2;
                          can_flow_with_more_corruption c1 c2 l12 l2
      | Join l11 l12, Meet l21 l22
      | Join l11 l12, Join l21 l22
      | Meet l11 l12, Meet l21 l22
      | Meet l11 l12, Join l21 l22 ->
                               can_flow_with_more_corruption c1 c2 l1 l21;
                               can_flow_with_more_corruption c1 c2 l1 l22;
                               can_flow_with_more_corruption c1 c2 l11 l2;
                               can_flow_with_more_corruption c1 c2 l12 l2


let rec flows_to_public_can_flow c (l1:label) (l2:label) =
    match l1, l2 with
      | Public, _ -> ()
      | ReadableBy ps1 , Public -> ()
      | ReadableBy ps1, ReadableBy ps2 -> ()
      | ReadableBy ps, Meet l21 l22 -> flows_to_public_can_flow c l1 l21; flows_to_public_can_flow c l1 l22
      | ReadableBy ps, Join l21 l22 -> flows_to_public_can_flow c l1 l21; flows_to_public_can_flow c l1 l22
      | Join l11 l12, Public
      | Join l11 l12, ReadableBy _ ->  flows_to_public_can_flow c l11 l2; flows_to_public_can_flow c l12 l2
      | Meet l11 l12, Public
      | Meet l11 l12, ReadableBy _ ->  flows_to_public_can_flow c l11 l2; flows_to_public_can_flow c l12 l2
      | Join l11 l12, Meet l21 l22
      | Join l11 l12, Join l21 l22
      | Meet l11 l12, Meet l21 l22
      | Meet l11 l12, Join l21 l22 -> flows_to_public_can_flow c l1 l21; flows_to_public_can_flow c l1 l22;
                                     flows_to_public_can_flow c l11 l2; flows_to_public_can_flow c l12 l2


let can_flow_from_public c l = ()

let rec can_flow_flows_to_public (c:T.corrupt_pred) (l1:label) (l2:label) :
    Lemma ((can_flow c l2 Public /\ can_flow c l1 l2) ==> can_flow c l1 Public) =
    match l1, l2 with
      | Public, _ -> ()
      | ReadableBy ps1 , Public -> ()
      | ReadableBy ps1, ReadableBy ps2 -> ()
      | ReadableBy ps, Meet l21 l22 -> can_flow_flows_to_public c l1 l21;can_flow_flows_to_public c l1 l22
      | ReadableBy ps, Join l21 l22 -> can_flow_flows_to_public c l1 l21;can_flow_flows_to_public c l1 l22
      | Join l11 l12, Public
      | Join l11 l12, ReadableBy _ -> can_flow_flows_to_public c l11 l2;can_flow_flows_to_public c l12 l2
      | Meet l11 l12, Public
      | Meet l11 l12, ReadableBy _ -> can_flow_flows_to_public c l11 l2;can_flow_flows_to_public c l12 l2
      | Join l11 l12, Meet l21 l22
      | Join l11 l12, Join l21 l22
      | Meet l11 l12, Meet l21 l22
      | Meet l11 l12, Join l21 l22 -> can_flow_flows_to_public c l11 l2;can_flow_flows_to_public c l12 l2;
                                     can_flow_flows_to_public c l1 l21;can_flow_flows_to_public c l1 l22


let rec can_flow_transitive c l1 l2 l3 =
  match l1,l2,l3 with
  | Public, _, _ -> ()
  | _, Public, _ -> flows_to_public_can_flow c l1 l3
  | _, _, Public -> can_flow_flows_to_public c l1 l2; flows_to_public_can_flow c l1 l3
  | ReadableBy ps1,ReadableBy ps2,ReadableBy ps3 -> ()
  | ReadableBy ps1, ReadableBy ps2, Meet l31 l32 -> can_flow_transitive c l1 l2 l31; can_flow_transitive c l1 l2 l32
  | ReadableBy ps1, ReadableBy ps2, Join l31 l32 -> can_flow_transitive c l1 l2 l31; can_flow_transitive c l1 l2 l32
  | ReadableBy ps1, Join l21 l22, Public -> can_flow_transitive c l1 l21 l3; can_flow_transitive c l1 l22 l3
  | ReadableBy ps1, Join l21 l22, ReadableBy _ -> can_flow_transitive c l1 l21 l3; can_flow_transitive c l1 l22 l3
  | ReadableBy ps1, Meet l21 l22, Public -> can_flow_transitive c l1 l21 l3; can_flow_transitive c l1 l22 l3
  | ReadableBy ps1, Meet l21 l22, ReadableBy _ -> can_flow_transitive c l1 l21 l3; can_flow_transitive c l1 l22 l3

  | ReadableBy ps1, Join l21 l22, Meet l31 l32
  | ReadableBy ps1, Meet l21 l22, Meet l31 l32
  | ReadableBy ps1, Meet l21 l22, Join l31 l32
  | ReadableBy ps1, Join l21 l22, Join l31 l32 -> can_flow_transitive c l1 l2 l31; can_flow_transitive c l1 l2 l32;
                                                 can_flow_transitive c l1 l21 l3; can_flow_transitive c l1 l22 l3

  | Join l11 l12, Public, _
  | Join l11 l12, ReadableBy _, Public
  | Join l11 l12, ReadableBy _, ReadableBy _
  | Meet l11 l12, Public, _
  | Meet l11 l12, ReadableBy _, Public
  | Meet l11 l12, ReadableBy _, ReadableBy _
    -> can_flow_transitive c l11 l2 l3; can_flow_transitive c l12 l2 l3

  | Join l11 l12, ReadableBy _, Meet l31 l32
  | Join l11 l12, ReadableBy _, Join l31 l32
  | Meet l11 l12, ReadableBy _, Join l31 l32
  | Meet l11 l12, ReadableBy _, Meet l31 l32
    -> can_flow_transitive c l1 l2 l31; can_flow_transitive c l1 l2 l32

  | Join l11 l12, Join l21 l22, Public
  | Join l11 l12, Join l21 l22, ReadableBy _
  | Join l11 l12, Meet l21 l22, Public
  | Join l11 l12, Meet l21 l22, ReadableBy _
  | Meet l11 l12, Join l21 l22, Public
  | Meet l11 l12, Join l21 l22, ReadableBy _
  | Meet l11 l12, Meet l21 l22, Public
  | Meet l11 l12, Meet l21 l22, ReadableBy _
  -> can_flow_transitive c l1 l21 l3; can_flow_transitive c l1 l22 l3; can_flow_transitive c l11 l2 l3; can_flow_transitive c l12 l2 l3

  | Join l11 l12, Join l21 l22, Meet l31 l32
  | Join l11 l12, Join l21 l22, Join l31 l32
  | Join l11 l12, Meet l21 l22, Meet l31 l32
  | Join l11 l12, Meet l21 l22, Join l31 l32
  | Meet l11 l12, Join l21 l22, Meet l31 l32
  | Meet l11 l12, Join l21 l22, Join l31 l32
  | Meet l11 l12, Meet l21 l22, Meet l31 l32
  | Meet l11 l12, Meet l21 l22, Join l31 l32  ->
    can_flow_transitive c l1 l2 l31; can_flow_transitive c l1 l2 l32;
    can_flow_transitive c l1 l21 l3; can_flow_transitive c l1 l22 l3;
    can_flow_transitive c l11 l2 l3; can_flow_transitive c l12 l2 l3


let rec can_flow_reflexive c l =
  match l with
  | Public
  | ReadableBy _ -> ()
  | Meet l1 l2 -> can_flow_reflexive c l1;  can_flow_reflexive c l2;
                 can_flow_to_meet_left c l1 l1 l2; can_flow_to_meet_right c l2 l1 l2
  | Join l1 l2 -> can_flow_reflexive c l1; can_flow_reflexive c l2;
                 can_flow_from_join_left c l1 l2 l1; can_flow_from_join_right c l1 l2 l2
and can_flow_to_meet_left c l1 l2 l3 = ()
and can_flow_to_meet_right c l1 l2 l3 = ()
and can_flow_from_join_left c l1 l2 l3 = ()
and can_flow_from_join_right c l1 l2 l3 = ()

let can_flow_from_meet c l1 l2 l3 = ()

let can_flow_to_join c l1 l2 l3 = ()

let can_flow_from_join c l1 l2 = ()

let can_flow_to_smaller_list c l1 l2 = ()

let can_flow_to_singleton c l x = ()

/// Labels and usages of secrets and bytes
/// --------------------------------------

let rec get_label_and_usage_of_secret (t:bytes) : option (label & usage) =
  match t with
  | Nonce i l u -> Some (l,u)
  | Derive k c extract ->
    (match get_label_and_usage_of_secret k with
     | Some (l,KDF (l', extract_u) expand_u) ->
            if extract = true then Some (l',extract_u)
            else Some (l,expand_u)
     | _ -> None) 
  | DH k s ->  
    (match get_label_and_usage_of_secret k, get_label_and_usage_of_secret s with 
    | Some (l1, DHKey u1), Some (l2, DHKey u2) ->
	   if eq_usage u1 u2 then
	     let l = Join l1 l2 in 
	     Some (l, u1)
	   else None
    | _, _ -> None)
  | _ -> None

let rec get_label (t:bytes) : label =
  match t with
  | Literal s -> Public
  | Concat t1 t2 -> Meet (get_label t1) (get_label t2)
  | PK s -> Public
  | PKEnc p msg -> Public
  | AEnc k msg _ -> Public
  | Sig sk msg -> get_label msg
  | Mac k msg -> get_label msg
  | Hash msg -> get_label msg
  | Nonce _ _ _
  | Derive _ _ _ ->
    (match get_label_and_usage_of_secret t with
     | Some (l,u) -> l
     | _ -> Public)
  | DH k s ->
    (match get_label_and_usage_of_secret t with
     | Some (l,u) -> l
     | _ -> Public)
  | CEOgen m -> Public
  | DEOgen m sk -> Public
  | _ -> Public

let rec eq_bytes_secrets_have_eq_label_and_usage t1 t2 =
  match t1, t2 with
  | Nonce i l u, Nonce i' l' u' -> ()
  | Derive k c e, Derive k' c' e' ->
	   eq_bytes_secrets_have_eq_label_and_usage k k'
  | DH k s, DH k' s' ->
	   eq_bytes_secrets_have_eq_label_and_usage k k';
	   eq_bytes_secrets_have_eq_label_and_usage s s';
	   (match get_label_and_usage_of_secret k,
		  get_label_and_usage_of_secret s,
		  get_label_and_usage_of_secret k',
		  get_label_and_usage_of_secret s'
	    with
	    | Some (_,u1), Some (_,u2), Some (_,u3), Some (_,u4) ->
	      eq_usage_transitive_lemma u1 u2 u3;
	      eq_usage_transitive_lemma u1 u2 u4
	    | _ -> ())
  | _ -> ()

let eq_bytes_secrets_have_eq_usage t1 t2 = eq_bytes_secrets_have_eq_label_and_usage t1 t2

let eq_bytes_secrets_have_eq_label t1 t2 = eq_bytes_secrets_have_eq_label_and_usage t1 t2

let rec has_secret_usage_pred (pr:preds) (t:bytes) (u:usage) (p:usage_pred u) =
  match t with
  | Nonce i l u' -> eq_usage u u' /\ pr.model.is_generated i t l u p
  | Derive k c true -> (exists l u' p'. has_secret_usage_pred pr k (kdf_usage (l,u) u') (C.kdf_usage_pred l u u' p p'))
  | Derive k c false -> (exists l u' p'. has_secret_usage_pred pr k (kdf_usage (l,u') u) (C.kdf_usage_pred l u' u p' p))
  | DH s1 s2 -> has_secret_usage_pred  pr s1 (dh_key_usage u) (dh_usage_pred u p) /\ has_secret_usage_pred pr s2 (dh_key_usage u) (dh_usage_pred u p)
  | _ -> False

#push-options "--z3rlimit 50"
let rec has_secret_label_usage_pred_lemma (pr:preds) (t:bytes) :
  Lemma (forall u p. has_secret_usage_pred pr t u p ==>
		(match get_label_and_usage_of_secret t with
	         | Some (l', u') -> eq_usage u u'
		 | _ -> False)) =
  match t with
  | Nonce i l u' -> ()
  | Derive k c true -> has_secret_label_usage_pred_lemma pr k
  | Derive k c false -> has_secret_label_usage_pred_lemma pr k
  | DH s s' -> has_secret_label_usage_pred_lemma pr s; has_secret_label_usage_pred_lemma pr s';
		   (match get_label_and_usage_of_secret s,
			  get_label_and_usage_of_secret s' with
		    | Some (_,u1), Some (_,u2) ->
		      eq_usage_symmetric_lemma u1 u2;
		      ()
		    | _ ->())
  | _ -> ()
#pop-options

let rec has_secret_usage_pred_lemma_forall_ pr t t':
  Lemma (forall u p. (eq_bytes t t' /\ has_secret_usage_pred pr t u p) ==> (has_secret_usage_pred pr t' u p))  =
  match t, t' with
  | Nonce i l u1, Nonce i' l' u2 -> pr.model.is_generated_eq_lemma i l u1; pr.model.is_generated_eq_bytes_lemma i t t'; ()
  | Derive k _ true, Derive k' _ true -> 
	 has_secret_label_usage_pred_lemma pr k;
	 has_secret_label_usage_pred_lemma pr k';
	 eq_bytes_secrets_have_eq_label_and_usage t t';
	 eq_bytes_secrets_have_eq_label_and_usage k k';
	 (match get_label_and_usage_of_secret k, get_label_and_usage_of_secret k' with
	   | Some (l, KDF (l1, u1) u2), Some (l', KDF (l1', u1') u2') ->
		  has_secret_usage_pred_lemma_forall_ pr k k' ;  
		  ()
	   | _ -> ())
  | Derive k _ false, Derive k' _ false -> has_secret_label_usage_pred_lemma pr t; 
	   (match get_label_and_usage_of_secret k with
	   | Some (l, KDF (l', extract_u) expand_u) -> 
		  has_secret_usage_pred_lemma_forall_ pr k k'; 
		  ()
	   | _ -> assert (eq_opt_label_and_usage (get_label_and_usage_of_secret t) None))
  | DH s1 p1, DH s2 p2 -> has_secret_usage_pred_lemma_forall_ pr s1 s2;	has_secret_usage_pred_lemma_forall_ pr p1 p2; ()
  | _ -> ()

val has_secret_usage_pred_lemma_: pr:preds -> t:bytes -> t':bytes -> u:usage -> p:usage_pred u ->
    Lemma ((eq_bytes t t' /\ has_secret_usage_pred pr t u p) ==> (has_secret_usage_pred pr t' u p)) 
	  [SMTPat (eq_bytes t t'); SMTPat (has_secret_usage_pred pr t u p)]
let has_secret_usage_pred_lemma_ pr t t' u p = has_secret_usage_pred_lemma_forall_ pr t t'

let has_secret_usage_pred_lemma_forall pr = ()

val has_public_usage_pred_lemma_forall_: pr:preds -> t:bytes -> t':bytes -> u:usage -> p:usage_pred u ->
    Lemma ((eq_bytes t t' /\ has_public_key_usage_pred pr t u p) ==> (has_public_key_usage_pred pr t' u p)) 
	  [SMTPat (eq_bytes t t'); SMTPat (has_public_key_usage_pred pr t u p)]
let has_public_usage_pred_lemma_forall_ pr t t' u p = 
  match t, t' with 
  | PK s, PK s' -> has_secret_usage_pred_lemma_forall_ pr s s'
  | _ -> () 

let has_public_usage_pred_lemma_forall pr = ()

let has_secret_usage_pred_for_dh pr k pk = ()

let get_label_and_usage_of_secret_lemma i l u = ()

(**
   Returns the label of bytes that is a public key (PK private_key).

   More precisely, the private_key must have the usage PKE. In this case,
   the label of the private_key is returned.

   Here, the public key is required to have a special format, i.e., PK private_key.
*)

let get_label_and_usage_of_private_key (t:bytes) =
  match t with
  | PK private_key -> get_label_and_usage_of_secret private_key
  | _ -> None

let get_label_and_usage_of_private_key_lemma t = ()

let get_label_of_secret_lemma t = ()
let get_label_and_usage_of_secret_nonce_lemma i l u = ()
let get_usage_of_secret_lemma i l u = ()
let get_label_of_secret_bytes_lemma t = ()

let rec eq_label_can_flow_lemma l l' = 
  match l, l' with 
  | Public, Public -> ()
  | ReadableBy a, ReadableBy b -> ()
  | Join l1 l2, Join l1' l2' 
  | Meet l1 l2, Meet l1' l2' -> eq_label_can_flow_lemma l1 l1'; eq_label_can_flow_lemma l2 l2'; eq_label_can_flow_lemma l1 l2'; eq_label_can_flow_lemma l2 l1'
  | _, _ -> ()

let rec eq_label_can_flow_to_lemma c l l' l'' = 
  match l, l'' with
  | Public, _ 
  | ReadableBy _, Public 
  | ReadableBy _, ReadableBy _
  | ReadableBy _, Meet _ _ 
  | ReadableBy _, Join _ _ -> ()
  | Join l11 l12, Public 
  | Join l11 l12, ReadableBy _ -> 
  	 (match l' with 
	 | Join l1 l2 -> eq_label_can_flow_to_lemma c l11 l1 l''; eq_label_can_flow_to_lemma c l12 l2 l''; 
			eq_label_can_flow_to_lemma c l11 l2 l''; eq_label_can_flow_to_lemma c l12 l1 l''
	 | _ -> ())	 
  | Meet l11 l12, Public 
  | Meet l11 l12, ReadableBy _ ->  
    	 (match l' with 
	 | Meet l1 l2 -> eq_label_can_flow_to_lemma c l11 l1 l''; eq_label_can_flow_to_lemma c l12 l2 l''; 
			eq_label_can_flow_to_lemma c l11 l2 l''; eq_label_can_flow_to_lemma c l12 l1 l''
	 | _ -> ())	 
  | Join l11 l12, Meet l21 l22 
  | Join l11 l12, Join l21 l22 -> 
    	 (match l' with 
	 | Join l1 l2 -> eq_label_can_flow_to_lemma c l11 l1 l''; eq_label_can_flow_to_lemma c l12 l2 l''; eq_label_can_flow_to_lemma c l11 l2 l'';
			eq_label_can_flow_to_lemma c l12 l1 l''; eq_label_can_flow_to_lemma c l l' l21; eq_label_can_flow_to_lemma c l l' l22
	 | _ -> ())	
  | Meet l11 l12, Meet l21 l22 
  | Meet l11 l12, Join l21 l22 -> 
  	 (match l' with 
	 | Meet l1 l2 -> eq_label_can_flow_to_lemma c l11 l1 l''; eq_label_can_flow_to_lemma c l12 l2 l''; eq_label_can_flow_to_lemma c l11 l2 l'';
			eq_label_can_flow_to_lemma c l12 l1 l''; eq_label_can_flow_to_lemma c l l' l21; eq_label_can_flow_to_lemma c l l' l22
	 | _ -> ())	

let rec can_flow_to_eq_labels_lemma c l l' l'' = 
  match l, l' with
  | Public, _ 
  | ReadableBy _, Public
  | ReadableBy _, ReadableBy _ 
  | Join _ _, Public 
  | Join _ _, ReadableBy _ 
  | Meet _ _, Public 
  | Meet _ _, ReadableBy _ -> ()
  | ReadableBy _, Meet l1 l2 -> (match l'' with 
			       | Meet l1' l2' -> can_flow_to_eq_labels_lemma c l l1 l1'; can_flow_to_eq_labels_lemma c l l2 l2';
						can_flow_to_eq_labels_lemma c l l2 l1'; can_flow_to_eq_labels_lemma c l l1 l2'
			       | _ -> ())
  | ReadableBy _, Join l1 l2 -> (match l'' with 
			       | Join l1' l2' -> can_flow_to_eq_labels_lemma c l l1 l1'; can_flow_to_eq_labels_lemma c l l2 l2';
					      can_flow_to_eq_labels_lemma c l l2 l1'; can_flow_to_eq_labels_lemma c l l1 l2'
			       | _ -> ())
  | Meet l1 l2, Meet l1' l2' 
  | Join l1 l2, Meet l1' l2' -> (match l'' with 
			       | Meet l1'' l2'' -> can_flow_to_eq_labels_lemma c l l1' l1''; can_flow_to_eq_labels_lemma c l l2' l2'';
						can_flow_to_eq_labels_lemma c l l1' l2''; can_flow_to_eq_labels_lemma c l l2' l1'';
						can_flow_to_eq_labels_lemma c l1 l' l''; can_flow_to_eq_labels_lemma c l2 l' l''
			       | _ -> ())	
  | Meet l1 l2, Join l1' l2' 
  | Join l1 l2, Join l1' l2' -> (match l'' with 
			       | Join l1'' l2'' -> can_flow_to_eq_labels_lemma c l l1' l1''; can_flow_to_eq_labels_lemma c l l2' l2'';
						can_flow_to_eq_labels_lemma c l l1' l2''; can_flow_to_eq_labels_lemma c l l2' l1'';
						can_flow_to_eq_labels_lemma c l1 l' l''; can_flow_to_eq_labels_lemma c l2 l' l''
			       | _ -> ())
	 
let eq_usage_ae_lemma u = ()

let eq_usage_dh_ae_lemma u = ()

let eq_usage_pke_lemma u = ()

let readable_label_equals_can_read i = ()

let eq_label_means_equal_readers i = ()

let eq_label_means_equal_join_readers i j = ()

let generated_secret_usage_pred_lemma pr i l u p = ()

#push-options "--max_fuel 4 --max_ifuel 4 --z3rlimit 200"
let rec unique_secret_usage_pred_lemma_forall pr t t' =
  match t, t' with
  | Nonce i l u1, Nonce i' l' u2  -> pr.model.is_generated_lemma i t t'; pr.model.is_generated_eq_bytes_lemma i t t'; ()
  | Derive k _ true, Derive k' _ true -> unique_secret_usage_pred_lemma_forall pr k k'; ()
  | Derive k _ false, Derive k' _ false -> unique_secret_usage_pred_lemma_forall pr k k'; ()
  | DH sk1 sk1', DH sk2 sk2' -> unique_secret_usage_pred_lemma_forall pr sk1 sk2; unique_secret_usage_pred_lemma_forall pr sk1' sk2'; ()
  | _ -> ()
#pop-options

let unique_secret_usage_pred_lemma pr t t' u p u' p' =
  unique_secret_usage_pred_lemma_forall pr t t'

let unique_public_key_usage_pred_lemma_forall pr t t' = ()

let extracted_secret_usage_pred_lemma pr k c l u u' p p' = ()

let expanded_secret_usage_pred_lemma pr k c l u u' p p' = ()

#push-options "--max_fuel 2 --max_ifuel 2 --z3rlimit 100"
let rec has_secret_usage_pred_with_more_corruption (pr:preds) (pr':preds) t: 
  Lemma (requires (corrupt_entry_is_extended pr pr'))
	(ensures (forall u p. has_secret_usage_pred pr t u p ==> has_secret_usage_pred pr' t u p)) =
  match t with
  | Nonce i x y -> ()
  | Derive k _ _ -> has_secret_usage_pred_with_more_corruption pr pr' k
  | DH s k -> has_secret_usage_pred_with_more_corruption pr pr' s; has_secret_usage_pred_with_more_corruption pr pr' k
  | _ -> ()

let has_public_key_usage_pred_with_more_corruption (pr:preds) (pr':preds) t:
  Lemma (requires (corrupt_entry_is_extended pr pr'))
	(ensures (forall u p. has_public_key_usage_pred pr t u p ==> has_public_key_usage_pred pr' t u p)) =
  match t with
  | PK t' -> has_secret_usage_pred_with_more_corruption pr pr' t'
  | _ -> ()
#pop-options

/// Correct usage of ``label`` and ``usage``
/// ----------------------------------------

let rec are_kdf_labels_increasing_ is_corrupt l u : Tot Type0 (decreases u) =
  match u with
  | KDF (extract_label, extract_usage) expand_usage -> 
        can_flow is_corrupt extract_label l /\ // The new label must flow to the old label. This ensures that the labels cannot get 'smaller'.
                                              // As the label does not change in the case of an expand, we only consider the extract case.
        are_kdf_labels_increasing_ is_corrupt extract_label extract_usage /\ //in case of an extract, the label changes
        are_kdf_labels_increasing_ is_corrupt l expand_usage //in case of an expand, the label stays the same
  | DHKey u -> are_kdf_labels_increasing_ is_corrupt l u
  | _ -> True 

let are_kdf_labels_increasing pr l u = are_kdf_labels_increasing_ pr l u 
let are_kdf_labels_increasing_lemma1 pr l = ()
let are_kdf_labels_increasing_lemma2 pr l l' u' u'' = ()
let are_kdf_labels_increasing_lemma3 pr l u = ()
let are_kdf_labels_increasing_lemma4 pr l u = ()

val are_kdf_labels_increasing_eq_lemma
  (pr:T.corrupt_pred) (l1:label) (u1:usage) (l2:label) (u2:usage):
  Lemma (ensures (are_kdf_labels_increasing pr l1 u1 /\ eq_label l1 l2 /\ eq_usage u1 u2) ==>
		  are_kdf_labels_increasing pr l2 u2) (decreases u2)
	[SMTPat (are_kdf_labels_increasing pr l1 u1); SMTPat (eq_label l1 l2); SMTPat (eq_usage u1 u2)]

let rec are_kdf_labels_increasing_eq_lemma
  (pr:T.corrupt_pred) (l1:label) (u1:usage) (l2:label) (u2:usage) =
  match u1,u2 with
  | KDF (l11,u11) u12, KDF (l21,u21) u22 ->
    are_kdf_labels_increasing_eq_lemma pr l11 u11 l21 u21;
    are_kdf_labels_increasing_eq_lemma pr l1 u12 l2 u22
  | DHKey u1', DHKey u2' -> are_kdf_labels_increasing_eq_lemma pr l1 u1' l2 u2'
  | _ -> ()

val are_kdf_labels_increasing_join_lemma
  (pr:T.corrupt_pred) (l1:label) (u1:usage) (l2:label) (u2:usage):
  Lemma (ensures (are_kdf_labels_increasing pr l1 u1 /\ are_kdf_labels_increasing pr l2 u2 /\ eq_usage u1 u2) ==>
		  are_kdf_labels_increasing pr (Join l1 l2) u1 /\ are_kdf_labels_increasing pr (Join l1 l2) u2) (decreases u2)
let rec are_kdf_labels_increasing_join_lemma
  (pr:T.corrupt_pred) (l1:label) (u1:usage) (l2:label) (u2:usage) =
  match u1, u2 with
  | KDF (l11,u11) u12, KDF (l21,u21) u22 ->
    are_kdf_labels_increasing_join_lemma pr l11 u11 l21 u21;
    are_kdf_labels_increasing_join_lemma pr l1 u12 l2 u22; ()
  | DHKey u1', DHKey u2' -> are_kdf_labels_increasing_join_lemma pr l1 u1' l2 u2'
  | _ -> ()
 
val are_kdf_labels_increasing_with_more_corruption: pr:T.corrupt_pred -> l:label -> u:C.usage ->
  Lemma (ensures (forall pr'. (are_kdf_labels_increasing pr l u /\
		   extends_corrupt pr pr') ==> (are_kdf_labels_increasing pr' l u)))
	(decreases u)
        [SMTPat (are_kdf_labels_increasing pr l u)]

let rec are_kdf_labels_increasing_with_more_corruption pr l u =
  match u with
  | KDF (l11,u11) u12 ->
    are_kdf_labels_increasing_with_more_corruption pr l11 u11;
    are_kdf_labels_increasing_with_more_corruption pr l u12
  | DHKey u1 ->
    are_kdf_labels_increasing_with_more_corruption pr l u1
  | _ -> ()

val pub_usage_is_valid: pr:T.corrupt_pred -> u:usage ->
  Lemma (requires (is_pub_usage u))
        (ensures (are_kdf_labels_increasing pr public u))
        [SMTPat (are_kdf_labels_increasing pr public u)]

let rec pub_usage_is_valid pr u =
  match u with
  | KDF (l',u') u'' -> pub_usage_is_valid pr u'; pub_usage_is_valid pr u''
  | DHKey u -> pub_usage_is_valid pr u
  | _ -> ()

let pk_is_PK (t:bytes) : Lemma (PK t == C.pk t) [SMTPat (C.pk t)] = ()

/// Main predicate to check correct label usage on bytes
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

let rec is_valid_p (pr:preds) (idx:nat) (t:bytes) : Type0 =
  match t with
  | Nonce i l u -> i <= idx /\ (exists up. pr.model.is_generated i t l u up) /\
                  are_kdf_labels_increasing (pr.model.corrupt_at i) l u
  | Literal s -> True
  | Concat t1 t2 -> is_valid_p pr idx t1 /\ is_valid_p pr idx t2
  | PK s -> is_valid_p pr idx s
  | PKEnc p msg -> is_valid_p pr idx p /\ is_valid_p pr idx msg /\
		  (can_flow (pr.model.corrupt_at idx) (get_label msg) Public \/ // (1) message is public, or
		  (match get_label_and_usage_of_private_key p with
		   | Some (private_key_label,PKE) ->
                      can_flow (pr.model.corrupt_at idx) (get_label msg) private_key_label /\ // (2) message is private and flows to the label of the key and
                      (pr.global.pke_un_pred private_key_label msg \/                // (2a) message satisfies pke_un_pred, or
		       (exists up. has_public_key_usage_pred pr p pke_key_usage up /\
			      pke_pred up idx msg)) // (2b) message satisfies pke_pred
		   | _ -> False))
  | AEnc k msg None -> is_valid_p pr idx k /\ is_valid_p pr idx msg /\
		     ((can_flow (pr.model.corrupt_at idx) (get_label msg) public /\
		       can_flow (pr.model.corrupt_at idx) (get_label k) public)    // (1) message and key are public, or
		    \/ (match get_label_and_usage_of_secret k with
		       | Some (l,AE) -> can_flow (pr.model.corrupt_at idx) (get_label msg) l /\ // (2) message flows to label of key and
				 (exists up. has_secret_usage_pred pr k ae_key_usage up /\  //  message satisfies ae_pred
					ae_pred up idx msg None)
		       | _ -> False))
  | AEnc k msg (Some ad) -> is_valid_p pr idx k /\ is_valid_p pr idx msg /\
			   is_valid_p pr idx ad /\ can_flow (pr.model.corrupt_at idx) (get_label ad) public /\
		     ((can_flow (pr.model.corrupt_at idx) (get_label msg) public /\
		       can_flow (pr.model.corrupt_at idx) (get_label k) public)    // (1) message and key are public, or
		    \/ (match get_label_and_usage_of_secret k with
		       | Some (l,AE) -> can_flow (pr.model.corrupt_at idx) (get_label msg) l /\ // (2) message flows to label of key and
				       (exists up. has_secret_usage_pred pr k ae_key_usage up /\  // message and ad satisfy ae_pred
					      ae_pred up idx msg (Some ad))
		       | _ -> False))
  | Sig sk msg -> is_valid_p pr idx sk /\ is_valid_p pr idx msg /\
	         (can_flow (pr.model.corrupt_at idx) (get_label sk) Public  // (1) key is public, or
		\/ (match get_label_and_usage_of_secret sk with
	           | Some (l,SIG) -> (exists up. has_secret_usage_pred pr sk sig_key_usage up /\ // (2) message satisfies sign_pred
			                   sign_pred up idx msg)
                   | _ -> False))
  | Mac k msg -> is_valid_p pr idx k /\ is_valid_p pr idx msg /\
		(can_flow (pr.model.corrupt_at idx) (get_label k) Public // (1) key is public, or
               \/ (match get_label_and_usage_of_secret k with
                  | Some (l,MAC) -> (exists up. has_secret_usage_pred pr k mac_key_usage up /\ // (2) message satisfies mac_pred
					  mac_pred up idx msg)
                  | _ -> False))
  | Hash msg -> is_valid_p pr idx msg
  | Derive k ctx b -> is_valid_p pr idx k /\ is_valid_p pr idx ctx /\
		    (can_flow (pr.model.corrupt_at idx) (get_label k) Public // (1) key is public, or
                  \/  (match get_label_and_usage_of_secret k with
                      | Some (l, KDF (l',u) u') -> are_kdf_labels_increasing (pr.model.corrupt_at idx) l (KDF (l',u) u')
                      | _ -> False))
  | DH k s -> is_valid_p pr idx k /\ is_valid_p pr idx s /\
	      can_flow (pr.model.corrupt_at idx) (get_label (PK s)) Public /\
	      (can_flow (pr.model.corrupt_at idx) (get_label t) Public \/
	      (match get_label_and_usage_of_secret k, get_label_and_usage_of_secret s with 
	      | Some (l, DHKey u1), Some (l', DHKey u2) ->
		if eq_usage u1 u2 then 
		   let tl = Join l l' in are_kdf_labels_increasing (pr.model.corrupt_at idx) tl u1
		else False
	      | _, _ -> False))
  | CEOgen m -> is_valid_p pr idx m /\ can_flow (pr.model.corrupt_at idx) (get_label m) Public
  | DEOgen m sk -> is_valid_p pr idx m /\ is_valid_p pr idx sk /\
	      can_flow (pr.model.corrupt_at idx) (get_label m) Public /\ can_flow (pr.model.corrupt_at idx) (get_label sk) Public
  | BadDH t1 t2 -> is_valid_p pr idx t1 /\ is_valid_p pr idx t2
  | _ -> False		

#push-options "--z3rlimit 200"
let rec validity_extends_lemma pr i t = 
  match t with 
  | Nonce _ _ _ 
  | Literal _ -> ()
  | Concat t1 t2 -> validity_extends_lemma pr i t1; validity_extends_lemma pr i t2
  | PK s -> validity_extends_lemma pr i s
  | PKEnc p msg -> validity_extends_lemma pr i p; validity_extends_lemma pr i msg; pr.model.corrupt_at_lemma i; ()
  | AEnc k msg None -> validity_extends_lemma pr i k; validity_extends_lemma pr i msg; pr.model.corrupt_at_lemma i; ()
  | AEnc k msg (Some ad) -> validity_extends_lemma pr i k; validity_extends_lemma pr i msg; validity_extends_lemma pr i ad; pr.model.corrupt_at_lemma i; ()
  | Sig sk msg -> validity_extends_lemma pr i sk; validity_extends_lemma pr i msg; pr.model.corrupt_at_lemma i; ()
  | Mac k msg -> validity_extends_lemma pr i k; validity_extends_lemma pr i msg; pr.model.corrupt_at_lemma i; ()
  | Hash msg -> validity_extends_lemma pr i msg; pr.model.corrupt_at_lemma i; ()
  | CEOgen msg -> validity_extends_lemma pr i msg; pr.model.corrupt_at_lemma i; ()
  | DEOgen msg sk -> validity_extends_lemma pr i msg; validity_extends_lemma pr i sk; pr.model.corrupt_at_lemma i; ()
  | Derive k ctx b -> validity_extends_lemma pr i k; validity_extends_lemma pr i ctx; pr.model.corrupt_at_lemma i; 
		     (match get_label_and_usage_of_secret k with
                      | Some (l, KDF (l',u) u') -> are_kdf_labels_increasing_with_more_corruption (pr.model.corrupt_at i) l (KDF (l', u) u')
                      | _ -> ())
  | DH k s -> validity_extends_lemma pr i k; validity_extends_lemma pr i s; pr.model.corrupt_at_lemma i; 
	      (match get_label_and_usage_of_secret k, get_label_and_usage_of_secret s with 
	      | Some (l, DHKey u1), Some (l', DHKey u2) -> if eq_usage u1 u2 then 
							     let tl = Join l l' in are_kdf_labels_increasing_with_more_corruption (pr.model.corrupt_at i) tl u1
							  else ()
	      | _, _ -> ())
  | BadDH t1 t2 -> validity_extends_lemma pr i t1; validity_extends_lemma pr i t2
  | _ -> ()
#pop-options

val secret_label_usage_is_valid: pr:preds -> idx:nat ->t:bytes -> l:label -> u:usage ->
  Lemma(requires (is_valid_p pr idx t /\ get_label_and_usage_of_secret t == Some (l,u)))
       (ensures (are_kdf_labels_increasing (pr.model.corrupt_at idx) l u))
       [SMTPat (is_valid_p pr idx t); SMTPat (are_kdf_labels_increasing (pr.model.corrupt_at idx) l u)]

let rec secret_label_usage_is_valid pr idx t l u =
  match t with
  | Nonce i l u -> pr.model.corrupt_at_lemma i; are_kdf_labels_increasing_with_more_corruption (pr.model.corrupt_at i) l u
  | Derive k c b ->
    (match get_label_and_usage_of_secret k with
     | Some (l,KDF (l', f) u') ->
       assert (is_valid_p pr idx t);
       assert (is_valid_p pr idx k);
       if b = true then
         secret_label_usage_is_valid pr idx k l (KDF (l',f) u')
       else secret_label_usage_is_valid pr idx k l (KDF (l',f) u')
     | _ -> ())
  | DH k s -> 
    (match get_label_and_usage_of_secret k, get_label_and_usage_of_secret s with 
    | Some (l, DHKey u1), Some (l', DHKey u2) ->
      if eq_usage u1 u2 then 
	 (secret_label_usage_is_valid pr idx k l (DHKey u1);
	 secret_label_usage_is_valid pr idx s l' (DHKey u2); 
	 assert (are_kdf_labels_increasing (pr.model.corrupt_at idx) l (u1));
	 assert (are_kdf_labels_increasing (pr.model.corrupt_at idx) l' (u2));
	 are_kdf_labels_increasing_join_lemma (pr.model.corrupt_at idx) l u1 l' u2;
	 ())
      else ()
    | _, _ -> ())
  | _ -> ()
 
#push-options "--max_fuel 2 --max_ifuel 2 --z3rlimit 100"
let rec valid_and_eq_bytes_implies_equal pr i t1 t2 =
  match t1,t2 with
  | Literal s1, Literal s2 -> ()
  | Concat t1a t1b, Concat t2a t2b -> valid_and_eq_bytes_implies_equal pr i t1a t2a; valid_and_eq_bytes_implies_equal pr i t1b t2b
  | Nonce n1 l1 u1, Nonce n2 l2 u2  ->
          assert (n1 == n2);
          assert (exists p1. pr.model.is_generated n1 t1 l1 u1 p1);
          assert (exists p2. pr.model.is_generated n2 t2 l2 u2 p2);
          pr.model.is_generated_lemma n1 t1 t2
  | PK s1, PK s2 -> valid_and_eq_bytes_implies_equal pr i s1 s2
  | PKEnc pk1 m1, PKEnc pk2 m2 -> valid_and_eq_bytes_implies_equal pr i pk1 pk2; valid_and_eq_bytes_implies_equal pr i m1 m2
  | Derive k1 ctx1 b1, Derive k2 ctx2 b2 -> valid_and_eq_bytes_implies_equal pr i k1 k2; valid_and_eq_bytes_implies_equal pr i ctx1 ctx2
  | AEnc k1 m1 None, AEnc k2 m2 None -> valid_and_eq_bytes_implies_equal pr i k1 k2; valid_and_eq_bytes_implies_equal pr i m1 m2
  | AEnc k1 m1 (Some ad1), AEnc k2 m2 (Some ad2) -> valid_and_eq_bytes_implies_equal pr i k1 k2; valid_and_eq_bytes_implies_equal pr i m1 m2; valid_and_eq_bytes_implies_equal pr i ad1 ad2
  | Sig sk1 m1, Sig sk2 m2 -> valid_and_eq_bytes_implies_equal pr i sk1 sk2; valid_and_eq_bytes_implies_equal pr i m1 m2
  | Mac k1 m1, Mac k2 m2 -> valid_and_eq_bytes_implies_equal pr i k1 k2; valid_and_eq_bytes_implies_equal pr i m1 m2  
  | DH k1 pk1, DH k2 pk2 -> eq_bytes_secrets_have_eq_label_and_usage t1 t2; valid_and_eq_bytes_implies_equal pr i k1 k2; valid_and_eq_bytes_implies_equal pr i pk1 pk2
  | Hash m1, Hash m2 -> valid_and_eq_bytes_implies_equal pr i m1 m2
  | CEOgen m1, CEOgen m2 -> valid_and_eq_bytes_implies_equal pr i m1 m2
  | DEOgen m1 sk1, DEOgen m2 sk2 -> valid_and_eq_bytes_implies_equal pr i m1 m2; valid_and_eq_bytes_implies_equal pr i sk1 sk2
  | _, _ -> ()
#pop-options  

let rec eq_bytes_has_secret_usage_pred_lemma (pr:preds) (idx:nat) (t:bytes) (t':bytes) =
  match t, t' with
  | Nonce i l u', Nonce i' l' u'' -> pr.model.is_generated_lemma i t t' 
  | Derive k _ _, Derive k' _ _ -> eq_bytes_has_secret_usage_pred_lemma pr idx k k' 
  | DH k s, DH k' s' -> (eq_bytes_has_secret_usage_pred_lemma pr idx k k'; eq_bytes_has_secret_usage_pred_lemma pr idx s s')
  | _ -> ()


/// Properties of correctly labeled bytes
/// -------------------------------------
let injective_labels c idx t l1 l2 = ()
  
let labeled_nonce_forall p = ()

let labeled_nonce_public_forall p = ()

val labeled_concat_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (concat t1 t2)))
        [SMTPat (is_publishable_p c idx (concat t1 t2))]
let labeled_concat_public c idx (t1:bytes) (t2:bytes) = ()

let concatenation_of_publishable_bytes_is_publishable_forall c  = ()

let concatenation_of_publishable_bytes_is_publishable_forall_under_any_preds t1 t2 = ()

val labeled_literal_public: c:preds -> idx:nat -> s:literal ->
  Lemma (ensures (is_publishable_p c idx (literal_to_bytes s)))
        [SMTPat (is_publishable_p c idx (literal_to_bytes s))]

let labeled_literal_public c idx s =
  let l = get_label (literal_to_bytes s) in
  assert (l == public)

let literals_are_publishable_forall c = ()

val labeled_split_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes -> t3:bytes ->
  Lemma (requires (is_succ2 (split t1) t2 t3 /\ is_publishable_p c idx t1))
        (ensures (is_publishable_p c idx t2 /\ is_publishable_p c idx t3))
        [SMTPat (is_succ2 (split t1) t2 t3); SMTPat (is_publishable_p c idx t1)]

let labeled_split_public c idx (t1:bytes) (t2:bytes) (t3:bytes) = ()
let splittable_bytes_publishable_implies_components_publishable_forall c = ()

let concatenation_publishable_implies_components_publishable c i t1 t2 = ()

let concatenation_publishable_implies_components_publishable_forall c = ()

val labeled_pk_public: c:preds -> idx:nat -> t1:bytes -> l1:label ->
  Lemma (is_labeled_p c idx t1 l1 ==> is_publishable_p c idx (pk t1))
        [SMTPat (is_labeled_p c idx t1 l1); SMTPat (is_publishable_p c idx (pk t1))]

let labeled_pk_public c idx (t1:bytes) l1 =
  assert (get_label (pk t1) == public);
  assert (is_valid_p c idx t1 ==> is_valid_p c idx (pk t1));
  assert (is_valid_p c idx t1 ==> is_publishable_p c idx (pk t1))

let public_key_is_publishable_if_private_key_is_publishable_forall c = ()

val labeled_pke_enc_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (pke_enc t1 t2)))
        [SMTPat (is_publishable_p c idx (pke_enc t1 t2))]

let labeled_pke_enc_public c idx (t1:bytes) (t2:bytes) =
    match get_label_of_private_key  t1 with
     | None -> ()
     | Some l -> flows_to_public_can_flow (c.model.corrupt_at idx) (get_label t2) l


let pke_ciphertext_publishable_if_key_and_msg_are_publishable_forall c = ()

val labeled_pke_dec_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes -> t3:bytes ->
  Lemma (requires (is_succ (pke_dec t1 t2) t3 /\ is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx t3))
        [SMTPat (is_publishable_p c idx t1); SMTPat (is_publishable_p c idx t2); SMTPat (is_succ (pke_dec t1 t2) t3)]

let labeled_pke_dec_public c (idx:nat) (t1:bytes) (t2:bytes) (t3:bytes) =
  match t2 with
  | PKEnc (PK t1') t3' ->
          if eq_bytes t1 t1' then (
               assert (t3 == t3');
               assert (is_valid_p c idx t2 ==> is_valid_p c idx t1');
               assert (is_valid_p c idx t3);
               (match get_label_of_private_key (PK t1') with
                | None -> ()
                | Some l -> can_flow_transitive (c.model.corrupt_at idx) (get_label t3) l public))
          else ()
  | _ -> ()

let pke_plaintext_publishable_if_key_and_ciphertext_publishable_forall c = ()

val labeled_sym_enc_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (aead_enc t1 t2 None)))
        [SMTPat (is_publishable_p c idx (aead_enc t1 t2 None))]

let labeled_sym_enc_public c idx (t1:bytes) (t2:bytes) =
  flows_to_public_can_flow (c.model.corrupt_at idx) (get_label t2) (get_label t1)

let sym_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall c = ()

val labeled_sym_dec_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes -> t3:bytes ->
  Lemma (requires (is_succ (aead_dec t1 t2 None) t3 /\ is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx t3))
        [SMTPat (is_publishable_p c idx t1); SMTPat (is_publishable_p c idx t2); SMTPat (is_succ (aead_dec t1 t2 None) t3)]

let labeled_sym_dec_public c (idx:nat) (t1:bytes) (t2:bytes) (t3:bytes) =
  match t2 with
  | AEnc t1' t3' None ->
    can_flow_transitive (c.model.corrupt_at idx) (get_label t3) (get_label t1') public; assert (is_publishable_p c idx t3)
  | _ -> ()

let sym_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall c = ()

val labeled_aead_enc_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes -> t3:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2 /\ is_publishable_p c idx t3))
        (ensures (is_publishable_p c idx (aead_enc t1 t2 (Some t3))))
        [SMTPat (is_publishable_p c idx (aead_enc t1 t2 (Some t3)))]

let labeled_aead_enc_public c (idx:nat) (t1:bytes) (t2:bytes) (t3:bytes) =
  flows_to_public_can_flow (c.model.corrupt_at idx) (get_label t2) (get_label t1);
  flows_to_public_can_flow (c.model.corrupt_at idx) (get_label t3) (get_label t2)

let aead_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall c = ()

val labeled_aead_dec_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes -> t3:bytes -> t4:bytes ->
  Lemma (requires (is_succ (C.aead_dec t1 t2 (Some t3)) t4 /\ is_publishable_p c idx t1 /\ is_publishable_p c idx t2 /\ is_publishable_p c idx t3))
        (ensures (is_publishable_p c idx t4))
        [SMTPat (is_publishable_p c idx t1); SMTPat (is_publishable_p c idx t2); SMTPat (is_publishable_p c idx t3); SMTPat (is_succ (C.aead_dec t1 t2 (Some t3)) t4)]

let labeled_aead_dec_public c (idx:nat) (t1:bytes) (t2:bytes) (t3:bytes) (t4:bytes) =
  match t2 with
  | AEnc t1' t4' (Some t3') ->
          if eq_bytes t1 t1' && eq_bytes t3 t3' then (
	     can_flow_transitive (c.model.corrupt_at idx) (get_label t4) (get_label t1') public)
          else () 
  | _ -> ()

let aead_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall c = ()

val labeled_sign_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (sign t1 t2)))
        [SMTPat (is_publishable_p c idx (sign t1 t2))]

let labeled_sign_public c idx (t1:bytes) (t2:bytes) = ()

let sig_is_publishable_if_key_and_msg_are_publishable_forall c = ()

val labeled_ceogen_public: c:preds -> idx:nat -> t1:bytes ->
  Lemma (requires (is_publishable_p c idx t1))
        (ensures (is_publishable_p c idx (ceo_gen t1)))
        [SMTPat (is_publishable_p c idx (ceo_gen t1))]

let labeled_ceogen_public c idx (t1:bytes) = ()

let ceo_is_publishable_if_msg_is_publishable_forall c = ()

val labeled_deogen_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (deo_gen t1 t2)))
        [SMTPat (is_publishable_p c idx (deo_gen t1 t2))]

let labeled_deogen_public c idx (t1:bytes) (t2:bytes) = ()

let deo_is_publishable_if_key_and_msg_are_publishable_forall c = ()

val labeled_mac_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (mac t1 t2)))
        [SMTPat (is_publishable_p c idx (mac t1 t2))]

let labeled_mac_public c idx (t1:bytes) (t2:bytes) = ()

let mac_is_publishable_if_key_and_msg_are_publishable_forall c = ()

val labeled_kdf_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes -> b:bool ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (kdf t1 t2 b)))
        [SMTPat (is_publishable_p c idx (kdf t1 t2 b))]

let labeled_kdf_public c idx (t1:bytes) (t2:bytes) b =
  match get_label_and_usage_of_secret t1 with
  | Some (l,KDF (l', u) u') ->
    let res = kdf t1 t2 b in
    assert (is_valid_p c idx res);
    assert (is_valid_p c idx t1);
    assert (are_kdf_labels_increasing (c.model.corrupt_at idx) l (KDF (l',u) u'));
    can_flow_transitive (c.model.corrupt_at idx) l' l public
  | _ -> () 

let derived_value_publishable_if_secret_and_context_are_publishable_forall c = ()
   
val labeled_dh_public: c:preds -> idx:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (is_publishable_p c idx t1 /\ is_publishable_p c idx t2))
        (ensures (is_publishable_p c idx (dh t1 t2)))
        [SMTPat (is_publishable_p c idx (dh t1 t2))]

let labeled_dh_public c idx (t1:bytes) (t2:bytes) = ()

let dh_is_publishable_if_keys_are_publishable_forall c = ()

/// Helper functions for labeled bytes
/// ----------------------------------

let labeled_public_is_publishable #pr t = ()

let restrict #pr #i #l1 t l2 =
  let l0 = get_label t in
  assert (can_flow (pr.model.corrupt_at i) l0 l1);
  can_flow_transitive (pr.model.corrupt_at i) l0 l1 l2;
  t

val can_flow_later: p:preds -> i:nat -> j:nat -> l1:label -> l2:label ->
  Lemma ((i <= j /\ can_flow (p.model.corrupt_at i) l1 l2) ==>
	          can_flow (p.model.corrupt_at j) l1 l2)
	[SMTPat (can_flow (p.model.corrupt_at i) l1 l2);
	 SMTPat (can_flow (p.model.corrupt_at j) l1 l2)]
let can_flow_later p i j l1 l2 =
  p.model.corrupt_at_lemma i

let can_flow_later_forall p = ()


val are_kdf_labels_increasing_later: p:preds -> i:nat -> j:nat -> l:label -> u:C.usage ->
  Lemma ((i <= j /\ are_kdf_labels_increasing (p.model.corrupt_at i) l u) ==>
		  are_kdf_labels_increasing (p.model.corrupt_at j) l u)
	[SMTPat (are_kdf_labels_increasing (p.model.corrupt_at i) l u);
	 SMTPat (are_kdf_labels_increasing (p.model.corrupt_at j) l u)]
let are_kdf_labels_increasing_later p i j l u =
  p.model.corrupt_at_lemma i

let are_kdf_labels_increasing_later_forall p = ()

let is_secret_later p i j t l u up = ()
val is_labeled_later: p:preds -> i:nat -> j:nat -> t:C.bytes -> l:label ->
  Lemma ((i <= j /\ is_labeled_p p i t l) ==> is_labeled_p p j t l)
	[SMTPat (is_labeled_p p i t l); SMTPat (is_labeled_p p j t l)]
let is_labeled_later p i j t l = ()

let is_labeled_later_forall p = ()

let can_label_of_bytes_flow_later p i j t l = ()



let pke_pred_later_forall () = ()
let sign_pred_later_forall () = ()
let mac_pred_later_forall () = ()
let ae_pred_later_forall () = ()

/// Labeled bytes API for applications
/// ----------------------------------

let literal_to_bytes_labeled_lemma pr i s =
  let t = C.literal_to_bytes s in
  literals_are_publishable_forall pr;
  assert (is_labeled_p pr i t public);
  assert (can_flow (pr.model.corrupt_at i) public public)

let literal_to_bytes pr i s = C.literal_to_bytes s

let literal_to_bytes_lemma pr i s = ()

let bytes_to_literal #pr #l s =
  match C.bytes_to_literal s with
  | Error s -> err s
  | Success s -> s

let bytes_to_literal_lemma pr s = ()


let string_to_bytes pr i s =
  let t = C.string_to_bytes s in
  literals_are_publishable_forall pr;
  assert (is_labeled_p pr i t public);
  assert (can_flow (pr.model.corrupt_at i) public public);
  t

let string_to_bytes_lemma pr i s = ()

let string_to_bytes_lemma2 s = ()

let string_to_bytes_can_flow s = ()


let bytes_to_string #pr #l s =
  match C.bytes_to_string s with
  | Error e -> err e
  | Success s -> s
let bytes_to_string_lemma pr s = ()

let nat_to_bytes pr i s =
  let t = C.nat_to_bytes s in
  literals_are_publishable_forall pr;
  assert (is_labeled_p pr i t public);
  assert (can_flow (pr.model.corrupt_at i) public public);
  t

let nat_to_bytes_lemma pr i s = ()

let bytes_to_nat #pr #l s =
  match C.bytes_to_nat s with
  | Error e -> err e
  | Success s -> s
let bytes_to_nat_lemma pr s = ()

let concat_labeled_lemma #pr #i #l t1 t2 = ()

let concat #pr #l t1 t2 = C.concat t1 t2
let concat_lemma #pr #l t1 t2 = ()
let concat_valid_lemma pr i m a = ()

let split_labeled_lemma #pr #i #l t =
  match C.split t with
  | Success (x,y) ->
    assert (eq_bytes t (C.concat x y));
    let l1 = get_label x in
    let l2 = get_label y in
    let l3 = get_label t in
    assert (l3 = meet l1 l2);
    can_flow_transitive (pr.model.corrupt_at i) l1 (meet l1 l2) l;
    can_flow_transitive (pr.model.corrupt_at i) l2 (meet l1 l2) l;
    ()
  | Error e -> ()

let split #pr #i #l t =
  match C.split t with
  | Success (x,y) -> (x,y)
  | Error e -> err e

let split_lemma #pr #l t = ()

let split_valid_lemma (pr:preds) i (t:bytes) = ()

let pk_labeled_lemma #pr #i #l s = ()

let pk #pr #l #up s = C.pk s
let pk_lemma #pr #l #up s = ()

let get_label_of_private_dec_key k =
  match k with
  | PK k ->
    (match get_usage_of_secret k with
      | Some (PKE) -> get_label k
      | _ -> Public)
  | _ -> Public

let get_label_of_private_dec_key_lemma k = ()

let get_label_of_private_dec_key_eq_lemma pr i = ()

let vk #pr #ps #up s = C.vk s
let vk_lemma #pr #ps #up s = ()

let pk_un #pr #l s = C.pk s
let pk_un_lemma #pr #l s = ()
  
let dh_pk #pr #l #u #up s = 
    let p = C.pk s in
    p
let dh_pk_lemma #pr #l #u #up s = ()
 
let get_label_of_dh_public_key k u =
  match k with
  | PK k ->
    (match get_label_and_usage_of_secret k with
      | Some (l, DHKey u') -> if eq_usage u u' then l else Public
      | _ -> Public)
  | _ -> Public

#push-options "--z3rlimit 400"
let get_label_of_dh_public_key_lemma k = ()
#pop-options

let get_usage_of_dh_public_key_lemma p = ()

let pke_enc_labeled_lemma #pr #i #l #up pk msg = ()
let pke_enc #pr #i #ps #up p m = C.pke_enc p m

let pke_enc_lemma #pr #ps #up p m = ()

let pke_enc_un_labeled_lemma #pr #i #l p m =
  let c = C.pke_enc p m in
  match get_label_and_usage_of_private_key p with
  | Some (l',PKE)  -> flows_to_public_can_flow (pr.model.corrupt_at i) l l';
               can_flow_transitive (pr.model.corrupt_at i) (get_label m) l l';
               can_flow_transitive (pr.model.corrupt_at i) (get_label m) public l';
               ()
  | _ -> assert (get_label_of_private_dec_key p == Public);
	   can_flow_transitive (pr.model.corrupt_at i) (get_label m) l public;
	   ()

let pke_enc_un #pr #i #l p m = C.pke_enc p m

let pke_enc_un_lemma #pr #i #l p m = ()

let pke_dec_labeled_lemma #pr #i #l #up s c =
  match C.pke_dec s c with
  | Success x ->
    C.pke_enc_dec_lemma s c;
    assert (eq_bytes c (C.pke_enc (C.pk s) x));
    pr.global.pke_un_pred_lemma x x;
    (match c with 
    | PKEnc (PK s') _ -> 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label s') (get_label s);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public l;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public (get_label s);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label s) public;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label s') public;
      ())
  | Error e -> ()

let pke_dec #pr #i #l #up s c =
  match C.pke_dec s c with
  | Success x ->
    C.pke_enc_dec_lemma s c;
    assert (eq_bytes c (C.pke_enc (C.pk s) x));
    assert (is_valid_p pr i c);
    assert ((can_flow (pr.model.corrupt_at i) l public /\ is_publishable_p pr i s) \/ is_secret_p pr i s l C.pke_key_usage up);
    pr.global.pke_un_pred_lemma x x;
    (match c with 
    | PKEnc (PK s') _ -> 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label s') (get_label s);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public l;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public (get_label s);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label s) public;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label s') public;
      x)
  | Error e -> err e

let pke_dec_un_lemma #pr #i #l s c = ()

let pke_dec_un_labeled_lemma #pr #i #l s c =
  match C.pke_dec s c with
  | Success x ->
    C.pke_enc_dec_lemma s c;
    assert (eq_bytes c (C.pke_enc (C.pk s) x));
    pr.global.pke_un_pred_lemma x x;
    (match c with 
    | PKEnc (PK s') _ -> 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) Public (get_label s); 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label s') (get_label s);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public l;
      ())
  | Error e -> ()

let pke_dec_un #pr #i #l s c =
  match C.pke_dec s c with
  | Success x -> x
  | Error e -> err e

let sign_labeled_lemma #pr #i #l1 #up #l2 k m =
  unique_secret_usage_pred_lemma_forall pr k k;
  assert (is_sign_key_p pr i k l1 up ==> has_secret_usage_pred pr k sig_key_usage up);
  let sg = C.sign k m in
  assert ((is_sign_key_p pr i k l1 up /\
	   can_label_of_bytes_flow_to pr i m l2 /\
	   C.sign_pred up i m) ==> is_valid_p pr i sg)

let sign #pr #i #l1 #up #l2 k m = C.sign k m

let sign_lemma #pr #i #l1 #up #ps k m = ()

let verify_labeled_lemma #pr #ps #up #l2 p m t = ()
let verify #pr #ps #up #l2 p m t = C.verify p m t

let verify_lemma #pr #ps #up #l2 p m t = ()

let verify_un #pr #l1 #l2 p m t = C.verify p m t

let verify_un_lemma #pr #l1 #l2 p m t = ()

let aead_enc_labeled_lemma #pr #ps #up k m ad = ()

let aead_enc #pr #ps #up k m ad = C.aead_enc k m (to_opt_bytes ad)
let aead_enc_lemma #pr #ps #up  k m ad = ()

let aead_enc_un_labeled_lemma #pr #i #l k m ad =
  let c = C.aead_enc k m ad in
  can_flow_transitive (pr.model.corrupt_at i) (get_label m) l public;
  match get_label_and_usage_of_secret k with
  | Some (l,AE) -> ()
  | _ -> has_secret_label_usage_pred_lemma pr k; ()

let aead_enc_un #pr #i #l k m ad = C.aead_enc k m (to_opt_bytes ad)

let aead_enc_un_lemma #pr #l k m ad = ()

let aead_dec_labeled_lemma #pr #i #kl #up k c ad =
  match C.aead_dec k c ad with
  | Success x ->
    (match c with 
    | AEnc k' _ _ ->
      assert (eq_bytes k k');
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) Public (get_label k); 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k') (get_label k);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public kl;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k) Public;
      ())
  | Error e -> ()

let aead_dec #pr #i #kl #up k c ad =
  match C.aead_dec k c (to_opt_bytes ad) with
  | Success x ->
    (match c with 
    | AEnc k' _ _ ->
      assert (eq_bytes k k');
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) Public (get_label k); 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k') (get_label k);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public kl;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k) Public;
      x)
  | Error e -> err e
 
let aead_dec_un_labeled_lemma #pr #i #kl k c ad =
  match C.aead_dec k c ad with
  | Success x ->
    (match c with 
    | AEnc k' _ _ -> 
      assert (eq_bytes k k');
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) Public (get_label k); 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k') (get_label k);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public kl;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k) Public;
      ())
  | Error e -> ()

let aead_dec_un #pr #i #kl k c ad =
  match C.aead_dec k c (to_opt_bytes ad) with
  | Success x ->
    (match c with 
    | AEnc k' _ _ -> 
      assert (eq_bytes k k');
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) Public (get_label k); 
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k') (get_label k);
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) public kl;
      can_flow_transitive (pr.model.corrupt_at i) (get_label x) (get_label k) Public;
      x)
  | Error e -> err e

#push-options "--z3refresh --max_fuel 1 --max_ifuel 1 --z3rlimit 100"
let mac_labeled_lemma #pr #i #l #up #l' k m = 
  unique_secret_usage_pred_lemma_forall pr k k;
  assert (is_mac_key_p pr i k l up ==> has_secret_usage_pred pr k mac_key_usage up);
  let t = C.mac k m in
  assert ((is_mac_key_p pr i k l up /\
	   can_label_of_bytes_flow_to pr i m l' /\
	   C.mac_pred up i m) ==> is_valid_p pr i t)
#pop-options

let mac #pr #i #l1 #ps #up k m = C.mac k m

let mac_lemma #pr #i #l1 #up #l2 k m = ()

let verify_mac_labeled_lemma #pr #i #l1 #up #l2 k m t = ()

let verify_mac #pr #i #l1 #up #l2 k m t = C.verify_mac k m t

let verify_mac_lemma #pr #i #l1 #up #l2 k m t = ()

#push-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 100"
let dh_labeled_lemma #p #i #l #u #up #l' k pk = 
  let c = C.dh k pk in
  match get_label_and_usage_of_secret k, get_label_and_usage_of_private_key pk with 
  | Some (l, DHKey u), Some (l', DHKey u') -> 
	 assert (eq_usage u u');
	 assert (is_dh_private_key_p p i k l u up);
	 assert (is_dh_public_key_p p i pk l' u up);
	 assert (has_secret_usage_pred p k (dh_key_usage u) (dh_usage_pred u up));
	 assert (has_public_key_usage_pred p pk (dh_key_usage u) (dh_usage_pred u up)); 
	 are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l u l' u;
	 assert (exists s. pk == PK s); 
	 are_kdf_labels_increasing_lemma4 (p.model.corrupt_at i) l u;
	 are_kdf_labels_increasing_lemma4 (p.model.corrupt_at i) l' u';
	 are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l u l' u'; 
	 are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l' u' l u;
	 assert (is_valid_p p i c);
	 assert (is_labeled_p p i c (join l l'));
	 assert (get_usage_of_secret c == Some u);
	 assert (has_secret_usage_pred p c u up);
	 assert (are_kdf_labels_increasing (p.model.corrupt_at i) (join l l') u)
  | _ -> ()
#pop-options

let dh #p #i #l #u #up #l' k pk = C.dh k pk
  
let dh_lemma #p #i #l #u #up #l' k pk = ()

#push-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 100"
let dh_un_labeled_lemma #p #i #l #u #up k pk =  
    let c = C.dh k pk in 
    assert (is_valid_p p i k /\ is_valid_p p i pk);
    assert (can_label_of_bytes_flow_to p i pk public);
    assert (eq_opt_label_and_usage (get_label_and_usage_of_secret k) (Some (l, DHKey u)));
    (match pk with 
    | PK s -> (match get_label_and_usage_of_secret s with 
	     | Some (l', DHKey u') -> 
	       if eq_usage u u' then 
		  (secret_label_usage_is_valid p i s l' (DHKey u'); 
		  are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l u l' u'; 
		  are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l' u' l u; 
		  assert (are_kdf_labels_increasing (p.model.corrupt_at i) (Join l l') u);
		  assert (are_kdf_labels_increasing (p.model.corrupt_at i) (Join l' l) u');
		  assert (is_valid_p p i k /\ is_valid_p p i pk /\ is_valid_p p i s);
		  assert (can_flow (p.model.corrupt_at i) (get_label pk) Public);
		  assert (can_flow (p.model.corrupt_at i) (get_label (PK k)) Public);
		  (match get_label_and_usage_of_secret k, get_label_and_usage_of_secret s with 
		  | Some (l1, DHKey u1), Some (l2, DHKey u2) -> 
		    if eq_usage u1 u2 then 
		       (are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l1 u1 l2 u2; 
		       are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l2 u2 l1 u1) 
		    else assert (can_flow (p.model.corrupt_at i) (get_label c) public));
		  assert (is_valid_p p i c);
		  assert (is_labeled_p p i c (join l l'));
		  assert (can_label_of_bytes_flow_to p i c l); assert (can_label_of_bytes_flow_to p i c l');
		  assert (c == DH k s \/ c == DH s k);
		  assert (get_usage_of_secret c == Some u \/ get_usage_of_secret c == Some u');
		  ())
	       else assert(get_label_of_dh_public_key pk u == public)
	     | _ -> assert(get_label_of_dh_public_key pk u == public); assert (can_label_of_bytes_flow_to p i c public))
    | _ -> ())
#pop-options

let dh_un #p #i #l #u #up k pk = 
  let c = C.dh k pk in
  match c with 
  | DH k1 k2 -> 
    (match get_label_and_usage_of_secret k1, get_label_and_usage_of_secret k2 with 
    | Some (l, DHKey u1), Some (l', DHKey u2) ->
      if eq_usage u1 u2 then 
	 (are_kdf_labels_increasing_lemma4 (p.model.corrupt_at i) l u1;
	 are_kdf_labels_increasing_lemma4 (p.model.corrupt_at i) l' u2;
	 are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l u1 l' u2; 
	 are_kdf_labels_increasing_join_lemma (p.model.corrupt_at i) l' u2 l u1)
      else ()
    | _, _ -> ());
    c
  | _ -> (
    assert(BadDH? c);
    err "invalid DH bytes"
  )

let hash_labeled_lemma #pr #i #l m = ()

let hash #pr #i #l m = C.hash m

let kdf_extract_labeled_lemma #pr #i #l1 #l2 #u1 #u2 #up1 #up2 k ctx = ()

let kdf_extract #pr #i  #l1 #l2 #u1 #u2 #up1 #up2 k ctx =
  let r = C.kdf k ctx true in
  assert (r == Derive k ctx true);
  (match get_label_and_usage_of_secret k with
   | Some (l, KDF(l',u') u'') -> assert (get_label r == l'); r
   | _ -> r)

let kdf_expand_labeled_lemma #pr #i  #l1 #l2 #u1 #u2 #up1 #up2 k ctx = ()

let kdf_expand #pr #i #ps1 #ps2 #u #u' #up1 #up2 k ctx =
  let r = C.kdf k ctx false in
  assert (r == Derive k ctx false);
  (match get_label_and_usage_of_secret k with
   | Some (l, KDF(l',u') u'') ->
          assert (get_label r == l);
          r
   | _ -> r)

let kdf_extract_lemma #pr #i #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()
let kdf_expand_lemma #pr #i #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()

let kdf_extract_usage_lemma #pr #i #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()
let kdf_expand_usage_lemma #pr #i #ps1 #ps2 #u #u' #up1 #up2 k ctx = ()

/// Lemmas about labeling

val nonce_generated_at_implies_is_labeled_: 
    pr:preds{pr.model.is_generated == T.is_nonce_generated_at} -> 
    i:nat ->
    n:C.bytes -> 
    lbl:label -> 
    u:C.usage -> 
    up:C.usage_pred u -> 
    Lemma (requires (T.is_nonce_generated_at i n lbl u up /\ are_kdf_labels_increasing (pr.model.corrupt_at i) lbl u))
    (ensures (is_labeled_p pr i n lbl))
    [SMTPat (T.is_nonce_generated_at i n lbl u up); SMTPat (are_kdf_labels_increasing (pr.model.corrupt_at i) lbl u)]
let nonce_generated_at_implies_is_labeled_ pr i n lbl u up = 
  pr.model.is_generated_eq_lemma i lbl u;
  assert (pr.model.is_generated i (gnonce i lbl u) lbl u up);
  assert (pr.model.is_generated i n lbl u up);
  pr.model.is_generated_lemma i (gnonce i lbl u) n;
  ()

let nonce_generated_at_implies_is_labeled pr n lbl u up = ()

let can_flow_to_public_implies_corruption c ak = ()

let publishable_of_secret_implies_corruption #pr #i #knowers #u #up s = ()

let is_private_dec_key_p_later_lemma p i t l up = ()

let is_sign_key_p_later_lemma p i t l up = ()

let is_publishable_p_later_lemma p i t = ()

let later_is_transitive i j k = ()

let corrupt_at_lemma i = ()

let corrupt_at_later_lemma pr i = pr.model.corrupt_at_lemma i

let is_verify_key_p_later_lemma p i t l up = ()

let is_verify_key_p_later_lemma2 p i t l up = ()

let there_is_only_one_owner_of_verify_key pr i up1 up2 key owner1 owner2 = ()

let owner_of_verify_key_is_unique pr i up1 up2 key sec_intendees owner = ()

let there_is_only_one_owner_of_verify_key_forall pr i up key owner = ()
