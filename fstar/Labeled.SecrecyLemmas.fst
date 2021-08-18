/// Labeled.SecrecyLemmas (implementation)
/// =======================================
module Labeled.SecrecyLemmas

friend Labeled.Crypto //needed for definition of is_valid
friend Labeled.ApplicationAPI // needed for definition of valid_trace

#set-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2"

val attacker_only_derives_public_values_:
  h:trace -> i:nat -> steps:nat -> Lemma
    (requires (valid_trace h /\ trace_len h >= i))
    (ensures (forall t. attacker_can_derive i steps t ==> is_publishable_p app_preds i t))

let rec attacker_only_derives_public_values_ h i steps =
  if steps = 0 then (
        literals_are_publishable_forall app_preds;
        corrupt_principals_have_publishable_state_at h i
  )
  else (
        attacker_only_derives_public_values_ h i (steps - 1);
        assert (forall (a':bytes). attacker_can_derive i (steps - 1) a' ==>
                             is_publishable_at i a');
        concatenation_of_publishable_bytes_is_publishable_forall app_preds;
        splittable_bytes_publishable_implies_components_publishable_forall app_preds;
        public_key_is_publishable_if_private_key_is_publishable_forall app_preds;
        pke_ciphertext_publishable_if_key_and_msg_are_publishable_forall app_preds;
        pke_plaintext_publishable_if_key_and_ciphertext_publishable_forall app_preds;
        sym_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall app_preds;
        sym_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall app_preds;
	aead_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall app_preds;
        aead_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall app_preds;
	sig_is_publishable_if_key_and_msg_are_publishable_forall app_preds;
        derived_value_publishable_if_secret_and_context_are_publishable_forall app_preds;
	mac_is_publishable_if_key_and_msg_are_publishable_forall app_preds;
	dh_is_publishable_if_keys_are_publishable_forall app_preds;
	ceo_is_publishable_if_msg_is_publishable_forall app_preds;
	deo_is_publishable_if_key_and_msg_are_publishable_forall app_preds;
        ())

val attacker_only_derives_public_values:
  h:trace -> i:nat -> steps:nat -> t:bytes -> Lemma
    (requires (valid_trace h /\ trace_len h >= i /\ attacker_can_derive i steps t))
    (ensures (is_publishable_p app_preds i t))
    [SMTPat (valid_trace h); SMTPat (attacker_can_derive i steps t)]

let attacker_only_derives_public_values h i steps t =
  attacker_only_derives_public_values_ h i steps

val attacker_only_knows_publishable_values:
  t:bytes ->
  DY unit
     (requires (fun tr -> valid_trace tr))
     (ensures (fun tr0 _ tr1 -> tr0 == tr1 /\
       (attacker_knows_at (trace_len tr0) t ==> is_publishable_p app_preds (trace_len tr0) t)))
let attacker_only_knows_publishable_values t = ()

let attacker_preserves_validity tr0 tr1 =
  labeled_nonce_forall app_preds;
  assert(forall i l u n up. is_nonce_generated_at i n l u up ==>
			 (n == gnonce i l u));
  assert(forall i a. (valid_trace tr0 /\ i <= trace_len tr0 /\ DY.AttackerAPI.attacker_knows_at i a) ==> is_publishable_at i a);
  ()

let secrecy_lemma t ps =
    let tr0 = get() in
    assert (valid_trace tr0);
    attacker_only_knows_publishable_values t;
    assert (corrupt_at == app_preds.model.corrupt_at);
    ()

let conditional_secrecy_lemma t ps =
    let t0 = get() in
    assert (valid_trace t0);
    attacker_only_knows_publishable_values t;
    assert (corrupt_at == app_preds.model.corrupt_at);
    ()

let secrecy_label_lemma t l = attacker_only_knows_publishable_values t

let secrecy_join_label_lemma t = attacker_only_knows_publishable_values t
