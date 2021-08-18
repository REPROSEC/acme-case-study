/// AMCE.Test.Init (implementation)
/// =================================
module ACME.Test.Init

open Helpers
open FStar.Tactics
open DY.Monad
open DY.Entry
open DY.Labels
open DY.Principals
open DY.Crypto
open DY.Trace
open Labeled.Crypto
open Labeled.ApplicationAPI
open Web.Messages
open ACME.Data
open ACME.Data.SerializationHelpers
open Application.Predicates
friend Application.Predicates
open Application.Predicates.Helpers
open HelperFunctions
open SerializationLemmas
open Application.Predicates.Lemmas

#set-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 1 --initial_fuel 0 --initial_ifuel 1"


val create_account_for_client:
  trace_index:nat ->
  client:principal ->
  priv_key:secret_at trace_index (readable_by_any1 client) sig_key_usage (acme_sig_key_usage (reader_any1 client) app_preds) ->
  account_url:url{is_publishable_p app_preds trace_index (serialize_url account_url)} ->
  order_url:url{is_publishable_p app_preds trace_index (serialize_url order_url)} ->
  DYL (si:nat)
  (requires fun t0 -> trace_index = trace_len t0)
  (ensures fun t0 _ t1 -> trace_len t0 <= trace_len t1)

let create_account_for_client trace_index client priv_key account_url order_url =
  if has_state_set client then (
    let (|now, v, state|) = get_last_state client in
    let new_ss_st = Account priv_key account_url order_url in
    let new_ss = serialize_acme_client_state new_ss_st in
    let new_state = Seq.snoc state new_ss in
    let new_v = Seq.snoc v 0 in
    assert(Seq.length new_v = Seq.length new_state);
    assert(state_inv now client new_v new_state);
    state_inv_implies_principal_state_readable now client new_v new_state;
    set_state client new_v new_state;
    (Seq.length v)
  ) else (
    let new_ss_st = Account priv_key account_url order_url in
    let new_ss = serialize_acme_client_state new_ss_st in
    let new_state = Seq.create 1 new_ss in
    let new_v = Seq.create 1 0 in
    let length_now = current_trace_len () in
    assert(state_inv length_now client new_v new_state);
    state_inv_implies_principal_state_readable length_now client new_v new_state;
    set_state client new_v new_state;
    0
  )

val create_valid_account_for_server:
  trace_index:nat ->
  client:principal ->
  server:principal ->
  pub_key:verify_key_p app_preds trace_index (readable_by_any1 client) (acme_sig_key_usage (reader_any1 client) app_preds) ->
  account_url:url{is_publishable_p app_preds trace_index (serialize_url account_url)} ->
  DYL (si:nat)
  (requires fun t0 -> trace_index = trace_len t0)
  (ensures fun t0 _ t1 -> later (trace_len t0) (trace_len t1))


let create_valid_account_for_server trace_index client server pub_key account_url =
  if has_state_set server then (
    let (|i, v, state|) = get_last_state server in
    let acc:acme_account = {status = Valid} in
    let new_ss_st = UserAccount acc pub_key account_url  in
    let new_ss = serialize_acme_server_state new_ss_st in
    let new_state = Seq.snoc state new_ss in
    let new_v = Seq.snoc v 0 in
    let length_now = current_trace_len () in
    assert(state_inv length_now server new_v new_state); // Maybe it helps to split this up into helper functions for each branch
    state_inv_implies_principal_state_readable length_now server new_v new_state;
    set_state server new_v new_state;
    (Seq.length v)
  ) else (
    let acc:acme_account = {status = Valid} in
    let new_ss_st = UserAccount acc pub_key account_url  in
    let new_ss = serialize_acme_server_state new_ss_st in
    let new_state = Seq.create 1 new_ss in
    let new_v = Seq.create 1 0 in
    let length_now = current_trace_len () in
    assert(state_inv length_now server new_v new_state);
    state_inv_implies_principal_state_readable length_now server new_v new_state;
    set_state server new_v new_state;
    0
  )



let gen_account client server account_url order_url =
  let (|sec_gen_idx,priv_key|) = secret_gen (readable_by_any1 client) sig_key_usage (acme_sig_key_usage (reader_any1 client) app_preds) in
  let now = sec_gen_idx + 1 in
  let priv_key_t = secret_at now (readable_by_any1 client) sig_key_usage (acme_sig_key_usage (reader_any1 client) app_preds) in
  let priv_key:priv_key_t = priv_key in
  let pub_key = vk #now #(readable_by_any1 client) #(acme_sig_key_usage (reader_any1 client) app_preds) priv_key in
  assert(is_publishable_p app_preds now (serialize_url account_url));
  assert(is_publishable_p app_preds now (serialize_url order_url));
  let now' = current_trace_len () in
  assert(now = now');
  let si_client = create_account_for_client now client priv_key account_url order_url in
  let now'' = current_trace_len () in
  assert(now <= now'');
  is_publishable_p_later_lemma app_preds now (serialize_url account_url);
  is_publishable_p_later_lemma app_preds now (serialize_url order_url);
  assert(is_publishable_p app_preds now'' (serialize_url account_url));
  assert(is_publishable_p app_preds now'' (serialize_url order_url));
  let si_server = create_valid_account_for_server now'' client server pub_key account_url in
  (si_client, si_server)


#push-options "--max_ifuel 2 --max_fuel 2"
let gen_private_ca_key server =
  if has_state_set server then (
    let (|i, v, state|) = get_last_state server in
    let (|sec_gen_idx,priv_key|) = secret_gen (readable_by_any1 server) sig_key_usage (acme_sig_key_usage (reader_any1 server) app_preds) in
    let new_ss_st = PrivateCAKey priv_key in
    let new_ss = serialize_acme_server_state new_ss_st in
    let new_state = Seq.snoc state new_ss in
    let new_v = Seq.snoc v 0 in
    let length_now = current_trace_len () in
    assert(state_inv length_now server new_v new_state);
    state_inv_implies_principal_state_readable length_now server new_v new_state;
    set_state server new_v new_state;
    (Seq.length v)
  ) else (
     let (|sec_gen_idx,priv_key|) = secret_gen (readable_by_any1 server) sig_key_usage (acme_sig_key_usage (reader_any1 server) app_preds) in
     let new_ss_st = PrivateCAKey priv_key  in
     let new_ss = serialize_acme_server_state new_ss_st in
     let new_state = Seq.create 1 new_ss in
     let new_v = Seq.create 1 0 in
     let length_now = current_trace_len () in
     assert(state_inv length_now server new_v new_state);
     state_inv_implies_principal_state_readable length_now server new_v new_state;
     set_state server new_v new_state;
     0
  )
#pop-options

(**
    After applying [string_to_bytes] to a list of strings, the every element of the modified list is
    publishable.
*)
let rec elements_of_list_of_strings_publishable
  (trace_index:nat)
  (s:list string)
  :Lemma(
     let path_bytes = List.Tot.Base.map string_to_bytes s in
     forall el. List.Tot.memP el path_bytes ==> is_publishable_p app_preds trace_index el
  )
  =
   match s with
   | [] -> ()
   | hd::tl -> elements_of_list_of_strings_publishable trace_index tl

let gen_publishable_url trace_index dom path_strings =
 let path_bytes = List.Tot.Base.map string_to_bytes path_strings in
 elements_of_list_of_strings_publishable trace_index path_strings;
 assert(forall s. List.Tot.memP s path_bytes ==> is_publishable_p app_preds trace_index s);
 let _req_uri: request_uri = {
   uri_path = init_seq_with_list path_bytes;
   uri_querystring = Seq.empty;
   uri_fragment = None;
 } in
 let _url:url = {
   url_scheme = HTTPS;
   url_domain = dom;
   url_request_uri = _req_uri
 } in
 init_seq_with_list_equivalence_of_list_and_sequence #bytes path_bytes;
 assert(is_url_publishable app_preds trace_index _url);
 label_of_url_flows_to_public app_preds trace_index _url;
 _url

//#push-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2"
let gen_new_replay_nonce_url trace_idx serv_dom =
  let u = gen_publishable_url trace_idx serv_dom ["acme"; "new-nonce"] in
  assume(eq_path u.url_request_uri.uri_path (init_seq_with_list [string_to_bytes "acme"; string_to_bytes "new-nonce"]));
  u
