/// Application.Predicates (implementation)
/// ============================================
module Application.Predicates
open DY.Principals
open DY.Crypto
open DY.Trace
open Labeled.Crypto
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Web.Messages
open SerializationHelpers
open ACME.Data
open ACME.Data.SerializationHelpers
friend ACME.Data.SerializationHelpers
open Application.Predicates.Helpers

let pke_un_pred l m = True
let pke_un_pred_lemma m m' = ()


let authenticated_send_pred idx sender receiver message =
  match parse_http_response message with
  | Success resp ->(
      match DY.Crypto.split resp.resp_body with
      |Success (token, account_pubkey) ->(
          //client_has_authorization_session trace_length sender token account_pubkey
          client_has_account_public_key sender account_pubkey idx
        )
      | _ -> False
    )
  | _ -> False

let event_pred idx sender event  = True
let event_pred_preserves_eq idx sender ev pl pl' = ()


(* 
  [state_inv] should not be changed. It's better to capture security properties using [valid_acme_server_st] and [valid_acme_client_st]
  Reason: the problem is localized, so adding/refining properties/state sessions goes way easier
*)
let state_inv trace_idx p v st =
  (Seq.length v = Seq.length st) /\
  (forall si. si < Seq.length v ==>
   ( v.[si] == 0 /\
   ( match parse_acme_server_state st.[si], parse_acme_client_state st.[si] with
     | Success sti, Error _ ->
       serialize_acme_server_state sti == st.[si] /\
       valid_acme_server_st app_preds trace_idx p sti
    | Error _, Success sti ->
       serialize_acme_client_state sti == st.[si] /\
       valid_acme_client_st st trace_idx app_preds p sti
    | _ -> False //one session cannot be both client or server session state
   )
  )
  )


let state_inv_later i j p vv st = ()


