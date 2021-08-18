/// ACME.Client.SaveCertificate
/// ==============================
module ACME.Client.SaveCertificate

open Helpers
open DY.Monad
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Labeled.ApplicationAPI
open Application.Predicates
open Labeled.Crypto
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.Predicates



val _acme_client_save_certificate:
    client:principal ->
    certificate:acme_certificate ->
    retrieve_cert_sessionid:nat ->
  DYL nat
   (requires fun h0 -> certificate_is_publishable app_preds (trace_len h0) certificate)
   (ensures fun h0 r h1 ->
      (
       exists (set_state_idx:nat) state v session_idx.
         set_state_idx < trace_len h1 /\
         is_set_state_at set_state_idx client v state /\ (
         match parse_acme_client_state state.[session_idx] with
         | Success (ReceivedCertificate cert _ _) -> (
           cert.acme_certificate_pub_key == certificate.acme_certificate_pub_key /\
           cert.acme_certificate_identifiers = certificate.acme_certificate_identifiers
         )
         | _ -> False
   )))

