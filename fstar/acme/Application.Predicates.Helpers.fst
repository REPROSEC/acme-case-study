/// Application.Predicates.Helpers (implementation)
/// ================================================
module Application.Predicates.Helpers
open DY.Principals
open DY.Labels
open DY.Crypto
open DY.Trace
open Labeled.Crypto
open Web.Messages
open SerializationHelpers
open ACME.Data
open ACME.Data.SerializationHelpers

open ACME.Data.Predicates

let spred_lemma_ i p pr m m' : Lemma (requires (acme_sign_pred p pr i m /\ eq_bytes m m')) (ensures (acme_sign_pred p pr i m')) [SMTPat (acme_sign_pred p pr i m); SMTPat (eq_bytes m m')] = ()

let sign_pred_payload_lemma i p pr m m' = ()

let valid_acme_client_st_later_lemma state tr_idx pr p st = ()

let is_valid_Certificate_session_later_lemma pr trace_index set_cert_state_idx cert cert_url account_pub_key = ()

let owner_of_domain_owns_public_key_or_corrupted_later_lemma pr trace_index dom acc_pub_key = ()

let authorization_is_Valid_implies_ownership_of_domain_and_ownership_of_account_public_key_or_corruption_before_later_lemma pr trace_index seq_authz_info acc_pub_key = ()

let is_valid_Order_session_later_lemma pr trace_index order seq_authz_info acc_pub_key = ()

let valid_acme_server_st_later_lemma pr tr_idx p st = ()
