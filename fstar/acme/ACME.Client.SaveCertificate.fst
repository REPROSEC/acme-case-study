/// ACME.Client.SaveCertificate (implementation)
/// ==============================================
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
friend Application.Predicates
open Labeled.Crypto
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open Application.Predicates.Helpers
open Application.Predicates.Lemmas
open ACME.Client.HelperLemmas


#set-options "--max_fuel 8 --max_ifuel 4 --z3rlimit 400"
let _acme_client_save_certificate  client certificate retrieve_cert_sessionid =
  let (|i, v, state|) = get_last_state client in
    //The session at [retrieve_cert_sessionid] contains the session index of the CSR session used
    //for getting the certificate. In the following, the client checks if the CSR contains the same
    //identifiers and public key as the certificate.
  if retrieve_cert_sessionid >= Seq.length state then
      error "fail to save certificate"
  else (
    match parse_acme_client_state (state.[retrieve_cert_sessionid]) with
    | Success (RetrieveCertificate csr_sessionid) -> (
      if (csr_sessionid >= Seq.length state) then
         error "fail to save certificate"
      else (
        match parse_acme_client_state (state.[csr_sessionid]) with
        | Success (CSR csr_cert_priv_key csr_identifiers csr_order_sessionid _) -> (
          if (eq_bytes certificate.acme_certificate_pub_key (DY.Crypto.pk csr_cert_priv_key)) then (
            //if(certificate.acme_certificate_identifiers = csr_identifiers) then(
            if(is_same_set certificate.acme_certificate_identifiers csr_identifiers) then(
              let cert_ss = ReceivedCertificate certificate retrieve_cert_sessionid i in
              let ss_cert = serialize_acme_client_state cert_ss in
              let st_cert = Seq.snoc state ss_cert in
              let v_cert = Seq.snoc v 0 in
              assert(valid_acme_client_st state i app_preds client cert_ss);
              add_valid_client_session_state_preserves_state_inv i client v state cert_ss; 
              set_state client v_cert st_cert;
              (Seq.length v)
            ) else error "fail to save certificate"
          ) else error "fail to save certificate"
          )
        | _ -> error "fail to save certificate"
      )
      )
    | _ -> error "fail to save certificate"
    )
