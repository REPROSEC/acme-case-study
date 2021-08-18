/// ACME.Client.ReceiveMessage (implementation)
/// =============================================
module ACME.Client.ReceiveMessage

open Helpers
open HelperFunctions
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.Labels
open Labeled.ApplicationAPI
open Labeled.Crypto
open Web.Messages
open ACME.Data
open ACME.Data.SerializationHelpers
open ACME.Data.SerializationLemmas
open Application.Predicates
//friend Application.Predicates
open FStar.Seq.Base

open SerializationHelpers
open SerializationLemmas
open FStar.String


let acme_client_receives_response_for_new_order tr_idx http_resp current_state =
  match find_reference_sessionid_of_pending_request_for_response http_resp current_state with
  |Success ref_sessid ->
    if ref_sessid < Seq.length current_state then (
      match parse_acme_client_state (current_state.[ref_sessid]) with
      |Success (ACMEOrder acme_order_object account_sess_idx _) -> (
        match parse_acme_order (http_resp.resp_body) with
        |Success updated_acme_order ->(
          if is_init_and_updated_order acme_order_object updated_acme_order then (
            http_response_is_publishable_implies_acme_order_in_http_response_is_publishable app_preds tr_idx http_resp;
            Success (
                   updated_acme_order,
                   ref_sessid
                 )
          )
          else Error "fail to receive response for new order"
        )
        |_ -> Error "fail to receive response for new order"
      )
      |_ -> Error "fail to receive response for new order"
    )
    else Error "fail to receive response for new order"
  |_ -> Error "fail to receive response for new order"



let acme_client_receives_response_for_asking_challenge tr_idx http_resp current_state =
  match find_reference_sessionid_of_pending_request_for_response   http_resp current_state with
  |Success ref_sessid ->
    if ref_sessid < Seq.length current_state then (
      match parse_acme_client_state (current_state.[ref_sessid]) with
      |Success (ACMEOrder acme_order_object account_sess_idx _) -> (
        match parse_acme_authorization (http_resp.resp_body) with
        |Success authorization ->(
          if Seq.mem authorization.acme_authorization_identifier  acme_order_object.acme_order_identifiers && //check whether the domain (identifier) is in the list of identifiers of the order
             Seq.length authorization.acme_authorization_challenges > 0 &&
             is_updated_order acme_order_object
          then (
            http_response_is_publishable_implies_acme_authorization_in_http_response_is_publishable app_preds tr_idx http_resp;

            Success ( authorization,
                      ref_sessid
                  )
          )
          else Error "fail to receive response for asking challenge"
        )
        |_ -> Error "fail to receive response for asking challenge"
      )
      |_ -> Error "fail to receive response for asking challenge"
    )
    else Error "fail to receive response for asking challenge"
  |_ -> Error "fail to receive response for asking challenge"


let check_path (path:Seq.seq bytes): result (token:bytes) =
 if Seq.length path = 3 then (
   match DY.Crypto.bytes_to_string (Seq.index path 0), DY.Crypto.bytes_to_string (Seq.index path 1) with
   |Success  ".well-known", Success "acme-challenge" -> Success (Seq.index path 2)
   |_ -> Error "path error"
 )else  Error "path error"


let acme_client_receives_challenge_request tr_idx client http_req current_state =
  if Seq.length http_req.req_headers = 1 then (
    let (name_bytes, value_bytes) = Seq.index http_req.req_headers 0 in
    match DY.Crypto.bytes_to_string name_bytes,
          parse_domain value_bytes,
          check_path http_req.req_uri.uri_path with
    | Success "Host",
      Success dom,
      Success token -> (
      //!Check whether the domain is in list authorization
      match find_ACMEAuthorization_session_state_by_domain_and_token current_state dom token with
      |Success (authz_idx, ACMEAuthorziation authorization order_sess_idx) -> (
        if Seq.length authorization.acme_authorization_challenges = 1 &&
           order_sess_idx < Seq.length current_state &&
           //! check whether the client is the owner of domain
           client = domain_principal_mapping dom
        then (
          match parse_acme_client_state (current_state.[order_sess_idx]) with
          |Success (ACMEOrder order account_sess_idx _) -> (
             http_request_is_publishable_implies_request_id_is_publishable app_preds tr_idx http_req;
             Success (account_sess_idx, authz_idx, http_req.req_id)
            )
          |_ -> Error "fail to receive challenge request"
        )else Error "fail to receive challenge request"
       )
      |_ -> Error "fail to receive challenge request"
     )
    | _ -> Error "fail to receive challenge request"
  )else Error "fail to receive challenge request"


let acme_client_receives_finalize_order tr_idx http_resp current_state =
  match find_reference_sessionid_of_pending_request_for_response  http_resp current_state with
  |Success ref_sessid -> (
      match find_ACMEOrder_and_Account_session_index_from_CSR_session_index current_state ref_sessid with
      |Success (order_idx, account_idx) -> (
        match parse_acme_order (http_resp.resp_body), parse_acme_client_state (current_state.[order_idx]) with
        |Success finalize_order, Success (ACMEOrder updated_order _ _) ->(
          if is_updated_and_finalize_order updated_order finalize_order then (
            (* The status of the order is [Valid]. The certificate can be retrieved at the certificate
            url. *)
            let certificate_url = Some?.v finalize_order.acme_order_certificate in
            http_response_is_publishable_implies_acme_order_in_http_response_is_publishable app_preds tr_idx http_resp;
            acme_order_is_publishable_implies_certificate_url_is_publishable tr_idx finalize_order;
            Success (ref_sessid, account_idx, Some certificate_url, None)
          )
          else if is_updated_and_finalize_processing_order updated_order finalize_order then (
            (* The status of the order is [Processing]. Send requests to the url contained in the
            Location header of the response, until the status is [Valid]. *)
            http_response_is_publishable_implies_acme_order_in_http_response_is_publishable app_preds tr_idx http_resp;
            match find_location_header_in_http_response http_resp with
            | Error e -> Error e
            | Success location_value -> (
              match parse_url location_value with
              | Success location_header_url -> (
                http_response_is_publishable_implies_location_in_headers_is_publishable tr_idx location_value http_resp;
                assert(is_publishable_p app_preds tr_idx location_value);
                serialize_parse_url_publishablity_lemma app_preds tr_idx location_value;
                assert(is_publishable_p app_preds tr_idx (serialize_url location_header_url));
                Success (ref_sessid, account_idx, None, Some location_header_url)
              )
              | _ -> Error "Error parsing location url (acme_client_receives_finalize_order)"
            )
          )
          else Error "fail to receive finalize order"
        )
        |_ -> Error "fail to receive finalize order"
      )
      |_ -> Error "fail to receive finalize order"
   )
  |_ -> Error "fail to receive finalize order"


let acme_client_receives_certificate tr_idx http_resp current_state =
  let  {resp_req_id; resp_status; resp_headers; resp_body} = http_resp in
  match find_reference_sessionid_of_pending_request_for_response  http_resp current_state with
  |Success ref_sessid -> (
    if ref_sessid < Seq.length current_state then(
      match parse_acme_client_state (current_state.[ref_sessid]), parse_acme_certificate resp_body with
      |Success (RetrieveCertificate csr_idx), Success certificate -> (
        http_response_is_publishable_implies_certificate_of_http_response_is_publishable app_preds tr_idx http_resp;
        Success(certificate, ref_sessid)
      )
      |_ -> Error "fail to receive certificate"
    )else Error "fail to receive certificate"
  )
  |_ -> Error "fail to receive certificate"


let extract_replay_nonce_from_response tr_idx http_resp =
  match find_replay_nonce_in_http_response http_resp with
  | Success replay_nonce  -> (
        http_response_is_publishable_implies_replay_nonce_in_headers_is_publishable tr_idx replay_nonce http_resp;
        Success(replay_nonce)
     )
  | Error e -> Error ("fail to extract replay nonce: " ^ e)


let acme_client_returns_replay_nonce_and_server_domain_for_response tr_idx http_resp current_state =
  match 
    find_server_domain_of_pending_request_for_response http_resp current_state,
    extract_replay_nonce_from_response tr_idx http_resp 
  with
  | Success (serv_dom), 
    Success replay_nonce  -> ( 
        assert(is_publishable_p app_preds tr_idx replay_nonce);
        Success(replay_nonce, serv_dom)
   )
  | Error e, Success _
  | Success _, Error e -> Error ("fail to receive replay nonce: " ^ e)
  | Error e1, Error e2 -> Error ("fail to receive replay nonce: " ^ e1 ^ " & " ^ e2)
