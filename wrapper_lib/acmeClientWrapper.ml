open Acme
open Web_Messages
open Log


(** The "internal name" of the ACME client - as we only run one client here, we can fix this name *)
let client : DY_Principals.principal = "client"


(** Deactivates the given replay nonce (for the client, i.e., the client won't use that nonce in
   future requests).

@return The updated trace *)
let _deactivate_replay_nonce replay_nonce trace =
  Logs.debug (fun m -> m "Deactivating the following nonce: %s" (DY_Crypto.sprint_bytes replay_nonce));
  let fstar_result = ACME_Client_HelperFunctions.client_deactivates_replay_nonce client replay_nonce trace in
  let trace = FstarWrapperUtils.split_fstar_result_unit fstar_result in
  trace


(** Create initial client state containing one account session.

@return "Set state" trace entry with a client state containing (only) an account and the session
   index of that account session in the client state. *)
let create_account_session private_key account_url order_url =
  let private_key_bytes = Trace.string_to_nonce private_key in
  let client_accout = ACME_Data.Account (private_key_bytes, account_url, order_url) in
  let account_session = ACME_Data_SerializationHelpers.serialize_acme_client_state client_accout in
  let state = FStar_Seq_Base.MkSeq [ account_session ] in
  (* We don't care about the value of the version vector here, it just needs to have the correct
     size *)
  let version_vec = FStar_Seq_Base.MkSeq [Prims.of_int 0] in
  DY_Entry.SetState (client, version_vec, state), Prims.of_int 0


(** Requests a fresh replay nonce from the configured server and stores it in the client's state.
   The request creation as well as the response processing are handled by the verified F* client
   implementation.

@return The updated trace *)
let get_fresh_replay_nonce (config:Config_reader.configuration) trace =
  Logs.info (fun m -> m "Getting a fresh replay nonce from %s" config.new_nonce_url);
  (* There is no _http function for this in the F* code, thus we call the function directly. *)
  let fstar_result = ACME_Client_RequestNonce._acme_client_request_replay_nonce_save_state
                       client (Urls.string_to_url config.new_nonce_url) trace in
  let server, request, trace = FstarWrapperUtils.split_fstar_result2 fstar_result in
  let nonce_bytes = HttpHelpers.send_fresh_nonce_request server request in
  let server_domain = Root server in
  let _, trace = ACME_Client_GetNonce._acme_client_get_nonce_save_state
                   client nonce_bytes server_domain trace in
  trace


(** Places an ACME order for the configured domains using the account specified by
   [client_account_idx]. The order creation as well as the response processing (i.e., storing the
   authorizations in the client state) are handled by the verified F* client implementation.

@return Index of the order session in the client's state, the number of ordered identifiers and the
   updated trace.  *)
let send_acme_order (config:Config_reader.configuration) client_account_idx trace =
  Logs.app (fun m -> m "Creating order request for the following domains: %s" (String.concat ", " config.cert_domains));
  let cert_domains = List.map (fun d -> Root d) config.cert_domains in
  let target_domains = FStar_Seq_Base.MkSeq cert_domains in
  let fstar_result = ACME_Client.acme_client_orders_certificate_http client target_domains client_account_idx trace in
  let server, request, used_replay_nonce, trace = FstarWrapperUtils.split_fstar_result_dt3 fstar_result in
  let trace = _deactivate_replay_nonce used_replay_nonce trace in
  let response = HttpHelpers.send_request config server request in
  let fstar_result = ACME_Client.acme_client_receive_order_response_http client response trace in
  let client_order_sessionid, ordered_identifier_count, trace = FstarWrapperUtils.split_fstar_result2 fstar_result in
  client_order_sessionid, Z.to_int ordered_identifier_count, trace


(** Requests authorization information for the [identifier_idx]th identifier in the order specified
   by [client_order_sessionid].  Will also ask the user to provision the challenge response for the
   respective identifier (or provision it automatically if it detects to be running a suitable
   testing environment).  The request creation as well as the response processing are handled by the
   verified F* client implementation.

@return Index of the authorization session in the client's state, the number of challenges offered
   by the server (already filtered by which of the challenge types the F* client supports), and the
   updated trace *)
let request_acme_authorization config client_order_sessionid identifier_idx trace =
  let fstar_result = ACME_Client.acme_client_send_authorization_request_i_http client client_order_sessionid (Prims.of_int identifier_idx) trace in
  let request, server, used_replay_nonce, trace = FstarWrapperUtils.split_fstar_result3 fstar_result in
  let trace = _deactivate_replay_nonce used_replay_nonce trace in
  let authz_http_response = HttpHelpers.send_request config server request in
  let fstar_result = ACME_Client.acme_client_receive_authorization_response_http
                       client authz_http_response trace in
  let authz_sessionid, num_of_challenges, trace = FstarWrapperUtils.split_fstar_result2 fstar_result in
  Logs.debug (fun m -> m "Output of ACME_Client.acme_client_receive_authorization_response_http: \
                          authz_sessionid: %s" (Prims.to_string authz_sessionid ));
  Logs.debug (fun m -> m "Output of ACME_Client.acme_client_receive_authorization_response_http: \
                          num_of_challenges: %s" (Prims.to_string num_of_challenges));
  AcmeClientWrapperHelpers.provision_challenge_responses client config authz_sessionid trace;
  authz_sessionid, num_of_challenges, trace




(** The client indicates to the server that it can validate the challenge. For this, the client
   sends a request to the challenge url. See Section 7.5.1 of RFC 8555.

@return The updated trace. *)
let trigger_challenge_verification config client_authz_sessionid challenge_idx trace =
  Logs.app (fun m -> m "Triggering challenge verification");
  let fstar_result = ACME_Client.acme_client_triggers_challenge_i_http
                       client client_authz_sessionid challenge_idx trace in
  let request, server, used_replay_nonce, trace = FstarWrapperUtils.split_fstar_result3 fstar_result in
  let trace = _deactivate_replay_nonce used_replay_nonce trace in
  (* The client does not process the response to a trigger challenge message, therefore, we have to
     ask for a fresh nonce "by hand". *)
  let trace = get_fresh_replay_nonce config trace in
  (* Our F* client does not process the response to trigger messages *)
  let _ = HttpHelpers.send_request config server request in
  trace


(**
  Poll at the order endpoint until the status of the order is 'Ready'.
*)
let rec poll_order_endpoint_until_ready config client_order_sessionid trace =
  let fstar_result = ACME_Client.acme_client_poll_order_create_http_request client client_order_sessionid trace in
  let polling_request, server, used_replay_nonce, trace = FstarWrapperUtils.split_fstar_result3 fstar_result in
  let trace = _deactivate_replay_nonce used_replay_nonce trace in
  let trace = get_fresh_replay_nonce config trace in

  let polling_resp = HttpHelpers.send_request config server polling_request in

  let fstar_result = ACME_Client.acme_client_polling_response_is_ready client polling_resp trace in
  let order_is_ready, trace = FstarWrapperUtils.split_fstar_result1 fstar_result in

  match order_is_ready with
  | true -> (
     Logs.debug (fun m -> m "Success: Polled order is Ready.");
     trace
  )
  | false -> (
    Unix.sleep 1;
    poll_order_endpoint_until_ready config client_order_sessionid trace
  )


(** The client creates and sends a CSR to the server. See Section 7.4 of RFC 8555.

@return The CSR response and the updated trace. *)
let send_csr config client_order_sessionid trace =
  Logs.app (fun m -> m "Sending CSR");
  let fstar_result = ACME_Client.acme_client_sends_CSR_http client client_order_sessionid trace in
  let csr_request, server, used_replay_nonce, trace = FstarWrapperUtils.split_fstar_result3 fstar_result in
  let trace = _deactivate_replay_nonce used_replay_nonce trace in
  let trace = get_fresh_replay_nonce config trace in
  let csr_http_response = HttpHelpers.send_request config server csr_request in

  let fstar_result = ACME_Client.acme_client_poll_at_order_endpoint client csr_http_response trace in
  let polling_needed, trace = FstarWrapperUtils.split_fstar_result1 fstar_result in

  if(polling_needed) then (
    (* Poll until ready *)
    let trace = poll_order_endpoint_until_ready config client_order_sessionid trace  in

    (* Send the CSR request. *)
    let fstar_result = ACME_Client.acme_client_sends_CSR_http client client_order_sessionid trace in
    let csr_request, server, used_replay_nonce, trace = FstarWrapperUtils.split_fstar_result3 fstar_result in
    let trace = _deactivate_replay_nonce used_replay_nonce trace in
    let trace = get_fresh_replay_nonce config trace in
    let csr_http_response = HttpHelpers.send_request config server csr_request in
    csr_http_response, trace
  ) else (
    Logs.debug (fun m -> m "Success: Client received response to CSR request.");
    csr_http_response, trace
  )



(**
  Send final request to retrieve the certificate from the ACME server.

  This function should be called with the http response from the finalize endpoint. If the status of
  the updated ACME order is [Processing], this function polls at the order endpoint first.
 *)
let rec retrieve_certificate config http_response trace =
  Logs.app (fun m -> m "Trying to retrieve certificate from ACME server");
  let trace = get_fresh_replay_nonce config trace in
  let fstar_result = ACME_Client.acme_client_retrieves_certificate_http client http_response trace in
  let request, server, used_replay_nonce, is_polling_at_order_endpoint, trace =
    FstarWrapperUtils.split_fstar_result4 fstar_result in
  let trace = _deactivate_replay_nonce used_replay_nonce trace in
  let response = HttpHelpers.send_request config server request in
  if is_polling_at_order_endpoint then (
    Logs.app (fun m -> m "Polling at the order endpoint until the certificate is ready...");
    Unix.sleep 1;
    retrieve_certificate config response trace
  ) else (
    let fstar_result = ACME_Client.acme_client_receives_and_saves_certificate client response trace in
    let cert_session_idx, trace = FstarWrapperUtils.split_fstar_result1 fstar_result in
    let cert_str = AcmeClientWrapperHelpers.get_certificate_str client cert_session_idx trace in
    Logs.info (fun m -> m "Client received response to final certificate request. Here's the \
                         certificate as it is stored by F*: %s" (DY_Crypto.sprint_bytes response.resp_body));
    Logs.app (fun m -> m "Here's your certificate (chain):\n%s" cert_str);
    trace
  )
