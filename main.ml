open Acme_wrapper_lib
module Client = AcmeClientWrapper



(** Set the initial internal state for our ACME client (i.e., create a trace entry with the client's
   account information).

@return A trace initialized with a single set state entry (containing the
client's account) and the session index of that account in the client state *)
let initialize_trace (config:Config_reader.configuration) =
  Logs.info (fun m -> m "Initializing F* trace for client");
  let private_key = Py.Object.to_string config.key in
  let account_url = Urls.string_to_url config.key_id in
  let new_order_url = Urls.string_to_url config.new_order_url in
  let client_initial_state, acct_idx = Client.create_account_session
                               private_key
                               account_url
                               new_order_url in
  FStar_Seq_Base.MkSeq [client_initial_state], acct_idx


(** Initializes the logging system with the given log levels. *)
let initialize_logging ?(library_level = Logs.Warning) level =
  Fmt_tty.setup_std_outputs ~style_renderer:((`Ansi_tty)) (); (* Colored logs *)
  (* Custom log reporter (we don't want the executable name prefix) *)
  let r ppf =
    let my_rep src lvl ~over k msgf =
      let k _ = over (); k () in
      let src_s = if src = Logs.default then "" else "" (* "(" ^ Logs.Src.name src ^ ") " *) in
      msgf @@ fun ?header ?tags fmt ->
              let _ = tags in (* supress unused warining *)
              match lvl with
              | Logs.App -> Format.kfprintf k ppf ("%a @[" ^^ fmt ^^ "@]@.") Logs_fmt.pp_header (lvl, Some "APP")
              | _ -> Format.kfprintf k ppf ("%a %s@[" ^^ fmt ^^ "@]@.") Logs_fmt.pp_header (lvl, header) src_s
    in
    { Logs.report = my_rep } in
  Logs.set_reporter (r (Format.std_formatter));
  Logs.set_level (Some level);
  Logs.Src.set_level Acme_wrapper_lib.log_src (Some library_level)


(* Note that the name "main" has no special meaning to OCaml - everything that is a "value" (and not
   a function) is "executed" (in declaration order). *)
let main =
  initialize_logging ~library_level:Logs.Error Logs.Error;
  let config = Config_reader.parse_args_and_load_config () in

  let trace, account_sessid = initialize_trace config in
  let trace = Client.get_fresh_replay_nonce config trace in
  let order_sessionid, ordered_identifier_count, trace = Client.send_acme_order config account_sessid trace in

  (* Function to trigger verification (RFC 8555, Sec. 7.5.1) for all challenges with
     [0 <= challenge_index < remaining_challenges] in the specified authorization object *)
  let rec verify_challenges (authz_sessionid, remaining_challenges, trace) =
    let chall_idx = Prims.(remaining_challenges - of_int 1) in
    let trace = Client.trigger_challenge_verification config authz_sessionid chall_idx trace in
    if Prims.(remaining_challenges > of_int 1) then (
      verify_challenges (authz_sessionid, chall_idx, trace)
    ) else (
      trace
    ) in

  (* Function to retrieve authorization objects and trigger their finalization by the server for the
     last [remaining_identifiers] identifiers (from the acme order stored under [order_sessionid] in
     the client's state).  This implies challenge response provisioning as well as challenge
     verification. *)
  let rec request_all_authorizations_and_verify_challenges remaining_identifiers trace =
    if remaining_identifiers <= 0 then (
      trace
    ) else (
      trace
      |> Client.request_acme_authorization config order_sessionid (remaining_identifiers - 1)
      |> verify_challenges
      |> request_all_authorizations_and_verify_challenges (remaining_identifiers - 1)
    ) in

  (* Retrieve all authorizations for [order_sessionid] and trigger verification of the respective
     challenges. *)
  let trace = request_all_authorizations_and_verify_challenges ordered_identifier_count trace in
  let csr_response, trace = Client.send_csr config order_sessionid trace in
  let _ = Client.retrieve_certificate config csr_response trace in
  ()
