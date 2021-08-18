open Pyops
open Log

(** Container data type for parsed configuration options. *)
type configuration = {
    new_account_url: string;
    new_nonce_url: string;
    new_order_url: string;
    key_file_location: string;
    key: Pytypes.pyobject;
    key_id: string;
    cert_domains: string list;
  }


(** Find and return [converter yaml.key] (assuming that [yaml] is a value representing a yaml
   dict). Returns None if [key] is not found or [yaml] isn't a dict and throws an exception if
   something goes wrong. *)
let yml_find converter (key:string) (yaml:Yaml.value) =
  match yaml with
  | `O str_val_pairs -> (
     (* Note: `O is just the name of the constructor we match here (Yaml module) *)
    let value_from_yml = List.assoc_opt key str_val_pairs in
    match value_from_yml with
    | Some v -> converter v
    | _ -> None
  )
  | _ -> None


(** Read the location to the config file from the command line arguments.  *)
let get_config_file_path_from_arguments () =
  let config_file_path = ref None in
  let set_config_file filename = config_file_path := Some filename in
  let speclist = [
    ("-c", Arg.String (set_config_file), "config-file");
  ] in
  let usage_msg = "\nACME client with verified core functions \n\nUsage:" in
  Arg.parse speclist print_endline usage_msg;
  if Option.is_none !config_file_path then (
    Logs.err (fun m -> m "No config file provided. Use -c to provide a config file.");
    exit 1
  ) else (
    Logs.debug (fun m -> m "Using config file '%s'" (Option.get !config_file_path));
    Option.get !config_file_path
  )


(** Get resource directory from ACME server, parse it and extract URLs for new nonce, new order,
   and new account endpoints (in that order) *)
let load_data_from_resource_directory directory_url =
  Pythonhelpers.ensure_pyml_is_loaded ();
  Logs.debug (fun m -> m "Getting ACME server directory from '%s'" directory_url);
  let response, _ = Pythonhelpers.do_http_request ~http_method:"get" directory_url in
  let response_dict = response.&("json") [| |] in
  Logs.debug (fun m -> m "Response to directory request: %s" (Py.Object.to_string response_dict));
  let new_nonce_url = Py.Object.to_string response_dict.%$["newNonce"] in
  let new_order_url = Py.Object.to_string response_dict.%$["newOrder"] in
  let new_account_url = Py.Object.to_string response_dict.%$["newAccount"] in
  (new_nonce_url, new_order_url, new_account_url)


(** Parse CLI arguments, read config file and get ACME server directory information. *)
let parse_args_and_load_config () =
    Pythonhelpers.ensure_pyml_is_loaded ();
    let config_file_location = get_config_file_path_from_arguments () in
    let config_file_content = Yaml_unix.of_file_exn Fpath.(v config_file_location) in
    let yml2str (v:Yaml.value) = match v with | `String s -> Some s | _ -> None in
    let yml2strlist (v:Yaml.value) =
      match v with
      | `String s -> Some [s]
      | `A l -> Some (List.flatten (List.map (fun i -> Option.to_list (yml2str i)) l))
      |  _ -> None in
    match yml_find yml2str "acme_server_directory_url" config_file_content,
          yml_find yml2str "account_key_location" config_file_content,
          yml_find yml2str "kid" config_file_content,
          yml_find yml2strlist "cert_domains" config_file_content with
    | Some dir_url, Some key_location, Some kid, Some cert_domains -> (
      Logs.debug (fun m -> m "ACME server directory URL from config: '%s'" dir_url);
      Logs.debug (fun m -> m "Key file location from config: '%s'" key_location);
      Logs.debug (fun m -> m "Key ID from config: '%s'" kid);
      Logs.debug (fun m -> m "URLs for certificate from config: %s" (String.concat ", " cert_domains));

      (* Read key from key file *)
      let key_file_content = Pythonhelpers.parse_json_file_to_dict key_location in
      let authlib = Py.import "authlib.jose" in
      let jsonWebKey = authlib.&("JsonWebKey") [| |] in
      let key = jsonWebKey.&("import_key") [| key_file_content |] in
      let nonce_url, order_url, new_account_url = load_data_from_resource_directory dir_url in
      {
        new_account_url = new_account_url;
        new_nonce_url = nonce_url;
        new_order_url = order_url;
        key_file_location = key_location;
        key_id = kid;
        key = key;
        cert_domains = cert_domains;
      }
    )
    | _,_,_,_ ->
       Logs.err (fun m -> m "Could not find all required values in the config file '%s'" config_file_location);
       exit 1
