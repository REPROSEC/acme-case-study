open Acme
open Web_Messages
open Log


(**
  Creates an (optional) scheme from a string.

  Example:
    s = "http"
    return value: Some HTTP
 *)
let string_to_url_scheme (s:string) : scheme option =
  match s with
  | "http" -> Some HTTP
  | "https" -> Some HTTPS
  | _ -> None

(**
  Given a string that represents a path, this function returns an FStar sequence of bytes, where
  each bytes corresponds to one part of the path.
 *)
let path_string_to_uri_path (path:string) : DY_Crypto.bytes FStar_Seq_Base.seq =
  let path_elements = Str.split (Str.regexp_string "/") path in
  let bytes_list = List.map DY_Crypto.string_to_bytes path_elements in
  FStar_Seq_Base.MkSeq bytes_list


(**
  Given a string u that represents an URL, this function creates a Web.Messages URL.
 *)
let string_to_url (u:string) : Web_Messages.url =
  let uri = Uri.of_string u in
  let path = Uri.path uri in
  match Uri.scheme uri, Uri.host uri, Uri.port uri with
  | Some str_scheme, Some str_domain, opt_port -> (
    match string_to_url_scheme str_scheme with
    | None -> raise (Invalid_argument ("Passed string '" ^ u ^ "' not parseable as URL!"))
    | Some scheme -> (
      let domain =
        if Option.is_some opt_port then (
          str_domain ^ ":" ^ (Int.to_string (Option.get opt_port))
        ) else (
          str_domain
        ) in
      Logs.debug (fun m -> m "Parsing string '%s' resulted in scheme '%s', domain '%s', and path '%s'"
                             u str_scheme domain path);
      let (result:url) = {
          url_scheme = scheme;
          url_domain = Root domain;
          url_request_uri = {
              uri_path = path_string_to_uri_path path;
              uri_querystring = FStar_Seq_Base.MkSeq [];
              uri_fragment = FStar_Pervasives_Native.None
            }
        } in
      result
    )
  )
  | _, _, _ -> raise (Invalid_argument ("Passed string '" ^ u ^ "' not parseable as URL!"))
