open Acme
open Web_Messages


(** Convert a [Web_Messages.http_method] to a lowercase string, e.g., "post" *)
let http_method_to_string (m:http_method) =
  match m with
  | HTTP_METHOD_GET -> "get"
  | HTTP_METHOD_POST -> "post"
  | HTTP_METHOD_HEAD -> "head"


(** Convert a sequence of bytes representing an URI path ([Web_Messages.request_uri.uri_path]) to a
   URL path string. This is done by calling [bytes_to_string] on each bytes and joining the results
   together with a "/" before each element.  An emtpy sequence results in an empty string.
@raise FstarWrapperUtils.Fstar_error if [bytes_to_string] fails on one of the sequence elements *)
let rec http_path_to_string (path:DY_Crypto.bytes FStar_Seq_Base.seq) =
  if FStar_Seq_Base.length path = Prims.of_int 0 then (
    ""
  ) else (
    let hd = FStar_Seq_Base.hd path in
    let tl = FStar_Seq_Base.tl path in
    match DY_Crypto.bytes_to_string hd with
    | Success s -> "/" ^ s ^ (http_path_to_string tl)
    | Error e -> raise (FstarWrapperUtils.Fstar_error (__LOC__, "bytes_to_string failed: " ^ e))
  )


(** Convert a sequence of bytes tuples representing a query
   ([Web_Messages.request_uri.uri_querystring]) to a URL query string. This is done by splitting
   each tuple into parameter name and value and then calling [bytes_to_string] on each
   value. Afterwards, the tuple elements are concatenated with a "=" in between, the resulting
   strings are then concatenated with "&" in between and "?" at the beginning. An emtpy sequence
   leads to an empty string.
@raise FstarWrapperUtils.Fstar_error if [bytes_to_string] fails on one of the bytes *)
let http_query_to_url_string (query:(DY_Crypto.bytes * DY_Crypto.bytes) FStar_Seq_Base.seq) =
  let query_elem_to_str (param_bytes, value_bytes) =
    match DY_Crypto.bytes_to_string param_bytes, DY_Crypto.bytes_to_string value_bytes with
    | Helpers.Success param, Helpers.Success value -> param ^ "=" ^ value
    | _, _ -> raise (FstarWrapperUtils.Fstar_error (__LOC__, "bytes_to_string failed!"))
  in
  match FstarWrapperUtils.fstar_sequence_to_list query with
  | [] -> ""
  | query_list -> "?" ^ (query_list |> List.map query_elem_to_str |> String.concat "&")


(** Convert a [Web_Messages.request_uri] to the "details" (i.e., path, query, and fragment) of an
   HTTP URL.
@raise FstarWrapperUtils.Fstar_error if [bytes_to_string] fails on one of the relevant bytes *)
let http_url_details_to_http_url_string details =
  let fragment_to_url_string f =
    match f with
    | None -> ""
    | Some frag_bytes -> (
      match DY_Crypto.bytes_to_string frag_bytes with
      | Helpers.Success fragment -> "#" ^ fragment
      | Helpers.Error e -> raise (FstarWrapperUtils.Fstar_error (__LOC__, "bytes_to_string failed: " ^ e))
    )
  in
  http_path_to_string details.uri_path ^
    http_query_to_url_string details.uri_querystring ^
      fragment_to_url_string details.uri_fragment


let url_scheme_to_string (s:scheme) =
  match s with
  | HTTP -> "http"
  | HTTPS -> "https"


(** Convert a [Web_Messages.url] to an HTTP URL.
@raise FstarWrapperUtils.Fstar_error if [bytes_to_string] fails on one of the relevant bytes *)
let http_url_to_string (u:url) : string =
  let scheme = url_scheme_to_string u.url_scheme in
  let domain = domain_to_string u.url_domain in
  let details = http_url_details_to_http_url_string u.url_request_uri in
  scheme ^ "://" ^ domain ^ details


(** Build an HTTP URL from the given domain, request and scheme (defaults to "https"). The resulting
   URL has the usual structure: <scheme>://<domain>/<path>?<query>#<fragment>, empty parts are
   omitted.
@raise FstarWrapperUtils.Fstar_error if [bytes_to_string] fails on one of the bytes in the request *)
let create_http_url ?(scheme:string = "https") (domain:string) (req:http_request) =
  let http_details = http_url_details_to_http_url_string req.req_uri in
  let url = scheme ^ "://" ^ domain ^ http_details in
  url


(** Convert an HTTP status string (e.g., "201") to a [Web_Messages.http_status].
@raise FstarWrapperUtils.Fstar_error if the given string cannot be mapped. *)
let status_string_to_http_status (s:string) : http_status =
  match s with
  | "200" -> HTTP_STATUS_200_OK
  | "201" -> HTTP_STATUS_201_CREATED
  | "403" -> HTTP_STATUS_403_FORBIDDEN
  | _ -> raise (FstarWrapperUtils.Fstar_error (__LOC__, "Unknown HTTP status: " ^ s))


