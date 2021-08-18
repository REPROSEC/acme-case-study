/// SerializationHelpers
/// ====================
///
/// General helper functions to serialize/parse state and messages into/from bytes. **Note that this
/// module does not depend on any labeling - it is supposed to be used in DY layer modules like
/// application data definitions.**
/// 
/// There is another module, :doc:`SerializationLemmas-impl`, for connections between the functions
/// here and labeling-related properties.
module SerializationHelpers

(**! No labeling dependencies here! See above *)
open DY.Principals
open DY.Crypto
open Web.Messages
open HelperFunctions
open Helpers

open FStar.Seq
module LC = Labeled.Crypto

(*** Read the following before adding stuff *)
// Virtually all functions in this module should be named serialize_xxx or parse_xxx (in particular,
// do NOT call them xxx_to_bytes or bytes_to_xxx!).

// We need ifuel to assemble algebraic types
#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

// Some abbreviations (note that we open the Seq module which overwrites some names)
let dy_concat = DY.Crypto.concat
let dy_split = DY.Crypto.split
let dy_pke_enc = DY.Crypto.pke_enc
let dy_pke_dec = DY.Crypto.pke_dec

/// Scheme
let serialize_scheme (s:scheme) : Tot bytes =
  match s with
  | HTTP -> string_to_bytes "Scheme:HTTP"
  | HTTPS -> string_to_bytes "Scheme:HTTPS"

let parse_scheme (t:bytes) : Tot (result scheme) =
  match bytes_to_string t with
  | Success "Scheme:HTTP" -> Success HTTP
  | Success "Scheme:HTTPS" -> Success HTTPS
  | _ -> Error "Bytes is not a known scheme"

let parse_scheme_lemma (s:scheme)
  : Lemma (parse_scheme (serialize_scheme s) = Success s)
    [SMTPat (parse_scheme (serialize_scheme s))]
  = ()

let parse_scheme_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_scheme t)))
  (ensures (serialize_scheme (Success?.v (parse_scheme t)) == t))
  =
  ()


/// Sequence of bytes
let rec serialize_sequence_of_bytes (s:seq bytes) : Tot bytes (decreases (length s)) =
  match length s with
  | 0 -> string_to_bytes "EndOfSequenceOfBytes"
  | _ ->
    let hd = head s in
    let tl = tail s in
    dy_concat hd (serialize_sequence_of_bytes tl)

let rec parse_sequence_of_bytes (t:bytes) : Tot (result (seq bytes)) (decreases (bytes_depth t)) =
  match dy_split t with
  | Success (hd, tl) ->
    if Success? (parse_sequence_of_bytes tl) then
      Success (cons hd (Success?.v (parse_sequence_of_bytes tl)))
    else Error "Invalid format"
  | Error e_msg ->
    if eq_bytes (string_to_bytes "EndOfSequenceOfBytes") t then
      Success (empty)
    else
      Error "Invalid format"


#push-options "--max_fuel 1"
let rec parse_sequence_of_bytes_lemma (s:seq bytes)
  : Lemma (ensures (parse_sequence_of_bytes (serialize_sequence_of_bytes s) == Success s))
    (decreases (length s))
    [SMTPat (parse_sequence_of_bytes (serialize_sequence_of_bytes s))]
  =
  match length s with
  | 0 -> FStar.Seq.Base.lemma_empty s
  | _ ->
    let hd = head s in
    let tl = tail s in
    parse_sequence_of_bytes_lemma tl
#pop-options


#push-options "--max_ifuel 0 --max_fuel 1"
let rec parse_sequence_of_bytes_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_sequence_of_bytes t)))
  (ensures (serialize_sequence_of_bytes (Success?.v (parse_sequence_of_bytes t)) == t))
  (decreases (bytes_depth t))
  =
  match dy_split t with
  | Success (hd, tl) -> (
    parse_sequence_of_bytes_lemma2 tl;
    let seq_of_tl = Success?.v (parse_sequence_of_bytes tl) in
    let seq_of_t = Success?.v (parse_sequence_of_bytes t) in
    Seq.Properties.lemma_cons_inj hd hd seq_of_tl (tail seq_of_t)
  )
  | Error e_msg -> ()
#pop-options


/// Sequence of bytes tuples
let rec serialize_sequence_of_bytes_tuples (s:seq (bytes * bytes)) : Tot bytes (decreases (length s)) =
  match length s with
  | 0 -> string_to_bytes "EndOfSequenceofBytesTuples"
  | _ ->
    let hd = head s in
    let tl = tail s in
    let serialized_hd = dy_concat (fst hd) (snd hd) in
    dy_concat serialized_hd (serialize_sequence_of_bytes_tuples tl)

let rec parse_sequence_of_bytes_tuples (t:bytes) : Tot (result (seq (bytes * bytes))) (decreases (bytes_depth t)) =
  match dy_split t with
  | Success (hd, tl) -> (
      if Success? (parse_sequence_of_bytes_tuples tl) then (
        match dy_split hd with
        | Error e_msg -> Error e_msg
        | Success (fst, snd) -> Success (cons (fst, snd) (Success?.v (parse_sequence_of_bytes_tuples tl)))
      ) else Error "Invalid format"
    )
  | Error e_msg ->
    if eq_bytes (string_to_bytes "EndOfSequenceofBytesTuples") t then
      Success (empty)
    else
      Error e_msg

#push-options "--max_fuel 1"
let rec parse_sequence_of_bytes_tuples_lemma (s:seq (bytes * bytes))
  : Lemma (ensures (parse_sequence_of_bytes_tuples (serialize_sequence_of_bytes_tuples s) == Success s))
    (decreases (length s))
    [SMTPat (parse_sequence_of_bytes_tuples (serialize_sequence_of_bytes_tuples s))]
  =
  match length s with
  | 0 -> FStar.Seq.Base.lemma_empty s
  | _ ->
    let hd = head s in
    let tl = tail s in
    parse_sequence_of_bytes_tuples_lemma tl
#pop-options

#push-options "--max_ifuel 0 --max_fuel 1"
let rec parse_sequence_of_bytes_tuples_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_sequence_of_bytes_tuples t)))
  (ensures (serialize_sequence_of_bytes_tuples (Success?.v (parse_sequence_of_bytes_tuples t)) == t))
  (decreases (bytes_depth t))
  =
  match dy_split t with
  | Success (hd, tl) -> (
    parse_sequence_of_bytes_tuples_lemma2 tl;
    let seq_of_tl = Success?.v (parse_sequence_of_bytes_tuples tl) in
    let seq_of_t = Success?.v (parse_sequence_of_bytes_tuples t) in
    let hds = Success?.v (dy_split hd) in
    Seq.Properties.lemma_cons_inj hds hds seq_of_tl (tail seq_of_t)
  )
  | Error e_msg -> ()
#pop-options



/// Optional bytes
let serialize_option_bytes (ot:option bytes) : Tot bytes =
  match ot with
  | None -> string_to_bytes "OptBytes:None"
  | Some t -> dy_concat (string_to_bytes "OptBytes:Some") t

let parse_option_bytes (t:bytes) : Tot (result (option bytes)) =
  match dy_split t with
  | Success (t1, t2) -> (
    match bytes_to_string t1 with
    | Success "OptBytes:Some" -> Success (Some t2)
    | _ -> Error "Invalid format"
  )
  | _ -> (
    match bytes_to_string t with
    | Success "OptBytes:None" -> Success None
    | _ -> Error "Invalid format"
  )

let parse_option_bytes_lemma (ot:option bytes)
  : Lemma (parse_option_bytes (serialize_option_bytes ot) == Success ot)
    [SMTPat (parse_option_bytes (serialize_option_bytes ot))]
  = ()

let parse_option_bytes_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_option_bytes t)))
  (ensures (serialize_option_bytes (Success?.v (parse_option_bytes t)) == t))
  =
  match dy_split t with
  | Success (t1, t2) -> (
    match bytes_to_string t1 with
    | Success "OptBytes:Some" -> ()
    | _ -> ()
  )
  | _ -> ()


/// Request URI
let serialize_request_uri (req_uri:request_uri) : Tot bytes =
  let serialized_path = serialize_sequence_of_bytes req_uri.uri_path in
  let serialized_querystring = serialize_sequence_of_bytes_tuples req_uri.uri_querystring in
  let serialized_fragment = serialize_option_bytes req_uri.uri_fragment in
  dy_concat (dy_concat serialized_path serialized_querystring) serialized_fragment


let parse_request_uri (t:bytes) : Tot (result request_uri) =
  match dy_split t with
  | Error e_msg -> Error e_msg
  | Success (t1, ser_fragment) -> (
    match dy_split t1 with
    | Success (ser_path, ser_querystring) -> (
      match parse_sequence_of_bytes ser_path, parse_sequence_of_bytes_tuples ser_querystring, parse_option_bytes ser_fragment with
      | Success path, Success querystring, Success fragment -> (
        let uri:request_uri = {
          uri_path = path;
          uri_querystring = querystring;
          uri_fragment = fragment
        } in
        Success uri
      )
      | _ -> Error "Invalid format"
    )
    | Error e_msg -> Error e_msg
  )

let parse_request_uri_lemma (u:request_uri)
  : Lemma (parse_request_uri (serialize_request_uri u) == Success u)
    [SMTPat (parse_request_uri (serialize_request_uri u))]
  =
    ()

let parse_request_uri_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_request_uri t)))
  (ensures (serialize_request_uri (Success?.v (parse_request_uri t)) == t))
  =
  let Success (t1, ser_fragment) = dy_split t in
  let Success (ser_path, ser_querystring) = dy_split t1 in
  parse_option_bytes_lemma2 ser_fragment;
  parse_sequence_of_bytes_tuples_lemma2 ser_querystring;
  parse_sequence_of_bytes_lemma2 ser_path


/// HTTP Method
let serialize_http_method (m:http_method) : Tot bytes =
  match m with
  | HTTP_METHOD_GET -> string_to_bytes "HTTP_METHOD_GET"
  | HTTP_METHOD_POST -> string_to_bytes "HTTP_METHOD_POST"
  | HTTP_METHOD_HEAD -> string_to_bytes "HTTP_METHOD_HEAD"

let parse_http_method (t:bytes) : Tot (result http_method) =
  match bytes_to_string t with
  | Success "HTTP_METHOD_GET" -> Success HTTP_METHOD_GET
  | Success "HTTP_METHOD_POST" -> Success HTTP_METHOD_POST
  | Success "HTTP_METHOD_HEAD" -> Success HTTP_METHOD_HEAD
  | _ -> Error "Invalid format"

let parse_http_method_lemma (m:http_method)
  : Lemma (parse_http_method (serialize_http_method m) = Success m)
          [SMTPat (parse_http_method (serialize_http_method m))]
  = ()

let parse_http_method_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_http_method t)))
  (ensures (serialize_http_method (Success?.v (parse_http_method t)) == t))
  =
  ()


/// Domain
let rec serialize_domain (d:domain) : Tot bytes =
  match d with
  | Root str -> dy_concat (string_to_bytes "Domain:Root") (string_to_bytes str)
  | Sub sub dom -> dy_concat (string_to_bytes sub) (serialize_domain dom)

let rec parse_domain (t:bytes) : Tot (result domain) (decreases (bytes_depth t)) =
  match dy_split t with
  | Error e_msg -> Error e_msg
  | Success (t1, t2) -> (
    match bytes_to_string t1, bytes_to_string t2 with
    | Success "Domain:Root", Success root -> Success (Root root)
    | _ -> (
      match bytes_to_string t1, parse_domain t2 with
      | Success sub, Success dom -> Success (Sub sub dom)
      | _ -> Error "Invalid format"
    )
  )

#push-options "--max_fuel 1"
let rec parse_domain_lemma (d:domain)
  : Lemma (parse_domain (serialize_domain d) = Success d)
          [SMTPat (parse_domain (serialize_domain d))]
  =
    match d with
    | Root _ -> ()
    | Sub sub dom -> (
      parse_domain_lemma dom
    )

let rec parse_domain_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_domain t)))
  (ensures (serialize_domain (Success?.v (parse_domain t)) == t))
  (decreases (bytes_depth t))
  =
  let Success (t1, t2) = dy_split t in
  match bytes_to_string t1, bytes_to_string t2 with
  | Success "Domain:Root", Success root -> ()
  | _ -> (
      match bytes_to_string t1, parse_domain t2 with
      | Success sub, Success dom -> parse_domain_lemma2 t2
      | _ -> ()
    )
#pop-options


/// URL
let serialize_url (u:url) : Tot bytes =
  let scheme = u.url_scheme in
  let domain = u.url_domain in
  let req_uri = u.url_request_uri in
  let serialized_scheme = serialize_scheme scheme in
  let serialized_domain = serialize_domain domain in
  let serialized_req_uri = serialize_request_uri req_uri in
  dy_concat (dy_concat serialized_scheme serialized_domain) serialized_req_uri

let parse_url (t:bytes) : Tot (result url) =
  match dy_split t with
  | Error e_msg -> Error e_msg
  | Success (t1, ser_req_uri) -> (
    match dy_split t1 with
    | Error e_msg -> Error e_msg
    | Success (ser_scheme, ser_domain) -> (
      match parse_scheme ser_scheme, parse_domain ser_domain, parse_request_uri ser_req_uri with
      | Success scheme, Success domain, Success uri -> (
        let url:url = {
          url_scheme = scheme;
          url_domain = domain;
          url_request_uri = uri
        } in
        Success url
      )
      | _ -> Error "Invalid format"
    )
  )

let parse_url_lemma (url_object:url)
  : Lemma (
      match parse_url (serialize_url url_object) with
      | Error e_msg -> False
      | Success object -> eq_url object url_object /\ object == url_object
    )
    [SMTPat (parse_url (serialize_url url_object))]
  = ()


let parse_url_lemma2
  (t:bytes)
  : Lemma
  (requires (Success? (parse_url t)))
  (ensures (serialize_url (Success?.v (parse_url t)) == t))
  =
  let Success (t1, ser_req_uri) = dy_split t in
  let Success (ser_scheme, ser_domain) = dy_split t1 in
  parse_domain_lemma2 ser_domain;
  parse_scheme_lemma2 ser_scheme;
  parse_request_uri_lemma2 ser_req_uri


/// HTTP Request
let serialize_http_request  (r:http_request) : Tot bytes =
  let s_method = serialize_http_method r.req_method in
  let s_uri = serialize_request_uri r.req_uri in
  let s_headers = serialize_sequence_of_bytes_tuples r.req_headers in
  dy_concat (dy_concat (dy_concat (dy_concat r.req_id s_method) s_uri) s_headers) r.req_body

let parse_http_request (t:bytes) : Tot (result http_request) =
  match dy_split t with
  | Error e_msg -> Error e_msg
  | Success (t1, body) -> (
    match dy_split t1 with
    | Error e_msg -> Error e_msg
    | Success (t2, s_headers) -> (
      match dy_split t2 with
      | Error e_msg -> Error e_msg
      | Success (t3, s_uri) -> (
        match dy_split t3 with
        | Error e_msg -> Error e_msg
        | Success (id, s_method) -> (
          match parse_sequence_of_bytes_tuples s_headers,
                parse_request_uri s_uri,
                parse_http_method s_method with
          | Success headers, Success uri, Success method -> (
            let req:http_request = {
              req_id = id;
              req_method = method;
              req_uri = uri;
              req_headers = headers;
              req_body = body
            } in
            Success req
          )
          | _ -> Error "Invalid format"
        )
      )
    )
  )

let parse_http_request_lemma (req:http_request)
  : Lemma (parse_http_request (serialize_http_request req) == Success req)
          [SMTPat (parse_http_request (serialize_http_request req))]
  = ()



/// HTTP Status
let serialize_http_status (s:http_status) : Tot bytes =
  match s with
  | HTTP_STATUS_200_OK -> string_to_bytes "HTTP_STATUS_200_OK"
  | HTTP_STATUS_201_CREATED -> string_to_bytes "HTTP_STATUS_201_CREATED"
  | HTTP_STATUS_403_FORBIDDEN -> string_to_bytes "HTTP_STATUS_403_FORBIDDEN"

let parse_http_status (t:bytes) : Tot (result http_status) =
  match bytes_to_string t with
  | Success "HTTP_STATUS_200_OK" -> Success HTTP_STATUS_200_OK
  | Success "HTTP_STATUS_201_CREATED" -> Success HTTP_STATUS_201_CREATED
  | Success "HTTP_STATUS_403_FORBIDDEN" -> Success HTTP_STATUS_403_FORBIDDEN
  | _ -> Error "Invalid format"

let parse_http_status_lemma (s:http_status)
  : Lemma (parse_http_status (serialize_http_status s) == Success s)
          [SMTPat (parse_http_status (serialize_http_status s))]
  = ()



/// HTTP Response
let serialize_http_response (r:http_response) : Tot bytes =
  let s_status = serialize_http_status r.resp_status in
  let s_headers = serialize_sequence_of_bytes_tuples r.resp_headers in
  dy_concat (dy_concat (dy_concat r.resp_req_id s_status) s_headers) r.resp_body

let parse_http_response (t:bytes) : Tot (result http_response) =
  match dy_split t with
  | Error e_msg -> Error e_msg
  | Success (t1, body) -> (
    match dy_split t1 with
    | Error e_msg -> Error e_msg
    | Success (t2, s_headers) -> (
      match dy_split t2 with
      | Error e_msg -> Error e_msg
      | Success (id, s_status) -> (
        match parse_sequence_of_bytes_tuples s_headers,
              parse_http_status s_status with
        | Success headers, Success status -> (
          let resp:http_response = {
            resp_req_id = id;
            resp_status = status;
            resp_headers = headers;
            resp_body = body
          } in
          Success resp
        )
        | _ -> Error "Invalid format"
      )
    )
  )

let parse_http_response_lemma (res:http_response)
  : Lemma (parse_http_response (serialize_http_response res) == Success res)
          [SMTPat (parse_http_response (serialize_http_response res))]
  = ()


/// Optional URL
let serialize_opt_url (opt_url:option url) : Tot bytes =
  match opt_url with
  | None -> string_to_bytes "OptURL:None"
  | Some url -> serialize_url url

let parse_opt_url (t:bytes) : Tot (result (option url)) =
  match bytes_to_string t with
  | Success "OptURL:None" -> Success None
  | _ -> (
    match parse_url t with
    | Success u -> Success (Some u)
    | _ -> Error "Invalid format"
  )

let parse_opt_url_lemma (opt_url:option url)
  : Lemma (parse_opt_url (serialize_opt_url opt_url) == Success opt_url)
          [SMTPat (parse_opt_url (serialize_opt_url opt_url))]
  = ()



/// Sequence of URLs
let rec serialize_sequence_of_urls (s:seq url) : Tot bytes (decreases (length s))
  =
  match length s with
  | 0 -> string_to_bytes "EndOfSequenceOfURLs"
  | _ ->
    let hd = head s in
    let tl = tail s in
    dy_concat (serialize_url hd) (serialize_sequence_of_urls tl)

let rec parse_sequence_of_urls (t:bytes) : Tot (result (seq url)) (decreases (bytes_depth t)) =
  match dy_split t with
  | Success (hd, tl) ->
    if Success? (parse_sequence_of_urls tl) && Success? (parse_url hd) then
      Success (cons (Success?.v (parse_url hd)) (Success?.v (parse_sequence_of_urls tl)))
    else Error "Invalid format"
  | _ ->
    if eq_bytes (string_to_bytes "EndOfSequenceOfURLs") t then
      Success (empty)
    else
      Error "Invalid format"

#push-options "--max_fuel 1"
let rec parse_sequence_of_urls_lemma (s:seq url)
  : Lemma (ensures (parse_sequence_of_urls (serialize_sequence_of_urls s) == Success s))
    (decreases (length s))
    [SMTPat (parse_sequence_of_urls (serialize_sequence_of_urls s))]
  =
  match length s with
  | 0 -> FStar.Seq.Base.lemma_empty s
  | _ ->
    let hd = head s in
    let tl = tail s in
    parse_sequence_of_urls_lemma tl
#pop-options



/// Sequence of domains
let rec serialize_sequence_of_domains (s:seq domain): Tot bytes (decreases (length s)) =
  match length s with
  | 0 -> string_to_bytes "EndOfSequenceOfDomains"
  | _ ->
      let hd = head s in
      let tl = tail s in
      dy_concat (serialize_domain hd) (serialize_sequence_of_domains tl)

let rec parse_sequence_of_domains (t:bytes) : Tot (result (seq domain)) (decreases (bytes_depth t)) =
  match dy_split t with
  | Success (hd, tl) ->
    if Success? (parse_sequence_of_domains tl) && Success? (parse_domain hd) then
      Success (cons (Success?.v (parse_domain hd)) (Success?.v (parse_sequence_of_domains tl)))
    else Error "Invalid format"
  | _ ->
    if eq_bytes (string_to_bytes "EndOfSequenceOfDomains") t then
      Success (empty)
    else
      Error "Invalid format"

#push-options "--max_fuel 1"
let rec parse_sequence_of_domains_lemma (s:seq domain)
  : Lemma (ensures (parse_sequence_of_domains (serialize_sequence_of_domains s) == Success s))
    (decreases (length s))
    [SMTPat (parse_sequence_of_domains (serialize_sequence_of_domains s))]
  =
  match length s with
  | 0 -> FStar.Seq.Base.lemma_empty s
  | _ ->
    let hd = head s in
    let tl = tail s in
    parse_sequence_of_domains_lemma tl
#pop-options



/// Optional sequence of URLs
let serialize_opt_seq_of_urls (o_seq:option (seq url)) : Tot bytes =
  match o_seq with
  | None -> string_to_bytes "OptSeq:None"
  | Some url_seq -> serialize_sequence_of_urls url_seq

let parse_opt_seq_of_urls (t:bytes) : Tot (result (option (seq url))) =
  match bytes_to_string t with
  | Success "OptSeq:None" -> Success None
  | _ -> (
    match parse_sequence_of_urls t with
    | Error e_msg -> Error e_msg
    | Success s -> Success (Some s)
  )

#push-options "--max_fuel 1"
let parse_opt_seq_of_urls_lemma (o_seq:option (seq url))
  : Lemma (ensures (parse_opt_seq_of_urls (serialize_opt_seq_of_urls o_seq) == Success o_seq))
    (decreases (if Some? o_seq then length (Some?.v o_seq) else 0))
    [SMTPat (parse_opt_seq_of_urls (serialize_opt_seq_of_urls o_seq))]
  =
    ()
#pop-options
