/// Web.Messages
/// =============
module Web.Messages

open DY.Crypto
open FStar.Seq
open FStar.Seq.Base
open HelperFunctions
module LC = Labeled.Crypto


type http_method =
  | HTTP_METHOD_GET: http_method
  | HTTP_METHOD_POST: http_method
  | HTTP_METHOD_HEAD: http_method


type domain =
  |Root: root:string -> domain
  |Sub: sub:string -> dom:domain -> domain

val domain_to_string: domain -> string

noeq type request_uri = {
  uri_path: seq bytes;
  uri_querystring: seq (bytes * bytes);
  uri_fragment: option bytes;
}


let eq_path p1 p2 = eq_seq_bytes p1 p2


(**
  Returns true iff the two queries a and b are equal. Here, we assume that the query components of both a and b
  have the same ordering.
*)
val eq_querystring: (a:seq (bytes * bytes)) -> (b:seq (bytes * bytes)) -> Tot bool (decreases (length a))


(**
   Lemma stating the main property of eq_querystring:
   eq_querystring a b is true iff:
   1) a and b have the same length and
   2) the individual query components are equal (according to eq_bytes)
*)
val eq_querystring_lemma: (a:seq (bytes * bytes)) -> (b:seq (bytes * bytes))  -> Lemma (
     eq_querystring a b <==>
     ((length a) = (length b))
      /\ (forall (i: nat {i < length a} ) . i < (length a)
         ==> ( eq_bytes (fst (Seq.index a i))  (fst (Seq.index b i)) /\ eq_bytes (snd (Seq.index a i))  (snd (Seq.index b i)))))

val eq_querystring_reflexive_lemma:
  a:seq (bytes * bytes) ->
  Lemma (ensures (eq_querystring a a))
  [SMTPat (eq_querystring a a)]



let eq_request_uri (a:request_uri) (b:request_uri) =
  ( eq_path a.uri_path b.uri_path ) &&
  ( eq_querystring a.uri_querystring b.uri_querystring ) &&
  ( match a.uri_fragment, b.uri_fragment with
    | Some afrag, Some bfrag -> eq_bytes afrag bfrag
    | None, None -> true
    | _, _ -> false )

val eq_request_uri_reflexive_lemma:
  a:request_uri ->
  Lemma (ensures (eq_request_uri a a))

val is_request_uri_publishable:
  #pr: LC.preds ->
  trace_idx:nat ->
  r: request_uri ->
  l: Type0 {l <==> is_seq_bytes_publishable #pr trace_idx r.uri_path /\ is_seq_bytes_pairs_publishable #pr trace_idx r.uri_querystring /\ (Some? r.uri_fragment ==> LC.is_publishable_p pr trace_idx (Some?.v r.uri_fragment))}


type scheme =
  | HTTP: scheme
  | HTTPS: scheme


noeq type url = {
  url_scheme: scheme;
  url_domain: domain;
  url_request_uri: request_uri;
}


let eq_url (a:url) (b:url): bool = (a.url_scheme = b.url_scheme) && (a.url_domain = b.url_domain) && (eq_request_uri a.url_request_uri b.url_request_uri)

val eq_url_reflexive_lemma:
  a:url ->
  Lemma (ensures (eq_url a a))

val eq_sequence_url:
  s_url1: Seq.seq url ->
  s_url2: Seq.seq url ->
  Tot bool (decreases (Seq.length s_url1))

type http_header = bytes * bytes


noeq type http_request = {
  req_id:bytes; // req_id is similar to the request nonce in the WIM
  req_method:http_method;
  req_uri:request_uri;
  req_headers:Seq.seq http_header;
  req_body: bytes;
}

let is_http_request_publishable
  (#pr:LC.preds)
  (trace_idx:nat)
  (r:http_request)
  =
  LC.is_publishable_p pr trace_idx r.req_id /\
  is_request_uri_publishable #pr trace_idx r.req_uri /\
  is_seq_bytes_pairs_publishable #pr trace_idx r.req_headers /\
  LC.is_publishable_p pr trace_idx r.req_body

type http_status =
  | HTTP_STATUS_200_OK: http_status
  | HTTP_STATUS_201_CREATED: http_status
  | HTTP_STATUS_403_FORBIDDEN: http_status

noeq type http_response = {
  resp_req_id: bytes; // resp_req_id is similar to the request nonce in the WIM
  resp_status: http_status;
  resp_headers:Seq.seq http_header;
  resp_body: bytes;
}




val get_header_from_headers:
  header_name: string ->
  headers: Seq.seq http_header ->
  current_index: nat ->
  Pure (option ((header_key:bytes) * (header_value:bytes)))
       (requires True)
       (ensures (fun result ->
                 (match result with
                  | None -> True
                  | Some el -> Seq.contains headers el
                 )))
       (decreases (Seq.length headers - current_index))

(**
  [get_header_from_headers] applied to a sequence containing one element
  returns a key-value pair corresponding to the element.
*)
val get_header_from_headers_singleton:
  (s:string) ->
  (t:bytes) ->
  Lemma
    (ensures(
      let headers = (Seq.create 1 (string_to_bytes s, t)) in
      match get_header_from_headers s headers 0 with
      | None -> False
      | Some (host_header_key, host_header_value) ->
        host_header_key == string_to_bytes s /\
        host_header_value == t
    ))


(**
two sequence of urls [s1], [s2] are same set if all element of [s1] is element of [s2] and vice versa
*)
val is_same_set_of_urls: s1:Seq.seq url -> s2:Seq.seq url -> bool
