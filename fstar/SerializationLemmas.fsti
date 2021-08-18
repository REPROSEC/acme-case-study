/// SerializationLemmas (implementation)
/// ======================================
///
/// Lemmas to connect serialization with the labeling world. Please do **not** implement
/// serialization/parse functions here, there is another module, :doc:`SerializationHelpers-impl`,
/// for that.
module SerializationLemmas

open Labeled.Crypto
open Web.Messages
open DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels

open SerializationHelpers
open FStar.Seq
open Helpers

(*! No serialization/parsing functions in here! Put them in SerializationHelpers instead! *)


(** True iff the url contains only values with labels that can flow to public. *)
let is_url_publishable (pr:preds) (trace_index:nat) (u:url)  =
  let request_uri = u.url_request_uri in
  let path = request_uri.uri_path in
  let querystring = request_uri.uri_querystring in
  let fragment = request_uri.uri_fragment in
  (forall (path_component:bytes). (Seq.contains path path_component) ==>
    can_label_of_bytes_flow_to pr trace_index path_component public) /\
  (can_label_of_bytes_flow_to pr trace_index (serialize_sequence_of_bytes_tuples querystring) public) /\
  ( match fragment with
    | Some f -> can_label_of_bytes_flow_to pr trace_index f public
    | None -> True
  )

val url_contains_no_secrets_later_lemma:
  (pr:preds) ->
  (trace_index:nat) ->
  (u:url) ->
  Lemma
  (requires is_url_publishable pr trace_index u)
  (ensures forall i. later trace_index i ==> is_url_publishable pr i u)
  [SMTPat (is_url_publishable pr trace_index u)]

(**
  Given a sequence that only contains elements with labels that can flow to public, the label of the
  serialized sequence also flows to public.
*)
val serialized_sequence_of_bytes_flows_to_public_if_elements_flow_to_public:
(pr:preds) ->
(trace_index:nat) ->
(seq:Seq.seq bytes) ->
  Lemma
  (requires
    (forall (el:bytes). Seq.contains seq el ==>
    can_label_of_bytes_flow_to pr trace_index el public))
  (ensures(can_label_of_bytes_flow_to pr trace_index (serialize_sequence_of_bytes seq) public))
  (decreases (length seq))


val serialized_sequence_of_bytes_flows_to_public_implies_elements_flow_to_public:
(pr:preds) ->
(trace_index:nat) ->
(seq:Seq.seq bytes) ->
  Lemma
  (requires(can_label_of_bytes_flow_to pr trace_index (serialize_sequence_of_bytes seq) public))
  (ensures
    (forall (i:nat). (i<Seq.length seq) ==>
    can_label_of_bytes_flow_to pr trace_index seq.[i] public))  
  (decreases (length seq))

val label_of_domain_flows_to_public:
  (pr:preds) ->
  (trace_index:nat) ->
  (d:domain) ->
  Lemma (can_label_of_bytes_flow_to pr trace_index (serialize_domain d) public)
  
(**
  Given a sequence of domains,the label of the serialized sequence also flows to public.
*)
val serialized_sequence_of_domains_flows_to_public:
  (pr:preds) ->
  (trace_index:nat) ->
  (seq:Seq.seq domain)->
  Lemma
  (ensures(can_label_of_bytes_flow_to pr trace_index (serialize_sequence_of_domains seq) public))
  (decreases (length seq))
 
(**
  Given a url that contains no secrets (according to is_url_publishable), the label of the
  serialized url flows to public.
*)
val label_of_url_flows_to_public: (pr:preds) -> (trace_index:nat) -> (u:url)->
  Lemma
  (requires (is_url_publishable pr trace_index u))
  (ensures(can_label_of_bytes_flow_to pr trace_index (serialize_url u) public))



(**
  The same as for label_of_url_flows_to_public, but for option urls.

  If the option url is not None and contains no secrets (according to is_url_publishable), then
  the label of the serialized optional url flows to public.
*)
val label_of_opt_url_flows_to_public: (pr:preds) -> (trace_index:nat) -> (u:option url) ->
  Lemma
  (requires (Some? u /\ is_url_publishable pr trace_index (Some?.v u)))
  (ensures(can_label_of_bytes_flow_to pr trace_index (serialize_opt_url u) public))
  
(**
  Given a sequence of urls that fulfills is_url_publishable, the label of the serialized
  sequence flows to public.
*)
val label_of_sequence_of_urls_flows_to_public: (pr:preds) -> (trace_index:nat) -> (seq:Seq.seq url) ->
  Lemma
  (requires (forall url. Seq.contains seq url ==> is_url_publishable pr trace_index url))
  (ensures(can_label_of_bytes_flow_to pr trace_index (serialize_sequence_of_urls seq) public))
  (decreases (Seq.length seq))
 

(** The same as for label_of_sequence_of_urls_flows_to_public, but for option sequences. *)
val label_of_opt_sequence_of_urls_flows_to_public: (pr:preds) -> (trace_index:nat) -> (opt_seq:option (Seq.seq url)) -> 
  Lemma
  (requires (forall url. Some? opt_seq /\ Seq.contains (Some?.v opt_seq) url ==> is_url_publishable pr trace_index url))
  (ensures(can_label_of_bytes_flow_to pr trace_index ( serialize_opt_seq_of_urls opt_seq) public))
 
(**
  Predicate on http requests that is true if basically every component of the request is publishable.
*)
let all_elements_of_http_request_are_publishable (pr:preds) (trace_index:nat) (req: http_request) =
 is_publishable_p pr trace_index req.req_id /\
 is_publishable_p pr trace_index (serialize_request_uri req.req_uri) /\
 is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples req.req_headers) /\
 is_publishable_p pr trace_index req.req_body

(**
  Predicate on http responses that is true if basically every component of the response is publishable.
*)
let all_elements_of_http_response_are_publishable (pr:preds) (trace_index:nat) (resp:http_response) =
  let req_id = resp.resp_req_id in
  let headers = resp.resp_headers in
  let body = resp.resp_body in
  is_publishable_p pr trace_index req_id /\
  is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples headers) /\
  is_publishable_p pr trace_index body

val all_elements_of_http_request_are_publishable_later_lemma:
  pr:preds -> 
  trace_index:nat -> 
  req: http_request ->
  Lemma
  (requires all_elements_of_http_request_are_publishable pr trace_index req)
  (ensures forall i. later trace_index i ==> all_elements_of_http_request_are_publishable pr i req)


(**
label of serialized http request can flow to public
*)
val label_of_http_request_can_flow_to_public:
  (pr:preds) ->
  (trace_index:nat) ->
  (http_req: http_request) ->
 Lemma
  (requires all_elements_of_http_request_are_publishable pr trace_index http_req)
  (ensures (can_label_of_bytes_flow_to pr trace_index (serialize_http_request http_req) public))


(**
label of serialized http response can flow to public
*)
val label_of_http_response_can_flow_to_public:
  (pr:preds) ->
  (trace_index:nat) ->
  (http_resp: http_response) ->
 Lemma
  (requires all_elements_of_http_response_are_publishable pr trace_index http_resp)
  (ensures (can_label_of_bytes_flow_to pr trace_index (serialize_http_response http_resp) public))
 

val url_is_publishable_implies_request_uri_is_publishable:
  pr: preds ->
  (trace_index:nat) ->
  _url: url ->
 Lemma
 (requires is_publishable_p pr trace_index (serialize_url _url))
 (ensures is_publishable_p pr trace_index (serialize_request_uri _url.url_request_uri))
 

val serialization_empty_sequence_http_header_is_publishable:
  pr: preds ->
  (trace_index:nat) ->
  headers:Seq.seq http_header ->
  Lemma
  (requires Seq.length headers = 0)
  (ensures is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples headers))
  
val http_request_is_publishable_implies_request_id_is_publishable:
  pr: preds ->
  (trace_index:nat) ->
  req: http_request ->
  Lemma
  (requires is_publishable_p pr trace_index (serialize_http_request req))
  (ensures is_publishable_p pr trace_index req.req_id)

(**
  If bytes (that is an option bytes) is publishable, then the bytes resulting from first parsing the
  bytes, and again serializing it, is still publishable.
*)
val serialize_parse_option_bytes_publishablity_lemma:
    (pr:preds)-> (trace_index:nat)->
    (t:bytes)->
 Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_option_bytes t)
    ))
    (ensures (
      let t = Success?.v (parse_option_bytes t) in
      is_publishable_p pr trace_index (serialize_option_bytes t)
    ))
 



(**
  If bytes (that is a sequence of bytes) is publishable, then the parsed sequence contains only
  bytes that are publishable.
*)
val parsed_sequence_of_bytes_contains_only_publishable_bytes:
    (pr:preds)-> (trace_index:nat)->
    (t:bytes)->
   Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_sequence_of_bytes t)
    ))
    (ensures(
      let parsed_sequence = Success?.v (parse_sequence_of_bytes t) in
      forall x. Seq.contains parsed_sequence x ==> is_publishable_p pr trace_index x
    ))
    (decreases (bytes_depth t))
  


(**
  If a sequence of bytes contains only bytes that are publishable, then the serialized sequence is
  also publishable.
*)
val serialized_sequence_of_bytes_publishable_if_all_elements_publishable:
    (pr:preds)-> (trace_index:nat)->
    (seq:seq bytes)->
   Lemma
    (requires (
      forall x. Seq.contains seq x ==> is_publishable_p pr trace_index x
    ))
    (ensures (
      let serialized_sequence = serialize_sequence_of_bytes seq in
      is_publishable_p pr trace_index serialized_sequence
    ))
    (decreases (Seq.length seq))
 


(**
  If bytes (that is a sequence of bytes) is publishable, then the bytes resulting from first parsing
  the sequence, and again serializing it, is still publishable.
*)
val serialize_parse_sequence_of_bytes_publishability_lemma:
    (pr:preds)-> (trace_index:nat)->
    (t:bytes)->
   Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_sequence_of_bytes t)
    ))
    (ensures (
      let parsed_sequence = Success?.v (parse_sequence_of_bytes t) in
      is_publishable_p pr trace_index (serialize_sequence_of_bytes parsed_sequence)
    ))
    (decreases (bytes_depth t))
 


(**
  If bytes (that is a sequence of bytes tuples) is publishable, then the parsed sequence contains
  only bytes that are publishable.
*)
val parsed_sequence_of_bytes_tuples_contains_only_publishable_bytes:
    (pr:preds)-> (trace_index:nat)->
    (msg:bytes)->
   Lemma
    (requires (
      is_publishable_p pr trace_index msg /\
      Success? (parse_sequence_of_bytes_tuples msg)
    ))
    (ensures (
      let parsed_sequence = Success?.v (parse_sequence_of_bytes_tuples msg) in
      forall x. Seq.contains parsed_sequence x ==> is_publishable_p pr trace_index (dy_concat (fst x) (snd x))
    ))
    (decreases (bytes_depth msg))
 

(**
  If a sequence of bytes tuples contains only bytes that are publishable, then the serialized sequence is
  also publishable.
*)
val serialized_sequence_of_bytes_tuples_publishable_if_all_elements_publishable
    (pr:preds) (trace_index:nat)
    (seq:seq (bytes * bytes))
  : Lemma
    (requires(
      forall x. Seq.contains seq x ==> is_publishable_p pr trace_index (dy_concat (fst x) (snd x))
    ))
    (ensures(
      let serialized_sequence = serialize_sequence_of_bytes_tuples seq in
      is_publishable_p pr trace_index serialized_sequence
    ))
    (decreases (Seq.length seq))
 

(**
  If bytes (that is a sequence of bytes tuples) is publishable, then the bytes resulting from first
  parsing the sequence, and again serializing it, is still publishable.
*)
val serialize_parse_sequence_of_bytes_tuples_publishability_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_sequence_of_bytes_tuples t)
    ))
    (ensures (
      let parsed_sequence = Success?.v (parse_sequence_of_bytes_tuples t) in
      is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples parsed_sequence)
    ))
    (decreases (bytes_depth t))
 


(**
  If bytes (that is a request_uri) is publishable, then the bytes resulting from first parsing
  the request uri, and again serializing it, is still publishable.
*)
val serialize_parse_request_uri_publishability_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_request_uri t)
    ))
    (ensures (
      let parsed_request_uri = Success?.v (parse_request_uri t) in
      is_publishable_p pr trace_index (serialize_request_uri parsed_request_uri)
    ))
    (decreases (bytes_depth t))



(**
  If bytes (that is an http_request) is publishable, then the components of the parsed request are
  also publishable.
*)
val serialize_parse_http_request_publishablity_lemma_helper
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index msg /\
      Success? (parse_http_request msg)
    ))
    (ensures (
      let http_req = Success?.v (parse_http_request msg) in
      let id = http_req.req_id in
      let method = http_req.req_method in
      let uri = http_req.req_uri in
      let headers = http_req.req_headers in
      let body = http_req.req_body in
      (is_publishable_p pr trace_index id) /\
      (is_publishable_p pr trace_index (serialize_request_uri uri)) /\
      (is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples headers)) /\
      (is_publishable_p pr trace_index body)
    ))
  


(**
  If bytes (that is an http_request) is publishable, then the bytes resulting from first parsing
  the request, and again serializing it, is still publishable.
*)
val serialize_parse_http_request_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index msg /\
      Success? (parse_http_request msg)
    ))
    (ensures (
      let http_req = Success?.v (parse_http_request msg) in
      is_publishable_p pr trace_index (serialize_http_request http_req)
    ))


(**
  If bytes (that is an http_response) is publishable, then the headers of the parsed response is
  also publishable.
*)
val serialize_parse_http_response_publishablity_lemma_helper
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index msg /\
      Success? (parse_http_response msg)
    ))
    (ensures(
      let http_resp = Success?.v (parse_http_response msg) in
      let headers = http_resp.resp_headers in
      is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples headers)
    ))
 

(**
  If bytes (that is an http_response) is publishable, then the bytes resulting from first parsing
  the response, and again serializing it, is still publishable.
*)
val serialize_parse_http_response_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index msg /\
      Success? (parse_http_response msg)
    ))
    (ensures (
      let http_resp = Success?.v (parse_http_response msg) in
      is_publishable_p pr trace_index (serialize_http_response http_resp)
    ))
 

(**
  If bytes (that is an url) is publishable, then the bytes resulting from first parsing
  the response, and again serializing it, is still publishable.
*)
val serialize_parse_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_url t)
    ))
    (ensures (
      let url = Success?.v (parse_url t) in
      is_publishable_p pr trace_index (serialize_url url)
    ))
  

(**
  If bytes (that is an option url) is publishable, then the bytes resulting from first parsing
  the bytes, and again serializing it, is still publishable.
*)
val serialize_parse_opt_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_opt_url t)
    ))
    (ensures (
      let opt_url = Success?.v (parse_opt_url t) in
      is_publishable_p pr trace_index (serialize_opt_url opt_url)
    ))
 

(**
  If bytes (that is a sequence of urls) is publishable, then the bytes resulting from first parsing
  the bytes, and again serializing it, is still publishable.
*)
val serialize_parse_seq_of_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_sequence_of_urls t)
    ))
    (ensures (
      let url_seq = Success?.v (parse_sequence_of_urls t) in
      is_publishable_p pr trace_index (serialize_sequence_of_urls url_seq)
    ))
    (decreases (DY.Crypto.bytes_depth t))
  


(**
  If bytes (that is an option sequence of urls) is publishable, then the bytes resulting from first
  parsing the bytes, and again serializing it, is still publishable.
*)
val serialize_parse_opt_seq_of_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_opt_seq_of_urls t)
    ))
    (ensures (
      let opt_url_seq = Success?.v (parse_opt_seq_of_urls t) in
      is_publishable_p pr trace_index (serialize_opt_seq_of_urls opt_url_seq)
    ))
 

(**
  If bytes (that is a sequence of urls) is publishable, then the parsed sequence contains only
  urls that are publishable (after serialization).
*)
val parsed_sequence_of_urls_contains_only_publishable_urls
    (pr:preds) (trace_index:nat)
    (t:bytes)
  : Lemma
    (requires (
      is_publishable_p pr trace_index t /\
      Success? (parse_sequence_of_urls t)
    ))
    (ensures(
      let parsed_sequence = Success?.v (parse_sequence_of_urls t) in
      forall x. Seq.contains parsed_sequence x ==> is_publishable_p pr trace_index (serialize_url x)
    ))
    (decreases (bytes_depth t))


(**
  If an http response is publishable, then the body of the response is also publishable.
*)
val http_response_is_publishable_implies_body_is_publishable:
  pr:preds ->
  trace_index:nat ->
  response:http_response ->
  Lemma
  (requires is_publishable_p pr trace_index (serialize_http_response response))
  (ensures is_publishable_p pr trace_index response.resp_body)


(**
  If an http request is publishable, then the body of the request is also publishable.
*)
val http_request_is_publishable_implies_body_is_publishable:
  pr:preds ->
  trace_index:nat ->
  request:http_request ->
  Lemma
  (requires is_publishable_p pr trace_index (serialize_http_request request))
  (ensures is_publishable_p pr trace_index request.req_body)



val serialized_sequence_of_bytes_tuples_publishable_implies_elements_publishable:
(pr:preds) ->
(trace_index:nat) ->
(seq:Seq.seq (bytes*bytes)) ->
  Lemma
  (requires(is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples seq) ))
  (ensures
    (forall (i:nat). (i<Seq.length seq) ==>
    is_publishable_p pr trace_index (fst seq.[i]) /\ is_publishable_p pr trace_index (snd seq.[i]) ))  
  (decreases (length seq))

val http_response_is_publishable_implies_headers_are_publishable:
  pr:preds ->
  trace_index:nat ->
  response:http_response ->
  Lemma
  (requires is_publishable_p pr trace_index (serialize_http_response response))
  (ensures forall (i:nat). i < Seq.length response.resp_headers ==> (is_publishable_p pr trace_index (fst response.resp_headers.[i])) /\ (is_publishable_p pr trace_index (snd response.resp_headers.[i])))
