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

(*! No serialization/parsing functions in here! Put them in SerializationHelpers instead! *)

// Note that we actually need much less for this file, but due to the way F* typechecks modules with
// an interface, we have to assign enough resources to check everything in the interface (pragmas
// like #push-options from the fsti file are ignored when F* typechecks the implementation + the
// interface).
#set-options "--z3rlimit 50 --max_fuel 4 --max_ifuel 4"

let url_contains_no_secrets_later_lemma pr idx u = ()


#push-options "--max_fuel 1"

let rec serialized_sequence_of_bytes_flows_to_public_if_elements_flow_to_public pr trace_index seq
  =
    match length seq with
      | 0 -> ()
      | _ ->
        let hd = head seq in
        let tl = tail seq in
        Seq.Properties.contains_cons hd tl hd;
        concatenation_of_publishable_bytes_is_publishable_forall pr;
        assert(Seq.contains seq hd);
        serialized_sequence_of_bytes_flows_to_public_if_elements_flow_to_public pr trace_index tl;
        assert(can_label_of_bytes_flow_to pr trace_index (serialize_sequence_of_bytes tl) public)
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let rec serialized_sequence_of_bytes_flows_to_public_implies_elements_flow_to_public pr trace_index seq
  =
    assert(is_publishable_p pr trace_index (serialize_sequence_of_bytes seq));
    match length seq with
      | 0 -> ()
      | _ -> 
        let hd = head seq in
        let tl = tail seq in
        assert(serialize_sequence_of_bytes seq == concat hd (serialize_sequence_of_bytes tl));
        concatenation_publishable_implies_components_publishable_forall pr;
        assert(can_label_of_bytes_flow_to pr trace_index hd public);
        serialized_sequence_of_bytes_flows_to_public_implies_elements_flow_to_public pr trace_index tl;
        assert(forall (i:nat). (i<Seq.length tl) ==>
    can_label_of_bytes_flow_to pr trace_index tl.[i] public);
        assert(forall (i:nat). (i<Seq.length tl) ==> tl.[i]==seq.[i+1]);
        
        assert(seq.[0] == hd);
        assert(length tl + 1 = length seq);
        assert(forall (i:nat). i < length seq ==> i = 0 \/ i>0);
        assert(forall (i:nat). (i<Seq.length seq /\ i >0) ==> tl.[i-1]==seq.[i]);
        ()
#pop-options


#push-options "--max_ifuel 1 --max_fuel 1"
let rec label_of_domain_flows_to_public pr trace_index d
  =
    match d with
    | Root str -> concatenation_of_publishable_bytes_is_publishable_forall pr
    | Sub sub dom -> (
      label_of_domain_flows_to_public pr trace_index dom;
      concatenation_of_publishable_bytes_is_publishable_forall pr
    )
#pop-options

#push-options "--max_fuel 1"
let rec serialized_sequence_of_domains_flows_to_public pr trace_index seq
  =
    match length seq with
      | 0 -> ()
      | _ ->
        let hd = head seq in
        let tl = tail seq in
        Seq.Properties.contains_cons hd tl hd;
        concatenation_of_publishable_bytes_is_publishable_forall pr;
        assert(Seq.contains seq hd);
        serialized_sequence_of_domains_flows_to_public pr trace_index tl;
        assert(can_label_of_bytes_flow_to pr trace_index (serialize_sequence_of_domains tl) public);
        label_of_domain_flows_to_public pr trace_index hd
#pop-options

#push-options "--max_ifuel 1"
let label_of_url_flows_to_public pr trace_index u
  =
    let request_uri = u.url_request_uri in
    let path = request_uri.uri_path in
    let querystring = request_uri.uri_querystring in
    let fragment = request_uri.uri_fragment in
    let serialized_path = serialize_sequence_of_bytes path in
    let serialized_querystring = serialize_sequence_of_bytes_tuples querystring in
    concatenation_of_publishable_bytes_is_publishable_forall pr;
    serialized_sequence_of_bytes_flows_to_public_if_elements_flow_to_public pr trace_index path;
    assert(can_label_of_bytes_flow_to pr trace_index serialized_path public);
    assert(can_label_of_bytes_flow_to pr trace_index serialized_querystring public);
    assert(match fragment with
           | Some f -> can_label_of_bytes_flow_to pr trace_index f public
           | None -> True);
    assert(can_label_of_bytes_flow_to pr trace_index (serialize_request_uri request_uri) public);
    assert(can_label_of_bytes_flow_to pr trace_index (serialize_scheme u.url_scheme) public);
    label_of_domain_flows_to_public pr trace_index u.url_domain
#pop-options


let label_of_opt_url_flows_to_public pr trace_index u
  =
  match u with
  |None -> ()
  |Some url -> label_of_url_flows_to_public pr trace_index url


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let rec label_of_sequence_of_urls_flows_to_public pr trace_index seq
  =
    match Seq.length seq with
    | 0 -> ()
    | _ ->
        let hd = head seq in
        let tl = tail seq in
        Seq.Properties.contains_cons hd tl hd;
        label_of_url_flows_to_public pr trace_index hd;
        label_of_sequence_of_urls_flows_to_public pr trace_index tl;
        concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options


let label_of_opt_sequence_of_urls_flows_to_public pr trace_index opt_seq
  =
    match opt_seq with
    | None -> ()
    | Some seq -> label_of_sequence_of_urls_flows_to_public pr trace_index seq


let all_elements_of_http_request_are_publishable_later_lemma pr trace_index req =
  is_publishable_p_later_lemma pr trace_index req.req_id;
  is_publishable_p_later_lemma pr trace_index (serialize_request_uri req.req_uri);
  is_publishable_p_later_lemma pr trace_index (serialize_sequence_of_bytes_tuples req.req_headers);
 is_publishable_p_later_lemma pr trace_index req.req_body

#push-options "--max_fuel 1 --max_ifuel 1"
let label_of_http_request_can_flow_to_public pr trace_index http_req
  = concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options


#push-options "--max_fuel 1 --max_ifuel 1"
let label_of_http_response_can_flow_to_public pr trace_index http_resp
  = concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options


let url_is_publishable_implies_request_uri_is_publishable pr trace_index _url =
  concatenation_publishable_implies_components_publishable_forall pr

#push-options "--max_fuel 1 --max_ifuel 0"
let serialization_empty_sequence_http_header_is_publishable pr trace_index headers = ()
#pop-options


let http_request_is_publishable_implies_request_id_is_publishable pr trace_index req =
  concatenation_publishable_implies_components_publishable_forall pr

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
(**
  If bytes (that is an option bytes) is publishable, then the bytes resulting from first parsing the
  bytes, and again serializing it, is still publishable.
*)
let serialize_parse_option_bytes_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    splittable_bytes_publishable_implies_components_publishable_forall pr;
    concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let rec parsed_sequence_of_bytes_contains_only_publishable_bytes
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    let parsed_sequence = Success?.v (parse_sequence_of_bytes t) in
    match dy_split t with
    | Success (hd, tl) -> (
      if Success? (parse_sequence_of_bytes tl) then (
        splittable_bytes_publishable_implies_components_publishable_forall pr;
         parsed_sequence_of_bytes_contains_only_publishable_bytes pr trace_index tl
      ) else ()
      )
    | _ -> (
      if eq_bytes (string_to_bytes "EndOfSequenceOfBytes") t then (
        assert(parsed_sequence == empty);
        Seq.Properties.lemma_contains_empty #bytes
      ) else ()
      )
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let rec serialized_sequence_of_bytes_publishable_if_all_elements_publishable
    (pr:preds) (trace_index:nat)
    (seq:seq bytes)
 
  =
    match length seq with
    | 0 -> ()
    | _ ->
      let hd = head seq in
      let tl = tail seq in
      Seq.Properties.contains_cons hd tl hd;
      serialized_sequence_of_bytes_publishable_if_all_elements_publishable pr trace_index tl;
      concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let serialize_parse_sequence_of_bytes_publishability_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    let parsed_sequence = Success?.v (parse_sequence_of_bytes t) in
    splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split t with
    | Success (hd, tl) -> (
        if Success? (parse_sequence_of_bytes tl) then (
        parsed_sequence_of_bytes_contains_only_publishable_bytes pr trace_index t;
        assert(forall x. Seq.contains parsed_sequence x ==> is_publishable_p pr trace_index x);
        serialized_sequence_of_bytes_publishable_if_all_elements_publishable pr trace_index parsed_sequence
      ) else ()
      )
    | _ -> ()
#pop-options


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
(**
  If bytes (that is a sequence of bytes tuples) is publishable, then the parsed sequence contains
  only bytes that are publishable.
*)
let rec parsed_sequence_of_bytes_tuples_contains_only_publishable_bytes
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  =
    let parsed_sequence = Success?.v (parse_sequence_of_bytes_tuples msg) in
    match dy_split msg with
    | Success (hd, tl) -> (
      if Success? (parse_sequence_of_bytes_tuples tl) then (
        splittable_bytes_publishable_implies_components_publishable_forall pr;
        parsed_sequence_of_bytes_tuples_contains_only_publishable_bytes pr trace_index tl
      ) else ()
      )
    | _ -> (
      if eq_bytes (string_to_bytes "EndOfSequenceofBytesTuples") msg then (
        assert(parsed_sequence == empty);
        Seq.Properties.lemma_contains_empty #(bytes*bytes)
      ) else ()
      )
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let rec serialized_sequence_of_bytes_tuples_publishable_if_all_elements_publishable
    (pr:preds) (trace_index:nat)
    (seq:seq (bytes * bytes))
  =
    match length seq with
    | 0 -> ()
    | _ ->
      let hd = head seq in
      let tl = tail seq in
      Seq.Properties.contains_cons hd tl hd;
      serialized_sequence_of_bytes_tuples_publishable_if_all_elements_publishable pr trace_index tl;
      concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let serialize_parse_sequence_of_bytes_tuples_publishability_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    concatenation_of_publishable_bytes_is_publishable_forall pr;
    let parsed_sequence = Success?.v (parse_sequence_of_bytes_tuples t) in
    match dy_split t with
    | Success (hd, tl) -> (
      match dy_split hd with
      | Success (hd1, hd2) -> (
         parsed_sequence_of_bytes_tuples_contains_only_publishable_bytes pr trace_index t;
        assert(forall x. Seq.contains parsed_sequence x ==> is_publishable_p pr trace_index (dy_concat (fst x) (snd x)));
         serialized_sequence_of_bytes_tuples_publishable_if_all_elements_publishable pr trace_index parsed_sequence
      )
    )
    | _ -> ()
#pop-options


let serialize_parse_request_uri_publishability_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    match dy_split t with
    | Success (t1, ser_fragment) -> (
      match dy_split t1 with
      | Success (ser_path, ser_querystring) -> (
        match parse_sequence_of_bytes ser_path,
              parse_sequence_of_bytes_tuples ser_querystring,
              parse_option_bytes ser_fragment with
        | Success path, Success querystring, Success fragment -> (
          splittable_bytes_publishable_implies_components_publishable_forall pr;
          concatenation_of_publishable_bytes_is_publishable_forall pr;

          assert(is_publishable_p pr trace_index ser_path);
          serialize_parse_sequence_of_bytes_publishability_lemma pr trace_index ser_path;
          assert(is_publishable_p pr trace_index (serialize_sequence_of_bytes path));

          assert(is_publishable_p pr trace_index ser_fragment);
          serialize_parse_option_bytes_publishablity_lemma pr trace_index ser_fragment;
          assert(is_publishable_p pr trace_index (serialize_option_bytes fragment));

          assert(is_publishable_p pr trace_index ser_querystring);
          serialize_parse_sequence_of_bytes_tuples_publishability_lemma pr trace_index ser_querystring;
          assert(is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples querystring))
        )
      )
    )

(**
  If bytes (that is an http_request) is publishable, then the components of the parsed request are
  also publishable.
*)
let serialize_parse_http_request_publishablity_lemma_helper
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  =
    splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split msg with
    | Success (t1, body) -> (
      assert(Helpers.is_succ2 (DY.Crypto.split msg) t1 body);
      assert(is_publishable_p pr trace_index t1);
      assert(is_publishable_p pr trace_index body);
      match dy_split t1 with
      | Success (t2, s_headers) -> (
        assert(Helpers.is_succ2 (DY.Crypto.split t1) t2 s_headers);
        assert(is_publishable_p pr trace_index t2);
        assert(is_publishable_p pr trace_index s_headers);
        match dy_split t2 with
        | Success (t3, s_uri) -> (
          assert(Helpers.is_succ2 (DY.Crypto.split t2) t3 s_uri);
          assert(is_publishable_p pr trace_index t3);
          assert(is_publishable_p pr trace_index s_uri);
          match dy_split t3 with
          | Success (id, s_method) -> (
            assert(Helpers.is_succ2 (DY.Crypto.split t3) id s_method);
            assert(is_publishable_p pr trace_index id);
            assert(is_publishable_p pr trace_index s_method);
            match parse_sequence_of_bytes_tuples s_headers,
                  parse_request_uri s_uri,
                  parse_http_method s_method with
            | Success headers, Success uri, Success method -> (
              concatenation_of_publishable_bytes_is_publishable_forall pr;
              splittable_bytes_publishable_implies_components_publishable_forall pr;
              serialize_parse_request_uri_publishability_lemma pr trace_index s_uri;
              serialize_parse_sequence_of_bytes_tuples_publishability_lemma pr trace_index s_headers;
              assert(is_publishable_p pr trace_index s_uri);
              assert(is_publishable_p pr trace_index (serialize_request_uri uri));
              assert(is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples headers))
              )
            )
          )
        )
      )

let serialize_parse_http_request_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  =
    let http_req = Success?.v (parse_http_request msg) in
    let id = http_req.req_id in
    let method = http_req.req_method in
    let uri = http_req.req_uri in
    let headers = http_req.req_headers in
    let body = http_req.req_body in
    serialize_parse_http_request_publishablity_lemma_helper pr trace_index msg;
    label_of_http_request_can_flow_to_public pr trace_index http_req


let serialize_parse_http_response_publishablity_lemma_helper
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  =
    splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split msg with
    | Success (t1, body) -> (
      assert(Helpers.is_succ2 (DY.Crypto.split msg) t1 body);
      match dy_split t1 with
      | Success (t2, s_headers) -> (
        assert(Helpers.is_succ2 (DY.Crypto.split t1) t2 s_headers);
        assert(is_publishable_p pr trace_index s_headers);
        serialize_parse_sequence_of_bytes_tuples_publishability_lemma pr trace_index s_headers
        )
      )


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let serialize_parse_http_response_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (msg:bytes)
  =
    let http_resp = Success?.v (parse_http_response msg) in
    let id = http_resp.resp_req_id in
    let headers = http_resp.resp_headers in
    let body = http_resp.resp_body in
    splittable_bytes_publishable_implies_components_publishable_forall pr;
    assert(is_publishable_p pr trace_index id);
    assert(is_publishable_p pr trace_index body);
    serialize_parse_http_response_publishablity_lemma_helper pr trace_index msg;
    assert(is_publishable_p pr trace_index (serialize_sequence_of_bytes_tuples headers));
    assert(all_elements_of_http_response_are_publishable pr trace_index http_resp);
    label_of_http_response_can_flow_to_public pr trace_index http_resp
#pop-options



#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let serialize_parse_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split t with
    | Success (t1, ser_req_uri) -> (
      assert(is_succ2 (dy_split t) t1 ser_req_uri);
      match dy_split t1 with
      | Success (ser_scheme, ser_domain) -> (
        assert(is_succ2 (dy_split t1) ser_scheme ser_domain);
        match parse_scheme ser_scheme, parse_domain ser_domain, parse_request_uri ser_req_uri with
        | Success scheme, Success domain, Success uri -> (
          assert(is_publishable_p pr trace_index ser_req_uri);
          serialize_parse_request_uri_publishability_lemma pr trace_index ser_req_uri;
          assert(is_publishable_p pr trace_index (serialize_request_uri uri));
          label_of_domain_flows_to_public pr trace_index domain;
          assert(is_publishable_p pr trace_index (serialize_domain domain));
          assert(is_publishable_p pr trace_index (serialize_scheme scheme));
          concatenation_of_publishable_bytes_is_publishable_forall pr
          )
        )
      )
#pop-options


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let serialize_parse_opt_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    match bytes_to_string t with
    | Success "OptURL:None" -> ()
    | _ -> (
      match parse_url t with
      | Success u ->
        serialize_parse_url_publishablity_lemma pr trace_index t;
        assert(is_publishable_p pr trace_index (serialize_url u))
      )
#pop-options

#push-options "--z3rlimit 150 --max_fuel 2 --max_ifuel 0"
let rec serialize_parse_seq_of_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split t with
    | Success (hd, tl) ->
     assert(is_succ2 (dy_split t) hd tl);
     if Success? (parse_sequence_of_urls tl) && Success? (parse_url hd) then (
      assert(is_publishable_p pr trace_index hd);
      assert(is_publishable_p pr trace_index tl);
      let parsed_seq = (cons (Success?.v (parse_url hd)) (Success?.v (parse_sequence_of_urls tl))) in

      let parsed_seq_hd = head parsed_seq in
      let parsed_seq_tl = tail parsed_seq in
      let serialized_seq_hd = serialize_url parsed_seq_hd in
      let serialized_seq_tl = serialize_sequence_of_urls parsed_seq_tl in
      let serialized_seq = dy_concat serialized_seq_hd serialized_seq_tl in

      serialize_parse_url_publishablity_lemma pr trace_index hd;
      assert(is_publishable_p pr trace_index serialized_seq_hd);
      serialize_parse_seq_of_url_publishablity_lemma pr trace_index tl;
      Seq.Properties.lemma_tl (Success?.v (parse_url hd))(Success?.v (parse_sequence_of_urls tl));
      assert((Success?.v (parse_sequence_of_urls tl)) == parsed_seq_tl);
      assert(is_publishable_p pr trace_index serialized_seq_tl);
      concatenation_of_publishable_bytes_is_publishable_forall pr;
      assert(is_publishable_p pr trace_index serialized_seq)
      ) else ()
    | _ ->
      if eq_bytes (string_to_bytes "EndOfSequenceOfURLs") t then
        ()
      else
        ()
#pop-options


#push-options "--z3rlimit 150 --max_fuel 2 --max_ifuel 2"
(**
  If bytes (that is an option sequence of urls) is publishable, then the bytes resulting from first
  parsing the bytes, and again serializing it, is still publishable.
*)
let serialize_parse_opt_seq_of_url_publishablity_lemma
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    match bytes_to_string t with
    | Success "OptSeq:None" -> ()
    | _ ->
      match parse_sequence_of_urls t with
      | Success s -> serialize_parse_seq_of_url_publishablity_lemma pr trace_index t
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"
let rec parsed_sequence_of_urls_contains_only_publishable_urls
    (pr:preds) (trace_index:nat)
    (t:bytes)
  =
    let parsed_sequence = Success?.v (parse_sequence_of_urls t) in
    match dy_split t with
    | Success (hd, tl) -> (
      if Success? (parse_sequence_of_urls tl) && Success? (parse_url hd) then (
        splittable_bytes_publishable_implies_components_publishable_forall pr;
        assert(is_succ2 (dy_split t) hd tl);
        parsed_sequence_of_urls_contains_only_publishable_urls pr trace_index tl;
        serialize_parse_url_publishablity_lemma pr trace_index hd;
        assert(is_publishable_p pr trace_index (serialize_url (Success?.v (parse_url hd))))
      ) else ()
      )
    | _ -> (
      if eq_bytes (string_to_bytes "EndOfSequenceOfURLs") t then (
        assert(parsed_sequence == empty);
        Seq.Properties.lemma_contains_empty #url
      ) else ()
      )
#pop-options

let http_response_is_publishable_implies_body_is_publishable pr trace_index resp =
  concatenation_publishable_implies_components_publishable_forall pr;
  assert(is_publishable_p pr trace_index resp.resp_body)


let http_request_is_publishable_implies_body_is_publishable pr trace_index req =
  concatenation_publishable_implies_components_publishable_forall pr;
  assert(is_publishable_p pr trace_index req.req_body)

let rec serialized_sequence_of_bytes_tuples_publishable_implies_elements_publishable pr trace_index seq = 
    match length seq with
      | 0 -> ()
      | _ -> 
        let hd = head seq in
        let tl = tail seq in
        assert(serialize_sequence_of_bytes_tuples seq == concat (concat (fst hd) (snd hd)) (serialize_sequence_of_bytes_tuples tl));
        concatenation_publishable_implies_components_publishable_forall pr;
        assert(is_publishable_p pr trace_index (concat (fst hd) (snd hd))); 
        serialized_sequence_of_bytes_tuples_publishable_implies_elements_publishable pr trace_index tl;
        assert(forall (i:nat). (i<Seq.length tl) ==>
    is_publishable_p pr trace_index (fst tl.[i]) /\ is_publishable_p pr trace_index (snd tl.[i])); 
        assert(forall (i:nat). (i<Seq.length tl) ==> tl.[i]==seq.[i+1]);
        
        assert(seq.[0] == hd);
        assert(length tl + 1 = length seq);
        assert(forall (i:nat). i < length seq ==> i = 0 \/ i>0);
        assert(forall (i:nat). (i<Seq.length seq /\ i >0) ==> tl.[i-1]==seq.[i]);
        ()
        
let http_response_is_publishable_implies_headers_are_publishable pr trace_index res =
  concatenation_publishable_implies_components_publishable_forall pr;
  assert(is_publishable_p pr trace_index ((serialize_sequence_of_bytes_tuples res.resp_headers)));
  serialized_sequence_of_bytes_tuples_publishable_implies_elements_publishable pr trace_index res.resp_headers;
  ()
  
