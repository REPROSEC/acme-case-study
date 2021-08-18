/// ACME.Data.SerializationLemmas (implementation)
/// ===============================================
module ACME.Data.SerializationLemmas

module LC = Labeled.Crypto
open Web.Messages
module DC = DY.Crypto
open DY.Trace
open DY.Principals
open DY.Labels
open Labeled.ApplicationAPI
open Application.Predicates
friend Application.Predicates
open ACME.Data
friend ACME.Data
open ACME.Data.SerializationHelpers
friend ACME.Data.SerializationHelpers
open ACME.Data.Predicates

open SerializationHelpers
open SerializationLemmas
open Web.Messages

open FStar.Seq

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 2"

let serialized_acme_status_label_flows_to_public trace_index status = ()

let serialized_option_acme_order_status_label_flows_to_public trace_index status = ()


#push-options "--z3rlimit 50 --max_fuel 2"
let serialized_acme_order_flows_to_public trace_index order =
  let status = order.acme_order_status in
  let identifiers = order.acme_order_identifiers in
  let authorizations = order.acme_order_authorizations in
  let finalize = order.acme_order_finalize in
  let certificate = order.acme_order_certificate in
  let serialized_status = serialize_opt_acme_order_status status in
  let serialized_identifiers = serialize_sequence_of_domains identifiers in
  serialized_sequence_of_domains_flows_to_public app_preds trace_index identifiers;
  assert(LC.is_publishable_p app_preds trace_index serialized_identifiers);
  let serialized_authorizations = serialize_opt_seq_of_urls authorizations in
  let serialized_finalize = serialize_opt_url finalize in
  let serialized_certificate = serialize_opt_url certificate in
  serialized_option_acme_order_status_label_flows_to_public trace_index status;
  label_of_opt_sequence_of_urls_flows_to_public app_preds trace_index authorizations;
  label_of_opt_url_flows_to_public app_preds trace_index finalize;
  LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
  assert (LC.can_label_of_bytes_flow_to app_preds trace_index serialized_status public);
  assert (LC.can_label_of_bytes_flow_to app_preds trace_index serialized_identifiers public);
  assert (LC.can_label_of_bytes_flow_to app_preds trace_index serialized_authorizations public);
  assert(LC.can_label_of_bytes_flow_to app_preds trace_index serialized_finalize public);
  match certificate with
  |None -> ()
  |Some c -> label_of_opt_url_flows_to_public app_preds trace_index certificate
#pop-options

let serialize_acme_server_st_issuedvalidnonce_lemma t s = ()


let parse_acme_server_st_of_client_st_returns_none st = ()

let parse_acme_client_st_of_server_st_returns_none st = ()


let serialized_acme_order_flows_to_public_implies_components_flow_to_public trace_index order =
  LC.concatenation_publishable_implies_components_publishable_forall app_preds;
  assert(LC.is_publishable_p app_preds trace_index (serialize_acme_order order))

let serialized_acme_authorization_flows_to_public_implies_components_flow_to_public trace_index authz =
  LC.concatenation_publishable_implies_components_publishable_forall app_preds;
  assert(LC.is_publishable_p app_preds trace_index (serialize_acme_authorization authz))

#push-options "--z3rlimit 150 --max_fuel 5 --max_ifuel 2"
let serialized_updated_acme_order_flows_to_public_status trace_index order =
     let identifiers = order.acme_order_identifiers in
     serialized_sequence_of_domains_flows_to_public app_preds trace_index identifiers;
     serialized_acme_order_flows_to_public_implies_components_flow_to_public trace_index order;
     LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds
#pop-options

#push-options "--z3rlimit 150 --max_fuel 5 --max_ifuel 2"
let serialized_updated_acme_order_flows_to_public trace_index order cert_url =
     let identifiers = order.acme_order_identifiers in
     serialized_sequence_of_domains_flows_to_public app_preds trace_index identifiers;
     serialized_acme_order_flows_to_public_implies_components_flow_to_public trace_index order;
     LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds
#pop-options

let serialized_updated_acme_challenge_flow_to_public trace_index challenge =
    LC.concatenation_publishable_implies_components_publishable_forall app_preds;
    LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
    assert(LC.is_publishable_p app_preds trace_index (serialize_acme_challenge challenge))

#push-options "--z3rlimit 150 --max_fuel 3 --max_ifuel 0"
let rec serialized_updated_acme_challenges_flow_to_public trace_index challenges challenge_index
    =
      LC.concatenation_publishable_implies_components_publishable_forall app_preds;
      LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
      assert(LC.is_publishable_p app_preds trace_index (serialize_sequence_of_acme_challenges challenges));
       match Seq.length challenges with
       | 0 -> ()
       | _ ->
           let hd = Seq.head challenges in
           let tl:Seq.seq acme_challenge = Seq.tail challenges in
           match challenge_index with
           | 0 -> ()
           | _ ->
           serialized_updated_acme_challenges_flow_to_public trace_index tl (challenge_index - 1)
#pop-options

#push-options "--z3rlimit 150 --max_fuel 3 --max_ifuel 0"
let rec sequence_of_challenges_publishable_implies_single_challenge_publishable trace_index challenge_sequence idx =
      LC.concatenation_publishable_implies_components_publishable_forall app_preds;
      LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
      assert(LC.is_publishable_p app_preds trace_index (serialize_sequence_of_acme_challenges challenge_sequence));
       match Seq.length challenge_sequence with
       | 0 -> ()
       | _ ->
           let hd = Seq.head challenge_sequence in
           let tl:Seq.seq acme_challenge = Seq.tail challenge_sequence in
           match idx with
           | 0 -> ()
           | _ -> sequence_of_challenges_publishable_implies_single_challenge_publishable trace_index tl (idx - 1)
#pop-options

let serialized_updated_acme_authorization_flows_to_public trace_index authz challenge_index =
    let old_challenge = authz.acme_authorization_challenges.[challenge_index] in
    let new_challenge = {old_challenge with acme_challenge_status = Processing} in
    let updated_authz = {
      authz with
      acme_authorization_challenges = authz.acme_authorization_challenges.[challenge_index] <- new_challenge
    } in
    let identifier = updated_authz.acme_authorization_identifier in
    let status = updated_authz.acme_authorization_status in
    let challenges = updated_authz.acme_authorization_challenges in
    LC.concatenation_publishable_implies_components_publishable_forall app_preds;
    serialized_acme_authorization_flows_to_public_implies_components_flow_to_public trace_index authz;
    LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
    serialized_updated_acme_challenges_flow_to_public trace_index authz.acme_authorization_challenges challenge_index

#push-options "--z3rlimit 150 --max_fuel 3 --max_ifuel 0"
let serialized_updated_acme_authorization_flows_to_public_challenge_and_authorization trace_index authz challenge_index =
    let challenge = Seq.index (authz.acme_authorization_challenges) challenge_index in
    let challenge' = {challenge with acme_challenge_status = Valid} in
    let authorization' = {authz with acme_authorization_challenges = authz.acme_authorization_challenges.[challenge_index] <- challenge'} in
    let authorization'' = {authorization' with acme_authorization_status = Valid} in
    let identifier = authorization''.acme_authorization_identifier in
    let status = authorization''.acme_authorization_status in
    let challenges = authorization''.acme_authorization_challenges in
    LC.concatenation_publishable_implies_components_publishable_forall app_preds;
    serialized_acme_authorization_flows_to_public_implies_components_flow_to_public trace_index authz;
    LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
    serialized_updated_acme_challenges_flow_to_public trace_index authz.acme_authorization_challenges challenge_index
#pop-options


#push-options "--z3rlimit 190 --initial_fuel 2 --max_fuel 6 --max_ifuel 4 "
let acme_challenge_contains_no_secrets_implies_flow_to_public trace_index (challenge:acme_challenge) =
    let challenge_type = challenge.acme_challenge_challenge_type in
    let challenge_url = challenge.acme_challenge_url in
    let challenge_status = challenge.acme_challenge_status in
    let challenge_token = challenge.acme_challenge_token in
    let serialized_challenge_type = serialize_acme_challenge_type challenge_type in
    let serialized_challenge_url = serialize_url challenge_url in
    let serialized_challenge_status = serialize_acme_status challenge_status in
    serialized_acme_status_label_flows_to_public trace_index challenge_status;
    label_of_url_flows_to_public app_preds trace_index challenge_url;
    LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
    assert(LC.can_label_of_bytes_flow_to app_preds trace_index serialized_challenge_url public);
    assert(LC.can_label_of_bytes_flow_to app_preds trace_index serialized_challenge_status public);
    assert(LC.can_label_of_bytes_flow_to app_preds trace_index serialized_challenge_type public)
    //assert(serialize_acme_challenge challenge ==
    //concat (concat (concat serialized_challenge_type serialized_challenge_url) serialized_challenge_status) challenge_token
    //)
#pop-options

#push-options "--max_fuel 1"
let rec sequence_of_acme_challenges_contains_no_secrets_implies_flow_to_public
  trace_index
  (challenge_seq:Seq.seq acme_challenge)
  =
    match Seq.length challenge_seq with
    | 0 -> ()
    | _ ->
      let hd = Seq.head challenge_seq in
      let tl = Seq.tail challenge_seq in
      Seq.Properties.contains_cons hd tl hd;
      assert(Seq.contains challenge_seq hd);
      acme_challenge_contains_no_secrets_implies_flow_to_public trace_index hd;
      sequence_of_acme_challenges_contains_no_secrets_implies_flow_to_public trace_index tl;
      LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds
#pop-options

let serialized_acme_authorization_can_flow_to_public trace_index (authz:acme_authorization) =
    let identifier = authz.acme_authorization_identifier in
    let status = authz.acme_authorization_status in
    let challenges = authz.acme_authorization_challenges in
    label_of_domain_flows_to_public app_preds trace_index identifier;
    assert(LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_domain identifier) public);
    assert(LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_acme_status status) public);
    sequence_of_acme_challenges_contains_no_secrets_implies_flow_to_public trace_index challenges;
    assert(LC.can_label_of_bytes_flow_to app_preds trace_index (serialize_sequence_of_acme_challenges challenges) public);
    LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"
(**
  If bytes (that is an acme_order] is publishable, then the bytes resulting from
  first parsing the order, and again serializing it, is still publishable.
*)
let serialize_parse_acme_order_publishability_lemma
    (pr:LC.preds)
    (trace_index:nat)
    (t:DC.bytes)
  : Lemma
    (requires (
      LC.is_publishable_p pr trace_index t /\
      Success? (parse_acme_order t)
    ))
    (ensures (
      LC.is_publishable_p pr trace_index (serialize_acme_order (Success?.v (parse_acme_order t)))
    ))
  =
    LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
    match DY.Crypto.split t with
    | Success (t1, s_cert_url) -> (
      assert(is_succ2 (DY.Crypto.split t) t1 s_cert_url);
      match DY.Crypto.split t1 with
      | Success (t2, s_finalize_url) -> (
        assert(is_succ2 (DY.Crypto.split t1) t2 s_finalize_url);
        match DY.Crypto.split t2 with
        | Success (t3, s_authzs) -> (
          assert(is_succ2 (DY.Crypto.split t2) t3 s_authzs);
          match DY.Crypto.split t3 with
          | Success (s_status, s_domains) -> (
            assert(is_succ2 (DY.Crypto.split t3) s_status s_domains);
            match parse_opt_url s_cert_url,
                  parse_opt_url s_finalize_url,
                  parse_opt_seq_of_urls s_authzs,
                  parse_opt_acme_order_status s_status,
                  parse_sequence_of_domains s_domains with
            | Success cert_url, Success finalize_url, Success authzs, Success status, Success domains -> (
              if Seq.length domains = 0 then () else (
                assert(LC.is_publishable_p pr trace_index s_status);
                assert(LC.is_publishable_p pr trace_index s_authzs);
                assert(LC.is_publishable_p pr trace_index s_finalize_url);
                assert(LC.is_publishable_p pr trace_index s_cert_url);
                assert(LC.is_publishable_p pr trace_index s_domains);
                serialize_parse_opt_url_publishablity_lemma pr trace_index s_cert_url;
                serialize_parse_opt_url_publishablity_lemma pr trace_index s_finalize_url;
                serialized_sequence_of_domains_flows_to_public pr trace_index domains;
                serialize_parse_opt_seq_of_url_publishablity_lemma pr trace_index s_authzs;
                assert(LC.is_publishable_p pr trace_index (serialize_sequence_of_domains domains));
                assert(LC.is_publishable_p pr trace_index (serialize_opt_seq_of_urls authzs));
                assert(LC.is_publishable_p pr trace_index (serialize_opt_url finalize_url));
                assert(LC.is_publishable_p pr trace_index (serialize_opt_url cert_url));
                LC.concatenation_of_publishable_bytes_is_publishable_forall pr
              )
              )
            )
          )
        )
      )
#pop-options


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"
(**
  If bytes (that is an acme_challenge) is publishable, then the bytes resulting from first
  parsing the challenge, and again serializing it, is still publishable.
*)
let serialize_parse_acme_challenge_publishability_lemma
    (pr:LC.preds)
    (trace_index:nat)
    (t:DC.bytes)
  : Lemma
    (requires (
      LC.is_publishable_p pr trace_index t /\
      Success? (parse_acme_challenge t)
    ))
    (ensures (
      LC.is_publishable_p pr trace_index (serialize_acme_challenge (Success?.v (parse_acme_challenge t)))
    ))
  =
    LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split t with
    | Success (t1, token) -> (
      assert(is_succ2 (dy_split t) t1 token);
      match dy_split t1 with
      | Success (t2, s_status) -> (
        assert(is_succ2 (dy_split t1) t2 s_status);
        match dy_split t2 with
        | Success (s_type, s_url) -> (
          assert(is_succ2 (dy_split t2) s_type s_url);
          match parse_acme_status s_status,
                parse_acme_challenge_type s_type,
                parse_url s_url with
          | Success status, Success c_type, Success url -> (
            if not(status = Pending || status = Processing || status = Valid || status = Invalid) then () else
              serialized_acme_status_label_flows_to_public trace_index status;
              serialize_parse_url_publishablity_lemma pr trace_index s_url;
              assert(LC.is_publishable_p pr trace_index (serialize_acme_challenge_type c_type));
              LC.concatenation_of_publishable_bytes_is_publishable_forall pr
            )
          | _ -> ()
          )
        )
      )
#pop-options


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"
(**
  If bytes (that is a sequence of [acme_challenge]s) is publishable, then the bytes resulting from
  first parsing the challenges, and again serializing it, is still publishable.
*)
let rec serialize_parse_sequence_of_acme_challenges_publishability_lemma
    (pr:LC.preds)
    (trace_index:nat)
    (t:DC.bytes)
  : Lemma
    (requires (
      LC.is_publishable_p pr trace_index t /\
      Success? (parse_sequence_of_acme_challenges t)
    ))
    (ensures (
      LC.is_publishable_p pr trace_index (serialize_sequence_of_acme_challenges (Success?.v (parse_sequence_of_acme_challenges t)))
    ))
    (decreases (DY.Crypto.bytes_depth t))
  =
    LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split t with
    | Error _ -> (
      match DC.bytes_to_string t with
      | Success "EndOfSequenceOfACMEChallenges" -> ()
      | _ -> ()
      )
    | Success (s_hd, s_tl) -> (
      assert(is_succ2 (dy_split t) s_hd s_tl);
      match parse_acme_challenge s_hd,
            parse_sequence_of_acme_challenges s_tl with
      | Success hd, Success tl ->
        serialize_parse_acme_challenge_publishability_lemma pr trace_index s_hd;
        serialize_parse_sequence_of_acme_challenges_publishability_lemma pr trace_index s_tl;
        assert(LC.is_publishable_p pr trace_index (serialize_acme_challenge hd));
        assert(LC.is_publishable_p pr trace_index (serialize_sequence_of_acme_challenges tl));
        Seq.Properties.lemma_tl hd tl;
        LC.concatenation_of_publishable_bytes_is_publishable_forall pr
      | _ -> ()
      )
#pop-options


#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"
(**
  If bytes (that is an acme_authorization) is publishable, then the bytes resulting from
  first parsing the authorization, and again serializing it, is still publishable.
*)
let serialize_parse_acme_authorization_publishability_lemma
    (pr:LC.preds)
    (trace_index:nat)
    (t:DC.bytes)
  : Lemma
    (requires (
      LC.is_publishable_p pr trace_index t /\
      Success? (parse_acme_authorization t)
    ))
    (ensures (
      LC.is_publishable_p pr trace_index (serialize_acme_authorization (Success?.v (parse_acme_authorization t)))
    ))
  =
    LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split t with
    | Error _ -> ()
    | Success (t1, s_challenges) -> (
      assert(is_succ2 (dy_split t) t1 s_challenges);
      match dy_split t1 with
      | Error _ -> ()
      | Success (s_identifier, s_status) -> (
        assert(is_succ2 (dy_split t1) s_identifier s_status);
        match parse_sequence_of_acme_challenges s_challenges,
              parse_domain s_identifier,
              parse_acme_status s_status with
        | Success challenges, Success identifier, Success status -> (
          if status = Pending ||
             status = Valid ||
             status = Invalid ||
             status = Deactivated ||
             status = Expired ||
             status = Revoked
           then (
             label_of_domain_flows_to_public pr trace_index identifier;
             serialized_acme_status_label_flows_to_public trace_index status;
             assert(LC.is_publishable_p pr trace_index (serialize_acme_status status));
             serialize_parse_sequence_of_acme_challenges_publishability_lemma pr trace_index s_challenges;
             assert(LC.is_publishable_p pr trace_index (serialize_sequence_of_acme_challenges challenges));
             LC.concatenation_of_publishable_bytes_is_publishable_forall pr
           ) else ()
          )
        | _ -> ()
        )
      )


(**
  If bytes (that is an acme_certificate) is publishable, the bytes resulting from first parsing, and
  then again serializing it, is still publishable.
*)
let serialize_parse_acme_certificate_publishablity_lemma
    (pr:LC.preds)
    (trace_index:nat)
    (t:DC.bytes)
  : Lemma
    (requires (
      LC.is_publishable_p pr trace_index t /\
      Success? (parse_acme_certificate t)
    ))
    (ensures (
      let cert = Success?.v (parse_acme_certificate t) in
      LC.is_publishable_p pr trace_index (serialize_acme_certificate cert)
    ))
  =
    LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
    match dy_split t with
    | Success (key_and_identifiers_and_issuer,signature) -> (
      assert(is_succ2 (dy_split t) key_and_identifiers_and_issuer signature);
      match dy_split key_and_identifiers_and_issuer with
      | Success (key_and_identifiers, serialized_issuer) -> (
        assert(is_succ2 (dy_split key_and_identifiers_and_issuer) key_and_identifiers serialized_issuer);
        match dy_split key_and_identifiers with
        | Success (key, serialized_identifiers) -> (
          assert(is_succ2 (dy_split key_and_identifiers) key serialized_identifiers);
          match parse_sequence_of_domains serialized_identifiers with
          | Success identifiers -> if Seq.length identifiers = 0 then () else (
            match parse_domain serialized_issuer with
            | Success issuer ->
              let cert:acme_certificate = {
                acme_certificate_pub_key = key;
                acme_certificate_identifiers = identifiers;
                acme_certificate_issuer = issuer;
                acme_certificate_signature = signature;
              } in
              label_of_domain_flows_to_public pr trace_index issuer;
              serialized_sequence_of_domains_flows_to_public pr trace_index identifiers;
              assert(LC.is_publishable_p pr trace_index key);
              assert(LC.is_publishable_p pr trace_index (serialize_sequence_of_domains identifiers));
              assert(LC.is_publishable_p pr trace_index (serialize_domain issuer));
              assert(LC.is_publishable_p pr trace_index signature);
              LC.concatenation_of_publishable_bytes_is_publishable_forall pr
            )
          )
        )
      )


#push-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"
let acme_order_containing_only_domain_is_publishable trace_index order =
  let status = order.acme_order_status in
  let identifiers = order.acme_order_identifiers in
  let authorizations = order.acme_order_authorizations in
  let finalize_url = order.acme_order_finalize in
  let certificate_url = order.acme_order_certificate in
  serialized_sequence_of_domains_flows_to_public app_preds trace_index identifiers;
  assert(LC.is_publishable_p app_preds trace_index (serialize_sequence_of_domains identifiers));
  LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
  assert(LC.is_publishable_p app_preds trace_index (serialize_acme_order order))
#pop-options


let http_response_is_publishable_implies_acme_order_in_http_response_is_publishable pr trace_index http_resp =
  match parse_acme_order http_resp.resp_body with
  |Success order -> (
    LC.concatenation_publishable_implies_components_publishable_forall pr;
    assert(LC.is_publishable_p pr trace_index http_resp.resp_body);
    serialize_parse_acme_order_publishability_lemma pr trace_index http_resp.resp_body
    )
  |_ -> ()


let http_response_is_publishable_implies_acme_authorization_in_http_response_is_publishable pr trace_index http_resp =
  match parse_acme_authorization http_resp.resp_body with
  |Success authz -> (
    LC.concatenation_publishable_implies_components_publishable_forall pr;
    assert(LC.is_publishable_p pr trace_index http_resp.resp_body);
    serialize_parse_acme_authorization_publishability_lemma pr trace_index http_resp.resp_body;
    assert(acme_authorization_in_http_response_is_publishable pr trace_index http_resp)
    )
  |_ -> ()


let http_response_is_publishable_implies_certificate_of_http_response_is_publishable pr trace_index http_resp =
  LC.concatenation_publishable_implies_components_publishable_forall pr;
  match parse_acme_certificate (http_resp.resp_body) with
   | Error _ -> ()
   | Success certificate ->
     assert(LC.is_publishable_p pr trace_index http_resp.resp_body);
     serialize_parse_acme_certificate_publishablity_lemma pr trace_index http_resp.resp_body;
     assert(certificate_is_publishable pr trace_index certificate)


let elements_of_jws_acme_request_are_publishable_implies_jws_request_is_publishable pr trace_index keyId url replayNonce payload sign_key reader =
  let jws_req = generate_jws_acme_request pr trace_index (APH.acme_sig_key_usage reader pr) keyId url replayNonce payload sign_key (readable_by reader) in
  let ser_jws_req = serialize_jws_acme_request jws_req in
  let signature = generate_signature_for_jws_acme_request pr trace_index (APH.acme_sig_key_usage reader pr) keyId url replayNonce payload sign_key (readable_by reader) in
  assert(LC.is_publishable_p pr trace_index signature);
  LC.concatenation_of_publishable_bytes_is_publishable_forall pr;
  assert(LC.is_publishable_p pr trace_index ser_jws_req)


let authorization_url_of_publishable_acme_order_is_publishable trace_index order _url =
  LC.concatenation_publishable_implies_components_publishable_forall app_preds;
  assert(is_authorization_url_of_acme_order order _url);
  assert(LC.is_publishable_p app_preds trace_index (serialize_acme_order order));
  assert(LC.is_publishable_p app_preds trace_index (serialize_opt_seq_of_urls (order.acme_order_authorizations)));
  let authz_urls = Some?.v order.acme_order_authorizations in
  assert(Seq.contains authz_urls _url);
  let serialized_authz_urls = serialize_sequence_of_urls (Some?.v order.acme_order_authorizations) in
  assert(LC.is_publishable_p app_preds trace_index serialized_authz_urls);
  parsed_sequence_of_urls_contains_only_publishable_urls app_preds trace_index serialized_authz_urls;
  assert(forall authz. Seq.contains authz_urls authz ==> LC.is_publishable_p app_preds trace_index (serialize_url authz));
  assert(LC.is_publishable_p app_preds trace_index (serialize_url _url))


let request_header_host_domain_is_publishable trace_index dom =
  let req_header = generate_request_header_host_domain dom in
  let (host_bytes:DC.bytes) = string_to_bytes "Host" in
  assert(req_header == create 1 (host_bytes, serialize_domain dom));
  label_of_domain_flows_to_public app_preds trace_index dom;
  LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
  Seq.Properties.lemma_contains_singleton (host_bytes, serialize_domain dom);
  assert(forall x. Seq.contains req_header x ==> x == (host_bytes, serialize_domain dom) );
  assert(forall x. Seq.contains req_header x ==> LC.is_publishable_p app_preds trace_index (dy_concat (fst x) (snd x)));
  serialized_sequence_of_bytes_tuples_publishable_if_all_elements_publishable app_preds trace_index req_header

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"
(**
  If bytes (that is a sequence of acme challenges) is publishable, then the parsed sequence contains only
  challenges that are publishable (after serialization).
*)
let rec parsed_sequence_of_acme_challenges_contains_only_publishable_challenges
    (pr:LC.preds)
    (trace_index:nat)
    (t:DC.bytes)
  : Lemma
    (requires (
      LC.is_publishable_p pr trace_index t /\
      Success? (parse_sequence_of_acme_challenges t)
    ))
    (ensures(
      let parsed_sequence = Success?.v (parse_sequence_of_acme_challenges t) in
      forall x. Seq.contains parsed_sequence x ==> LC.is_publishable_p pr trace_index (serialize_acme_challenge x)
    ))
    (decreases (DC.bytes_depth t))
  =
    let parsed_sequence = Success?.v (parse_sequence_of_acme_challenges t) in
    match dy_split t with
    | Error _ -> (
      match DC.bytes_to_string t with
      | Success "EndOfSequenceOfACMEChallenges" -> (
        assert(parsed_sequence == empty);
        Seq.Properties.lemma_contains_empty #acme_challenge
        )
      | _ -> ()
      )
    | Success (hd, tl) -> (
      if Success? (parse_sequence_of_acme_challenges tl) && Success? (parse_acme_challenge hd) then (
        LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
        assert(is_succ2 (dy_split t) hd tl);
        parsed_sequence_of_acme_challenges_contains_only_publishable_challenges pr trace_index tl;
        serialize_parse_acme_challenge_publishability_lemma pr trace_index hd
      ) else ()
      )
#pop-options


let challenge_of_publishable_acme_authorization_is_publishable trace_index authz challenge =
  assert(LC.is_publishable_p app_preds trace_index (serialize_acme_authorization authz));
  LC.concatenation_publishable_implies_components_publishable_forall app_preds;
  let challenges = authz.acme_authorization_challenges in
  let serialized_challenges = serialize_sequence_of_acme_challenges challenges in
  assert(LC.is_publishable_p app_preds trace_index serialized_challenges);
  parsed_sequence_of_acme_challenges_contains_only_publishable_challenges app_preds trace_index serialized_challenges;
  assert(forall c. Seq.contains challenges c ==> LC.is_publishable_p app_preds trace_index (serialize_acme_challenge c))


let url_and_token_of_publishable_challenge_are_publishable trace_index challenge =
  LC.concatenation_publishable_implies_components_publishable_forall app_preds


let acme_order_is_publishable_implies_certificate_url_is_publishable trace_index order =
  LC.concatenation_publishable_implies_components_publishable_forall app_preds


let token_of_publishable_challenge_is_publishable trace_index challenge =
  LC.concatenation_publishable_implies_components_publishable_forall app_preds


let acme_order_is_publishable_implies_finalize_url_is_publishable trace_index order =
  LC.concatenation_publishable_implies_components_publishable_forall app_preds


let csr_is_publishable_with_publishable_public_key trace_index csr =
  LC.concatenation_of_publishable_bytes_is_publishable_forall app_preds;
  serialized_sequence_of_domains_flows_to_public app_preds trace_index csr.acme_csr_identifiers


let parse_acme_csr_publishablity_lemma pr trace_index t =
  LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
  match dy_split t with
  | Success (ser_ids, pub_key) -> (
      assert(is_succ2 (dy_split t) ser_ids pub_key);
      match parse_sequence_of_domains ser_ids with
      | Success ids -> (
        if Seq.length ids = 0 then () else
        let csr:acme_csr = {
          acme_csr_identifiers = ids;
          acme_csr_pub_key = pub_key
        } in
        serialized_sequence_of_domains_flows_to_public pr trace_index ids;
        assert(LC.is_publishable_p pr trace_index pub_key);
        assert(LC.is_publishable_p pr trace_index (serialize_sequence_of_domains ids))
        )
    )


let parse_jws_acme_request_lemma_publishablity pr trace_index t =
 LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
 match DY.Crypto.split t with
 | Success (nonce_bytes, a) ->(
   assert(is_succ2  (DY.Crypto.split t) nonce_bytes a);
   match DY.Crypto.split a with
   | Success (key_id_bytes, b) -> (
    assert(is_succ2  (DY.Crypto.split a) key_id_bytes b);
    match DY.Crypto.split b with
    | Success (url_bytes, c) -> (
      assert(is_succ2  (DY.Crypto.split b) url_bytes c);
      match DY.Crypto.split c with
      | Success (payload, signature) -> (
        assert(is_succ2  (DY.Crypto.split c) payload signature);
        match parse_url url_bytes with
        | Success url_object -> (
          match parse_url key_id_bytes with
          | Success key_id_url -> (
            serialize_parse_url_publishablity_lemma pr trace_index url_bytes;
            serialize_parse_url_publishablity_lemma pr trace_index key_id_bytes
            )
          )
        )
      )
    )
  )


let parse_acme_new_key_inner_jws_lemma_publishablity pr trace_index t =
  LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
  match DC.split t with
  | Success (ser_alg, t1) -> (
    match DC.split t1 with
    | Success (jwk, t2) -> (
      match DC.split t2 with
      | Success (ser_url, t3) -> (
        match DC.split t3 with
        | Success (ser_acc, t4) -> (
          match DC.split t4 with
          | Success (old_key, sig) -> (
            serialize_parse_url_publishablity_lemma pr trace_index ser_url;
            serialize_parse_url_publishablity_lemma pr trace_index ser_acc
          )
        )
      )
    )
  )


#push-options "--z3rlimit 150 --max_fuel 2 --max_ifuel 0"
let serialize_parse_jws_acme_request_publishability_lemma pr trace_index t =
 LC.splittable_bytes_publishable_implies_components_publishable_forall pr;
 match DY.Crypto.split t with
 | Success (nonce_bytes, a) ->
   assert(is_succ2  (DY.Crypto.split t) nonce_bytes a);
   match DC.split a with
   | Success (key_id_bytes, b) ->
      assert(is_succ2 (DC.split a) key_id_bytes b);
      match DC.split b with
      | Success (url_bytes, c) ->
        assert(is_succ2 (DC.split b) url_bytes c);
        match DC.split c with
        | Success (payload, signature) ->
          assert(is_succ2 (DC.split c) payload signature);
          match parse_url url_bytes with
          | Success url_object ->
            match parse_url key_id_bytes with
            | Success key_id_url ->
              let result = { key_id = key_id_url; url = url_object; replay_nonce = nonce_bytes; payload = payload; signature = signature } in
              assert(LC.is_publishable_p pr trace_index payload);
              assert(LC.is_publishable_p pr trace_index signature);
              serialize_parse_url_publishablity_lemma pr trace_index url_bytes;
              serialize_parse_url_publishablity_lemma pr trace_index key_id_bytes;
              assert(LC.is_publishable_p pr trace_index (serialize_url url_object));
              assert(LC.is_publishable_p pr trace_index (serialize_url key_id_url));
              LC.concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options


let http_request_publishable_implies_payload_of_jws_publishable pr trace_index http_req =
  match parse_jws_acme_request http_req.req_body with
  | Error _ -> ()
  | Success jws_acme_request_object -> (
    let payload = jws_acme_request_object.payload in
    LC.concatenation_publishable_implies_components_publishable_forall pr;
    assert(LC.is_publishable_p pr trace_index http_req.req_body);
    parse_jws_acme_request_lemma_publishablity pr trace_index http_req.req_body;
    assert(LC.is_publishable_p pr trace_index payload)
    )


#push-options "--max_fuel 2 --max_ifuel 2"
let authorization_info_is_publishable
  (pr:LC.preds)
  (trace_index:nat)
  (authz_info:authorization_info)
  : Lemma
  (requires True)
  (ensures LC.is_publishable_p pr trace_index (serialize_authorization_info authz_info))
  =
  label_of_domain_flows_to_public pr trace_index authz_info.authz_info_identifier;
  concatenation_of_publishable_bytes_is_publishable_forall pr
#pop-options

let rec sequence_of_authorization_info_is_publishable
  (pr:LC.preds)
  (trace_index:nat)
  (seq_authz_info:Seq.seq authorization_info)
  =
  match Seq.length seq_authz_info with
  | 0 -> ()
  | _ -> (
    concatenation_of_publishable_bytes_is_publishable_forall pr;
    let hd = Seq.head seq_authz_info in
    let tl = Seq.tail seq_authz_info in
    sequence_of_authorization_info_is_publishable pr trace_index tl;
    assert(serialize_sequence_of_authorization_info seq_authz_info == DC.concat (serialize_authorization_info hd) (serialize_sequence_of_authorization_info tl));
    authorization_info_is_publishable pr trace_index hd;
    assert(LC.is_publishable_p pr trace_index (serialize_authorization_info hd))
    )
