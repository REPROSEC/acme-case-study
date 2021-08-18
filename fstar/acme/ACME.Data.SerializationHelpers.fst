/// ACME.Data.SerializationHelpers (implementation)
/// ===============================================
module ACME.Data.SerializationHelpers

open DY.Principals
module DC = DY.Crypto
open Web.Messages
open HelperFunctions

open SerializationHelpers
open Helpers

open ACME.Data

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 10"

let serialize_acme_status (status:acme_status) : Tot DC.bytes =
  match status with
  | Pending -> DC.string_to_bytes "Status:Pending"
  | Deactivated -> DC.string_to_bytes "Status:Deactivated"
  | Revoked -> DC.string_to_bytes "Status:Revoked"
  | Valid -> DC.string_to_bytes "Status:Valid"
  | Invalid -> DC.string_to_bytes "Status:Invalid"
  | Ready -> DC.string_to_bytes "Status:Ready"
  | Processing -> DC.string_to_bytes "Status:Processing"
  | Expired -> DC.string_to_bytes "Status:Expired"

let parse_acme_status (t:DC.bytes) : Tot (result acme_status) =
  match DC.bytes_to_string t with
  | Success "Status:Pending" -> Success Pending
  | Success "Status:Deactivated" -> Success Deactivated
  | Success "Status:Revoked" -> Success Revoked
  | Success "Status:Valid" -> Success Valid
  | Success "Status:Invalid" -> Success Invalid
  | Success "Status:Ready" -> Success Ready
  | Success "Status:Processing" -> Success Processing
  | Success "Status:Expired" -> Success Expired
  | _ -> Error "Invalid format"


let parse_acme_status_lemma (s:acme_status)
  : Lemma (parse_acme_status (serialize_acme_status s) == Success s)
    [SMTPat (parse_acme_status (serialize_acme_status s))]
  = ()


let serialize_acme_account (a:acme_account) : Tot DC.bytes =
  serialize_acme_status a.status

let parse_acme_account (t:DC.bytes) : Tot (result acme_account) =
  match parse_acme_status t with
  | Success Valid -> Success ({status = Valid})
  | Success Deactivated -> Success ({status = Deactivated})
  | Success Revoked -> Success ({status = Revoked})
  | _ -> Error "Invalid format"

let parse_acme_account_lemma (a:acme_account)
  : Lemma (parse_acme_account (serialize_acme_account a) == Success a)
    [SMTPat (parse_acme_account (serialize_acme_account a))]
  = ()


let serialize_opt_acme_order_status o_acme_status =
  match o_acme_status with
  | Some status -> serialize_acme_status status
  | None -> DC.string_to_bytes "NoStatus"

#push-options "--max_ifuel 2 --max_fuel 2"
let parse_opt_acme_order_status (t:DC.bytes)
  : Tot (result (option (s:acme_status{s = Pending \/
                                       s = Ready \/
                                       s = Processing \/
                                       s = Valid \/
                                       s = Invalid}))) =
  match DC.bytes_to_string t with
  | Success "NoStatus" -> Success None
  | Success _ -> (
    let parsed_o_status = parse_acme_status t in
    match parsed_o_status with
    | Success Pending
    | Success Ready
    | Success Processing
    | Success Valid
    | Success Invalid -> (
      assert(Success? parsed_o_status);
      let parsed_status = Success?.v parsed_o_status in
      assert(parsed_status = Pending \/ parsed_status = Ready \/ parsed_status = Processing \/ parsed_status = Valid \/ parsed_status = Invalid);
      Success (Some parsed_status)
    )
    | _ -> Error "Invalid format"
  )
  | _ -> Error "Invalid format"
#pop-options


let parse_opt_acme_order_status_lemma (os:option (s:acme_status{s = Pending \/
                                                                s = Ready \/
                                                                s = Processing \/
                                                                s = Valid \/
                                                                s = Invalid}))
  : Lemma (parse_opt_acme_order_status (serialize_opt_acme_order_status os) == Success os)
    [SMTPat (parse_opt_acme_order_status (serialize_opt_acme_order_status os))]
  = ()



let serialize_acme_order (order:acme_order): Tot DC.bytes =
  let status = order.acme_order_status in
  let identifiers = order.acme_order_identifiers in
  let authorizations = order.acme_order_authorizations in
  let finalize = order.acme_order_finalize in
  let certificate = order.acme_order_certificate in
  let serialized_status = serialize_opt_acme_order_status status in
  let serialized_identifiers = serialize_sequence_of_domains identifiers in
  let serialized_authorizations = serialize_opt_seq_of_urls authorizations in
  let serialized_finalize = serialize_opt_url finalize in
  let serialized_certificate = serialize_opt_url certificate in
  DC.concat (DC.concat (DC.concat (DC.concat serialized_status serialized_identifiers) serialized_authorizations) serialized_finalize) serialized_certificate

let parse_acme_order (t:DC.bytes): Tot (result acme_order) =
  match DC.split t with
  | Error e_msg -> Error e_msg
  | Success (t1, s_cert_url) -> (
    match DC.split t1 with
    | Error e_msg -> Error e_msg
    | Success (t2, s_finalize_url) -> (
      match DC.split t2 with
      | Error e_msg -> Error e_msg
      | Success (t3, s_authzs) -> (
        match DC.split t3 with
        | Error e_msg -> Error e_msg
        | Success (s_status, s_domains) -> (
          match parse_opt_url s_cert_url,
                parse_opt_url s_finalize_url,
                parse_opt_seq_of_urls s_authzs,
                parse_opt_acme_order_status s_status,
                parse_sequence_of_domains s_domains with
         | Success cert_url, Success finalize_url, Success authzs, Success status, Success domains -> (
           if Seq.length domains = 0 then Error "Invalid format" else
           let order:acme_order = {
             acme_order_status = status;
             acme_order_identifiers = domains;
             acme_order_authorizations = authzs;
             acme_order_finalize = finalize_url;
             acme_order_certificate = cert_url
           } in
           Success order
         )
         | _ -> Error "Invalid format"
        )
      )
    )
  )

let parse_acme_order_lemma (o:acme_order)
  : Lemma (ensures (parse_acme_order (serialize_acme_order o) == Success o))
    [SMTPat (parse_acme_order (serialize_acme_order o))]
  = ()


(**
    Mapping from challenge_type to bytes.
*)
let serialize_acme_challenge_type (challenge_type:acme_challenge_type): Tot DC.bytes =
  match challenge_type with
  | HTTP01 -> DC.string_to_bytes "ACMECHALLENGETYPE:HTTP01"
  | DNS01 -> DC.string_to_bytes "ACMECHALLENGETYPE:DNS01"

let parse_acme_challenge_type (t:DC.bytes): result acme_challenge_type =
  match DC.bytes_to_string t with
  | Success "ACMECHALLENGETYPE:HTTP01" -> Success HTTP01
  | Success "ACMECHALLENGETYPE:DNS01" -> Success DNS01
  | _ -> Error "Invalid format"

let parse_acme_challenge_type_lemma (ct:acme_challenge_type)
  : Lemma (parse_acme_challenge_type (serialize_acme_challenge_type ct) == Success ct)
    [SMTPat (parse_acme_challenge_type (serialize_acme_challenge_type ct))]
  = ()


let serialize_acme_challenge (challenge:acme_challenge): Tot DC.bytes =
  let challenge_type = challenge.acme_challenge_challenge_type in
  let challenge_url = challenge.acme_challenge_url in
  let challenge_status = challenge.acme_challenge_status in
  let challenge_token = challenge.acme_challenge_token in
  let serialized_challenge_type = serialize_acme_challenge_type challenge_type in
  let serialized_challenge_url = serialize_url challenge_url in
  let serialized_challenge_status = serialize_acme_status challenge_status in
  DC.concat (DC.concat (DC.concat serialized_challenge_type serialized_challenge_url) serialized_challenge_status) challenge_token

let parse_acme_challenge (t:DC.bytes): Tot (result acme_challenge) =
  match DC.split t with
  | Error e_msg -> Error e_msg
  | Success (t1, token) -> (
    match DC.split t1 with
    | Error e_msg -> Error e_msg
    | Success (t2, s_status) -> (
      match DC.split t2 with
      | Error e_msg -> Error e_msg
      | Success (s_type, s_url) -> (
        match parse_acme_status s_status,
              parse_acme_challenge_type s_type,
              parse_url s_url with
        | Success status, Success c_type, Success url -> (
          if not(status = Pending || status = Processing || status = Valid || status = Invalid) then Error "Invalid format" else
          let c:acme_challenge = {
            acme_challenge_challenge_type = c_type;
            acme_challenge_url = url;
            acme_challenge_status = status;
            acme_challenge_token = token
          } in
          Success c
        )
        | _ -> Error "Invalid format"
      )
    )
  )

let parse_acme_challenge_lemma (c:acme_challenge)
  : Lemma (parse_acme_challenge (serialize_acme_challenge c) == Success c)
    [SMTPat (parse_acme_challenge (serialize_acme_challenge c))]
  = ()

let rec serialize_sequence_of_acme_challenges (challenge_seq:Seq.seq acme_challenge): Tot DC.bytes
  (decreases (Seq.length challenge_seq))
  =
    match Seq.length challenge_seq with
    | 0 -> DC.string_to_bytes "EndOfSequenceOfACMEChallenges"
    | _ ->
      let hd = Seq.head challenge_seq in
      let tl = Seq.tail challenge_seq in
      DC.concat (serialize_acme_challenge hd) (serialize_sequence_of_acme_challenges tl)

let rec parse_sequence_of_acme_challenges t =
  match DC.split t with
  | Error e_msg -> (
    match DC.bytes_to_string t with
    | Success "EndOfSequenceOfACMEChallenges" -> Success (Seq.empty)
    | _ -> Error "Invalid format"
  )
  | Success (s_hd, s_tl) -> (
    match parse_acme_challenge s_hd,
          parse_sequence_of_acme_challenges s_tl with
    | Success hd, Success tl -> Success (Seq.cons hd tl)
    | _ -> Error "Invalid format"
  )

#push-options "--max_fuel 1"
let rec parse_sequence_of_acme_challenges_lemma cs =
    match Seq.length cs with
    | 0 -> Seq.Base.lemma_empty cs
    | _ ->
      let tl = Seq.tail cs in
      parse_sequence_of_acme_challenges_lemma tl
#pop-options


let serialize_acme_authorization (authz:acme_authorization) =
  let identifier = authz.acme_authorization_identifier in // a domain
  let status = authz.acme_authorization_status in
  let challenge = authz.acme_authorization_challenges in
  let serialized_identifier = serialize_domain identifier in
  let serialized_status = serialize_acme_status status in
  let serialized_challenges = serialize_sequence_of_acme_challenges challenge in
  DC.concat (DC.concat serialized_identifier serialized_status) serialized_challenges

let parse_acme_authorization (t:DC.bytes) =
  match DC.split t with
  | Error e_msg -> Error e_msg
  | Success (t1, s_challenges) -> (
    match DC.split t1 with
    | Error e_msg -> Error e_msg
    | Success (s_identifier, s_status) -> (
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
           let authz:acme_authorization = {
             acme_authorization_identifier = identifier;
             acme_authorization_status = status;
             acme_authorization_challenges = challenges
           } in
           Success authz
         ) else Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
  )

let parse_acme_authorization_lemma authz = ()


let serialize_acme_certificate cert =
  let serialized_identifiers = serialize_sequence_of_domains (cert.acme_certificate_identifiers) in
  let serialized_issuer = serialize_domain (cert.acme_certificate_issuer) in
  (DC.concat
     (DC.concat
       (DC.concat
         cert.acme_certificate_pub_key
         serialized_identifiers)
       serialized_issuer)
     cert.acme_certificate_signature)

let parse_acme_certificate t =
  match DC.split t with
  | Error e_msg -> Error e_msg
  | Success (key_and_identifiers_and_issuer,signature) -> (
    match DC.split key_and_identifiers_and_issuer with
    | Error e_msg -> Error e_msg
    | Success (key_and_identifiers, serialized_issuer) -> (
      match DC.split key_and_identifiers with
      | Error e_msg -> Error e_msg
      | Success (key, serialized_identifiers) -> (
        match parse_sequence_of_domains serialized_identifiers with
        | Success identifiers -> if Seq.length identifiers = 0 then Error "Invalid format" else (
          match parse_domain serialized_issuer with
          | Success issuer ->
            let cert:acme_certificate = {
              acme_certificate_pub_key = key;
              acme_certificate_identifiers = identifiers;
              acme_certificate_issuer = issuer;
              acme_certificate_signature = signature;
            } in
            Success cert
          | _ -> Error "Invalid format"
          )
        | _ -> Error "Invalid format"
      )
    )
  )

let parse_acme_certificate_lemma cert = ()


let serialize_acme_csr acme_csr =
  let serialized_identifiers = serialize_sequence_of_domains acme_csr.acme_csr_identifiers in
  DC.concat serialized_identifiers acme_csr.acme_csr_pub_key

let parse_acme_csr t =
  match DC.split t with
  | Error e_msg -> Error e_msg
  | Success (ser_ids, pub_key) -> (
      match parse_sequence_of_domains ser_ids with
      | Error e_msg -> Error e_msg
      | Success ids -> (
        if Seq.length ids = 0 then Error "Invalid format" else
        let csr:acme_csr = {
          acme_csr_identifiers = ids;
          acme_csr_pub_key = pub_key
        } in
        Success csr
        )
    )

let parse_acme_csr_lemma csr = ()


#push-options "--max_fuel 2 --max_ifuel 0 --z3rlimit 150"
let parse_acme_csr_error_if_acme_order order = ()
#pop-options


let parse_authorization_info t =
   match DC.split t with
  | Error e_msg -> Error e_msg
  | Success (dom_bytes, status_bytes) -> (
      match parse_domain dom_bytes, parse_acme_status status_bytes with
      | Success dom, Success status -> (
        let authz_info:authorization_info = {
          authz_info_identifier = dom;
          authz_info_status = status
        } in
        Success authz_info
        )
      | _ -> Error "Invalid format"
    )

let serialize_authorization_info authz_info =
  let status = authz_info.authz_info_status in
  let identifier = authz_info.authz_info_identifier in
  let serialized_status = serialize_acme_status status in
  let serialized_identifier = serialize_domain identifier in
  DC.concat serialized_identifier serialized_status

let parse_authorization_info_lemma authz_info = ()


let rec parse_sequence_of_authorization_info t =
   match DC.split t with
  | Error e_msg -> (
    match DC.bytes_to_string t with
    | Success "EndOfSequenceOfAuthorizationInfo" -> Success (Seq.empty)
    | _ -> Error "Invalid format"
  )
  | Success (s_hd, s_tl) -> (
    match parse_authorization_info s_hd,
          parse_sequence_of_authorization_info s_tl with
    | Success hd, Success tl -> Success (Seq.cons hd tl)
    | _ -> Error "Invalid format"
  )

let rec serialize_sequence_of_authorization_info seq_authz_info =
    match Seq.length seq_authz_info with
    | 0 -> DC.string_to_bytes "EndOfSequenceOfAuthorizationInfo"
    | _ ->
      let hd = Seq.head seq_authz_info in
      let tl = Seq.tail seq_authz_info in
      DC.concat (serialize_authorization_info hd) (serialize_sequence_of_authorization_info tl)

#push-options "--max_fuel 1"
let rec parse_sequence_of_authorization_info_lemma seq_authz_info =
  match Seq.length seq_authz_info with
    | 0 -> Seq.Base.lemma_empty seq_authz_info
    | _ ->
      let tl = Seq.tail seq_authz_info in
      parse_sequence_of_authorization_info_lemma tl
#pop-options


let serialize_acme_server_state_inner (acme_server_st:acme_server_state) (str:string) : Tot (option DC.bytes) =
  if str = "principal_type" then Some (DC.string_to_bytes "acme_server") else
  match acme_server_st with
   | IssuedValidNonce n ->
     if str = "session_type" then
       Some (DC.string_to_bytes "IssuedValidNonce")
     else
     if str = "nonce" then
       Some n
     else None
   | UserAccount account public_key account_url ->
     if str = "session_type" then
       Some (DC.string_to_bytes "UserAccount")
     else
     if str = "account" then
       Some (serialize_acme_account account)
     else
     if str = "public_key" then
       Some public_key
     else
     if str = "account_url" then
       Some (serialize_url account_url)
     else None
   | Order order user_account_sessionid acc_url acc_pub_key seq_authz_info ->
     if str = "session_type" then
       Some (DC.string_to_bytes "Order")
     else
     if str = "order" then
       Some (serialize_acme_order order)
     else
     if str = "user_account_sessionid" then
       Some (DC.nat_to_bytes user_account_sessionid)
     else
     if str = "acc_pub_key" then
       Some acc_pub_key
     else
     if str = "acc_url" then
       Some (serialize_url acc_url)
     else if str = "seq_authz_info" then
       Some (serialize_sequence_of_authorization_info seq_authz_info)
     else None
   | Authorization authorization_url authorization order_sessionid  ->
     if str = "session_type" then
       Some (DC.string_to_bytes "Authorization")
     else
     if str = "authorization_url" then
       Some (serialize_url authorization_url)
     else
     if str = "authorization" then
       Some (serialize_acme_authorization authorization)
     else
     if str = "order_sessionid" then
       Some (DC.nat_to_bytes order_sessionid)
     else None
   | PrivateCAKey k ->
     if str = "session_type" then
       Some(DC.string_to_bytes "PrivateCAKey")
     else
     if str = "private_ca_key" then
       Some k
     else None
   | Certificate set_state_idx cert certificate_url account_public_key ->
     if str = "session_type" then
       Some(DC.string_to_bytes "Certificate")
     else if str = "certificate" then
       Some(serialize_acme_certificate cert)
     else if str = "certificate_url" then
       Some(serialize_url certificate_url)
     else if str = "set_state_idx" then
       Some(DC.nat_to_bytes set_state_idx)
     else
     if str = "account_public_key" then
       Some account_public_key
     else None
   | ProcessingChallenge authorization_sessionid challenge_idx http_request_id ->
     if str = "session_type" then
       Some(DC.string_to_bytes "ProcessingChallenge")
     else if str = "authorization_sessionid" then
       Some (DC.nat_to_bytes authorization_sessionid)
     else if str = "challenge_idx" then
       Some (DC.nat_to_bytes challenge_idx)
     else if str = "http_request_id" then
       Some http_request_id
     else None


let serialize_acme_server_state (acme_server_st:acme_server_state): Tot session_state =
  let fields_to_be_printed:list string = (
    match acme_server_st with
    | UserAccount _ _ _ -> ["public_key"; "account_url"]
    | Order _ _ _ _ _ -> ["order"; "user_account_sessionid"; "acc_pub_key"; "acc_url"; "seq_authz_info"]
    | Authorization _ _ _ -> ["authorization_url"; "order_sessionid"]
    | PrivateCAKey _ -> ["private_ca_key"]
    | Certificate _ _ _ _ -> ["certificate"; "certificate_url"; "set_state_idx"]
    | ProcessingChallenge _ _ _ -> ["authorization_sessionid"; "challenge_idx"; "http_request_id"]
    | _ -> []
  ) in
  (["principal_type"; "session_type"] @ fields_to_be_printed, serialize_acme_server_state_inner acme_server_st)


let parse_acme_server_state state =
  let (_, st) = state in
  match str (st "principal_type") with
  | Some "acme_server" -> (
    match str (st "session_type") with
    | Some "IssuedValidNonce" -> (
      match st "nonce" with
      | None -> Error "Invalid format"
      | Some n -> Success (IssuedValidNonce n)
    )
    | Some "UserAccount" -> (
      match st "account", st "public_key", st "account_url" with
      | Some s_acc, Some pubkey, Some s_acc_url -> (
        match parse_acme_account s_acc, parse_url s_acc_url with
        | Success acc, Success acc_url -> Success (UserAccount acc pubkey acc_url)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "Order" -> (
      match st "order", st "user_account_sessionid", st "acc_pub_key", st "seq_authz_info", st "acc_url"  with
      | Some s_order, Some sess_id_bytes, Some acc_pub_key, Some seq_authz_info_bytes, Some acc_url_bytes -> (
        match parse_acme_order s_order,
              DC.bytes_to_nat sess_id_bytes,
              parse_sequence_of_authorization_info seq_authz_info_bytes,
              parse_url acc_url_bytes with
        | Success order, Success sess_id, Success seq_authz_info, Success acc_url -> Success (Order order sess_id acc_url acc_pub_key seq_authz_info)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "Authorization" -> (
      match st "authorization_url", st "authorization", st "order_sessionid" with
      | Some s_authz_url, Some s_authz, Some sess_id_bytes -> (
        match parse_url s_authz_url,
              parse_acme_authorization s_authz,
              DC.bytes_to_nat sess_id_bytes with
        | Success authz_url, Success authz, Success sess_id -> Success (Authorization authz_url authz sess_id)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "PrivateCAKey" -> (
      match st "private_ca_key" with
      | Some key -> Success (PrivateCAKey key)
      | None -> Error "Invalid format"
    )
    | Some "Certificate" -> (
      match st "certificate", st "certificate_url", st "set_state_idx", st "account_public_key" with
      | Some s_cert, Some s_cert_url, Some set_state_idx_bytes, Some acc_pub_key -> (
        match parse_acme_certificate s_cert, parse_url s_cert_url, DC.bytes_to_nat set_state_idx_bytes with
        | Success cert, Success cert_url, Success set_state_idx -> Success (Certificate set_state_idx cert cert_url acc_pub_key)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "ProcessingChallenge" -> (
      match st "authorization_sessionid", st "challenge_idx", st "http_request_id" with
      | Some sess_id_bytes, Some chall_idx_bytes, Some req_id -> (
        match DC.bytes_to_nat sess_id_bytes, DC.bytes_to_nat chall_idx_bytes with
        | Success sess_id, Success chall_idx -> Success (ProcessingChallenge sess_id chall_idx req_id)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | _ -> Error "Invalid format"
  )
  | _ -> Error "Invalid format"


let parse_acme_server_state_lemma st = ()



let serialize_acme_new_key_inner_jws input_object =
  DC.concat (DC.string_to_bytes input_object.alg) (
    DC.concat input_object.jwk (
      DC.concat (serialize_url input_object.inner_url) (
        DC.concat (serialize_url input_object.inner_payload_account) (
          DC.concat input_object.inner_payload_old_key input_object.inner_signature
        )
      )
    )
  )

let parse_acme_new_key_inner_jws input_bytes =
  match DC.split input_bytes with
  | Error e -> Error e
  | Success (ser_alg, t1) -> (
    match DC.split t1 with
    | Error e -> Error e
    | Success (jwk, t2) -> (
      match DC.split t2 with
      | Error e -> Error e
      | Success (ser_url, t3) -> (
        match DC.split t3 with
        | Error e -> Error e
        | Success (ser_acc, t4) -> (
          match DC.split t4 with
          | Error e -> Error e
          | Success (old_key, sig) -> (
            match
              DC.bytes_to_string ser_alg,
              parse_url ser_url,
              parse_url ser_acc
            with
            | Success alg, Success url, Success acc -> (
              let obj:acme_new_key_inner_jws = {
                alg = alg;
                jwk = jwk;
                inner_url = url;
                inner_payload_account = acc;
                inner_payload_old_key = old_key;
                inner_signature = sig
              } in
              Success obj
            )
            | _ -> Error "Wrong format of acme_new_key_inner_jws"
          )
        )
      )
    )
  )

let parse_acme_new_key_inner_jws_lemma obj = ()

let parse_acme_new_key_inner_jws_lemma2 t =
  let Success (ser_alg, t1) = DC.split t in
  let Success (jwk, t2) = DC.split t1 in
  let Success (ser_url, t3) = DC.split t2 in
  let Success (ser_acc, t4) = DC.split t3 in
  let Success (old_key, sig) = DC.split t4 in
  parse_url_lemma2 ser_url;
  parse_url_lemma2 ser_acc


let serialize_jws_acme_request input_object =
  DC.concat input_object.replay_nonce  (DC.concat (serialize_url input_object.key_id) (DC.concat (serialize_url input_object.url) (DC.concat input_object.payload input_object.signature))) (* ) *)

let parse_jws_acme_request input_bytes =
  match DC.split input_bytes with
  | Error e_msg -> Error e_msg
  | Success (nonce_bytes, a) -> (
     match DC.split a with
     | Error e_msg -> Error e_msg
     | Success (key_id_bytes, b) ->
      match DC.split b with
      | Error e_msg -> Error e_msg
      | Success (url_bytes, c) ->
        match DC.split c with
        | Error e_msg -> Error e_msg
        | Success (payload, signature) ->
          match parse_url url_bytes with
          | Error e_msg -> Error e_msg
          | Success url_object ->
            match parse_url key_id_bytes with
            | Error e_msg -> Error e_msg
            | Success key_id_url ->
              let result = { key_id = key_id_url; replay_nonce = nonce_bytes; url = url_object; payload = payload; signature = signature } in
              Success result
   )
let parse_jws_acme_request_lemma request_object = ()




let serialize_acme_client_state_inner client_state str =
 if str = "principal_type" then Some (DC.string_to_bytes "acme_client") else
  (match client_state with
  | Account private_key account_url order_url ->
    if str = "session_type" then
      Some(DC.string_to_bytes "Account")
    else if str = "private_key" then
      Some private_key
    else if str = "account_url" then
       Some (serialize_url account_url)
    else if str = "order_url" then
       Some (serialize_url order_url)
    else None
  | HTTPSPendingRequest request_nonce  reference_sessionid serv_dom ->
    if str = "session_type" then
      Some(DC.string_to_bytes "HTTPSPendingRequest")
    else if str = "request_nonce" then
      Some  request_nonce
    else if str = "reference_sessionid" then
      Some  (DC.nat_to_bytes reference_sessionid)
   else if str = "server_domain" then
      Some (serialize_domain serv_dom)
    else None
  | ACMEOrder acme_order_object account_sessionid opt_current_order_url ->
    if str = "session_type" then
      Some (DC.string_to_bytes "ACMEOrder")
    else if str = "acme_order_object" then
      Some (serialize_acme_order acme_order_object)
    else if str = "account_sessionid" then
      Some  (DC.nat_to_bytes account_sessionid)
    else if str = "opt_current_order_url" then
      Some  (serialize_opt_url opt_current_order_url)
    else None
  | ACMEAuthorziation acme_authorization_object acme_order_sessionid ->
    if str = "session_type" then
      Some (DC.string_to_bytes "ACMEAuthorziation")
    else if str = "acme_authorization_object" then
       Some (serialize_acme_authorization acme_authorization_object)
    else if str = "acme_order_sessionid" then
      Some (DC.nat_to_bytes acme_order_sessionid)
    else None
  | CSR priv_cert_key identifiers acme_authz_sessionid csr_set_state_idx ->
    if str = "session_type" then
      Some (DC.string_to_bytes "CSR")
    else if str = "certificate_private_key" then
       Some priv_cert_key
    else if str = "acme_authorization_sessionid" then
      Some (DC.nat_to_bytes acme_authz_sessionid)
    else if str = "identifers" then
      Some (serialize_sequence_of_domains identifiers)
    else if str = "csr_set_state_idx" then
      Some (DC.nat_to_bytes csr_set_state_idx)
    else None
  |  RetrieveCertificate csr_sessionid ->
    if str = "session_type" then
      Some(DC.string_to_bytes "RetrieveCertificate")
    else if str = "csr_sessionid" then
      Some (DC.nat_to_bytes csr_sessionid)
    else None
  | ReceivedCertificate certificate retrieve_cert_sessionid tr_idx ->
     if str = "session_type" then
      Some(DC.string_to_bytes "ReceivedCertificate")
    else if str = "retrieve_cert_sessionid" then
      Some (DC.nat_to_bytes retrieve_cert_sessionid)
    else if str = "certificate" then
      Some (serialize_acme_certificate certificate)
    else if str = "trace_idx" then
      Some (DC.nat_to_bytes tr_idx)
    else None
  | ChallengeResponse authz_sessionid request_id ->
     if str = "session_type" then
      Some(DC.string_to_bytes "ChallengeResponse")
    else if str = "authz_sessionid" then
      Some (DC.nat_to_bytes authz_sessionid)
    else if str = "request_id" then
      Some request_id
    else None
  | ReplayNonce nonce valid serv_dom ->
    if str = "session_type" then
      Some(DC.string_to_bytes "ReplayNonce")
    else if str = "replay_nonce" then
      Some (nonce)
    else if str = "valid" then
      Some (DC.literal_to_bytes (DC.Bool valid))
    else if str = "server_domain" then
      Some (serialize_domain serv_dom)
    else None
  | ReplayNonceRequest serv_dom ->
    if str = "session_type" then
      Some(DC.string_to_bytes "ReplayNonceRequest")
    else if str = "server_domain" then
      Some (serialize_domain serv_dom)
    else None
  )
  


let serialize_acme_client_state (cs:acme_client_state): Tot session_state =
  let fields_to_be_printed:list string = (
    match cs with
    | Account _ _ _ -> ["private_key"; "account_url"; "order_url"]
    | HTTPSPendingRequest _ _ _ -> ["request_nonce"; "reference_sessionid"; "server_domain"]
    | ACMEOrder _ _ _ -> ["acme_order_object"; "account_sessionid"; "opt_current_order_url"]
    | ACMEAuthorziation _ _ -> ["acme_authorization_object"; "acme_order_sessionid"]
    | CSR _ _ _ _ -> ["certificate_private_key"; "acme_authorization_sessionid"; "identifers"; "csr_set_state_idx"]
    | RetrieveCertificate _ -> ["csr_sessionid"]
    | ReceivedCertificate _ _ _ -> ["retrieve_cert_sessionid"; "certificate"; "trace_idx"]
    | ChallengeResponse _ _ -> ["authz_sessionid"; "request_id"]
    | ReplayNonce _ _ _ -> ["replay_nonce"; "valid"; "server_domain"]
    | ReplayNonceRequest _ -> ["server_domain"]
  ) in
  (["principal_type"; "session_type"] @ fields_to_be_printed,
    serialize_acme_client_state_inner cs)


let parse_acme_client_state state =
  let ct = snd state in
  match str (ct "principal_type") with
  | Some "acme_client" -> (
    match str (ct "session_type") with
    | Some "Account" -> (
      match ct "account_url", ct "order_url", ct "private_key" with
      | Some s_acc_url, Some s_order_url, Some privk -> (
        match parse_url s_acc_url, parse_url s_order_url with
        | Success acc_url, Success order_url -> Success (Account privk acc_url order_url)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "HTTPSPendingRequest" -> (
      match ct "request_nonce", ct "reference_sessionid", ct "server_domain" with
      | Some req_n,  Some sess_id_bytes, Some serv_dom_bytes -> (
        match DC.bytes_to_nat sess_id_bytes, parse_domain serv_dom_bytes with
        | Success sess_id, Success serv_dom -> Success (HTTPSPendingRequest req_n sess_id serv_dom)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "ACMEOrder" -> (
      match ct "acme_order_object", ct "account_sessionid", ct "opt_current_order_url"  with
      | Some s_order, Some acc_ssid_bytes, Some opt_url_bytes -> (
        match parse_acme_order s_order, DC.bytes_to_nat acc_ssid_bytes, parse_opt_url opt_url_bytes with
        | Success order, Success acc_ssid, Success opt_url -> Success (ACMEOrder order acc_ssid opt_url)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "ACMEAuthorziation" -> (
      match ct "acme_authorization_object", ct "acme_order_sessionid" with
      | Some s_authz, Some sess_id_bytes -> (
        match parse_acme_authorization s_authz,
              DC.bytes_to_nat sess_id_bytes with
        | Success authz, Success sess_id -> Success (ACMEAuthorziation authz sess_id)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "CSR" -> (
      match ct "certificate_private_key", ct "acme_authorization_sessionid", ct "identifers", ct "csr_set_state_idx" with
      | Some cert_priv_key, Some authz_sessionid_bytes, Some identifiers_bytes, Some csr_set_state_idx_bytes -> (
        match DC.bytes_to_nat authz_sessionid_bytes, parse_sequence_of_domains identifiers_bytes, DC.bytes_to_nat csr_set_state_idx_bytes with
        | Success sess_id, Success identifiers, Success csr_set_state_idx -> Success (CSR cert_priv_key identifiers sess_id csr_set_state_idx)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "RetrieveCertificate" -> (
      match ct "csr_sessionid" with
      | Some csr_sessionid_bytes -> (
        match DC.bytes_to_nat csr_sessionid_bytes with
        | Success csr_sessionid -> Success (RetrieveCertificate csr_sessionid)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "ReceivedCertificate" -> (
      match ct "certificate", ct "retrieve_cert_sessionid", ct "trace_idx" with
      | Some certificate_bytes, Some retrieve_cert_sessionid_bytes, Some tr_idx_bytes ->(
        match parse_acme_certificate certificate_bytes, DC.bytes_to_nat retrieve_cert_sessionid_bytes, DC.bytes_to_nat tr_idx_bytes with
        | Success certificate, Success retrieve_cert_sessionid, Success tr_idx -> Success (ReceivedCertificate certificate retrieve_cert_sessionid tr_idx)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "ChallengeResponse" -> (
      match ct "authz_sessionid", ct "request_id" with
      | Some authz_sessionid_bytes, Some request_id -> (
        match DC.bytes_to_nat authz_sessionid_bytes with
        | Success authz_sessionid -> Success (ChallengeResponse authz_sessionid request_id)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "ReplayNonce" -> (
      match ct "replay_nonce", ct "valid", ct "server_domain" with
      | Some replay_nonce_bytes, Some valid_bytes, Some serv_dom_bytes -> (
        match DC.bytes_to_literal valid_bytes, parse_domain serv_dom_bytes with
        | Success (DC.Bool b), Success serv_dom -> Success (ReplayNonce replay_nonce_bytes b serv_dom)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | Some "ReplayNonceRequest" -> (
      match ct "server_domain" with
      | Some serv_dom_bytes -> (
        match parse_domain serv_dom_bytes with
        | Success serv_dom -> Success (ReplayNonceRequest serv_dom)
        | _ -> Error "Invalid format"
      )
      | _ -> Error "Invalid format"
    )
    | _ -> Error "Invalid format"
  )
  | _ -> Error "Invalid format"


let parse_acme_client_state_lemma (st:acme_client_state) :
  Lemma (ensures (parse_acme_client_state (serialize_acme_client_state st) == Success st))
  [SMTPat (parse_acme_client_state (serialize_acme_client_state st))]
  =
  match st with
  | Account _ _ _ -> ()
  | HTTPSPendingRequest _  _ _ -> ()
  | ACMEOrder _ _ _ -> ()
  | ACMEAuthorziation _ _ -> ()
  | CSR _ _ _ _ -> ()
  | RetrieveCertificate  _ -> ()
  | ReceivedCertificate _ _ _ -> ()
  | ChallengeResponse _ _ -> ()
  | ReplayNonce _ _ _ -> ()
  | ReplayNonceRequest _ -> ()
  


