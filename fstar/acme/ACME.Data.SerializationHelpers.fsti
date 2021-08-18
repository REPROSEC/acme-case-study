/// ACME.Data.SerializationHelpers
/// ==============================
module ACME.Data.SerializationHelpers

open DY.Trace
open DY.Principals
module DC = DY.Crypto
open Web.Messages
open HelperFunctions

open SerializationHelpers
open Helpers
open DY.Entry

open ACME.Data

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 0"

val serialize_acme_status: (status:acme_status) -> Tot DC.bytes

val parse_acme_status: (t:DC.bytes) -> Tot (result acme_status)

val parse_acme_status_lemma: (s:acme_status)
  -> Lemma (parse_acme_status (serialize_acme_status s) == Success s)
    [SMTPat (parse_acme_status (serialize_acme_status s))]


val serialize_acme_account: (a:acme_account) -> Tot DC.bytes

val parse_acme_account: (t:DC.bytes) -> Tot (result acme_account)

val parse_acme_account_lemma: (a:acme_account)
  -> Lemma (parse_acme_account (serialize_acme_account a) == Success a)
    [SMTPat (parse_acme_account (serialize_acme_account a))]


val serialize_opt_acme_order_status:
  option (s:acme_status{s = Pending \/
                        s = Ready \/
                        s = Processing \/
                        s = Valid \/
                        s = Invalid}) ->
  DC.bytes

val parse_opt_acme_order_status: (t:DC.bytes)
  -> Tot (result (option (s:acme_status{s = Pending \/
                                       s = Ready \/
                                       s = Processing \/
                                       s = Valid \/
                                       s = Invalid})))


val parse_opt_acme_order_status_lemma: (os:option (s:acme_status{s = Pending \/
                                                                 s = Ready \/
                                                                 s = Processing \/
                                                                 s = Valid \/
                                                                 s = Invalid}))
  -> Lemma (parse_opt_acme_order_status (serialize_opt_acme_order_status os) == Success os)
    [SMTPat (parse_opt_acme_order_status (serialize_opt_acme_order_status os))]

val serialize_acme_order: (order:acme_order) -> Tot DC.bytes

val parse_acme_order: (t:DC.bytes) -> Tot (result acme_order)

val parse_acme_order_lemma: (o:acme_order)
  -> Lemma (ensures (parse_acme_order (serialize_acme_order o) == Success o))
    [SMTPat (parse_acme_order (serialize_acme_order o))]

val serialize_acme_challenge_type: (challenge_type:acme_challenge_type) -> Tot DC.bytes

val parse_acme_challenge_type: (t:DC.bytes) -> Tot (result acme_challenge_type)

val parse_acme_challenge_type_lemma: (ct:acme_challenge_type)
  -> Lemma (parse_acme_challenge_type (serialize_acme_challenge_type ct) == Success ct)
    [SMTPat (parse_acme_challenge_type (serialize_acme_challenge_type ct))]


val serialize_acme_challenge: (challenge:acme_challenge) -> Tot DC.bytes


val parse_acme_challenge: (t:DC.bytes) -> Tot (result acme_challenge)

val parse_acme_challenge_lemma: (c:acme_challenge)
  -> Lemma (parse_acme_challenge (serialize_acme_challenge c) == Success c)
    [SMTPat (parse_acme_challenge (serialize_acme_challenge c))]

val serialize_sequence_of_acme_challenges: (challenge_seq:Seq.seq acme_challenge) -> Tot DC.bytes (decreases (Seq.length challenge_seq))

val parse_sequence_of_acme_challenges: (t:DC.bytes) -> Tot (result (Seq.seq acme_challenge)) (decreases (DC.bytes_depth t))

val parse_sequence_of_acme_challenges_lemma: (cs:Seq.seq acme_challenge)
  -> Lemma (ensures (parse_sequence_of_acme_challenges (serialize_sequence_of_acme_challenges cs) == Success cs))
    (decreases (Seq.length cs))
    [SMTPat (parse_sequence_of_acme_challenges (serialize_sequence_of_acme_challenges cs))]


val serialize_acme_authorization: acme_authorization -> DC.bytes

val parse_acme_authorization: DC.bytes -> Tot (result acme_authorization)

val parse_acme_authorization_lemma: (a:acme_authorization) ->
  Lemma (parse_acme_authorization (serialize_acme_authorization a) == Success a)
  [SMTPat (parse_acme_authorization (serialize_acme_authorization a))]


val serialize_acme_certificate: acme_certificate -> DC.bytes

val parse_acme_certificate: DC.bytes -> Tot (result acme_certificate)

val parse_acme_certificate_lemma: (c:acme_certificate) ->
  Lemma (parse_acme_certificate (serialize_acme_certificate c) == Success c)
  [SMTPat (parse_acme_certificate (serialize_acme_certificate c))]


val serialize_acme_csr: acme_csr -> Tot DC.bytes

val parse_acme_csr: DC.bytes -> Tot (result acme_csr)

val parse_acme_csr_lemma:
  acme_csr_object:acme_csr ->
  Lemma (parse_acme_csr (serialize_acme_csr acme_csr_object) == Success acme_csr_object)
  [SMTPat (parse_acme_csr (serialize_acme_csr acme_csr_object))]

val parse_acme_csr_error_if_acme_order:
  order:acme_order ->
  Lemma (Error? (parse_acme_csr (serialize_acme_order order)))

val parse_authorization_info: t:DC.bytes -> Tot (result authorization_info)

val serialize_authorization_info: authorization_info -> Tot DC.bytes

val parse_authorization_info_lemma: (authz_info:authorization_info)
  -> Lemma (ensures (parse_authorization_info (serialize_authorization_info authz_info) == Success authz_info))
    [SMTPat (parse_authorization_info (serialize_authorization_info authz_info))]

val parse_sequence_of_authorization_info: t:DC.bytes -> Tot (result (Seq.seq authorization_info))  (decreases (DC.bytes_depth t))

val serialize_sequence_of_authorization_info: seq_authz_info:Seq.seq authorization_info -> Tot DC.bytes  (decreases (Seq.length seq_authz_info))

val parse_sequence_of_authorization_info_lemma: (seq_authz_info:Seq.seq authorization_info)
  -> Lemma (ensures (parse_sequence_of_authorization_info (serialize_sequence_of_authorization_info seq_authz_info) == Success seq_authz_info))
    (decreases (Seq.length seq_authz_info))
    [SMTPat (parse_sequence_of_authorization_info (serialize_sequence_of_authorization_info seq_authz_info))]



val serialize_acme_server_state: acme_server_state -> session_state

val parse_acme_server_state: session_state -> result acme_server_state

val parse_acme_server_state_lemma:
  acme_server_state_object:acme_server_state ->
  Lemma (
     parse_acme_server_state (serialize_acme_server_state acme_server_state_object) == Success acme_server_state_object /\
     serialize_acme_server_state(Success?.v (parse_acme_server_state (serialize_acme_server_state acme_server_state_object))) == serialize_acme_server_state acme_server_state_object
  )
  [SMTPat (parse_acme_server_state (serialize_acme_server_state acme_server_state_object))]


val serialize_acme_new_key_inner_jws: acme_new_key_inner_jws -> DC.bytes

val parse_acme_new_key_inner_jws: DC.bytes -> result acme_new_key_inner_jws

val parse_acme_new_key_inner_jws_lemma:
  inner_jws:acme_new_key_inner_jws ->
  Lemma (ensures ( parse_acme_new_key_inner_jws (serialize_acme_new_key_inner_jws inner_jws) == Success inner_jws))

val parse_acme_new_key_inner_jws_lemma2:
  t:DC.bytes ->
  Lemma
  (requires ( Success? (parse_acme_new_key_inner_jws t) ))
  (ensures (
    let obj = Success?.v (parse_acme_new_key_inner_jws t) in
    serialize_acme_new_key_inner_jws obj == t
  ))

val serialize_jws_acme_request: jws_acme_request -> DC.bytes

val parse_jws_acme_request: DC.bytes -> result jws_acme_request

val parse_jws_acme_request_lemma:
  request_object:jws_acme_request ->
  Lemma (ensures ( parse_jws_acme_request (serialize_jws_acme_request request_object) == Success request_object))


val serialize_acme_client_state : acme_client_state -> session_state

val parse_acme_client_state: session:session_state -> result acme_client_state

val parse_acme_client_state_lemma: (st:acme_client_state) ->
  Lemma (ensures (
           parse_acme_client_state (serialize_acme_client_state st) == Success st) /\
           serialize_acme_client_state(Success?.v (parse_acme_client_state (serialize_acme_client_state st))) == serialize_acme_client_state st
        )
	[SMTPat (parse_acme_client_state (serialize_acme_client_state st))]


