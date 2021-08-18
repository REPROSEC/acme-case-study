/// ACME.Test (implementation)
/// ==============================
module ACME.Test

open DY.Monad
open DY.Entry
open DY.Labels
open DY.Principals
open DY.Crypto
open DY.Trace
open DY.AttackerAPI
open Helpers
open Labeled.Crypto
open Labeled.ApplicationAPI
open Web.Messages
open ACME.Data
open ACME.Client
open ACME.Server
open ACME.Test.Init
open Application.Predicates
friend Application.Predicates
open ACME.Data.SerializationHelpers
open SerializationHelpers
open SerializationLemmas
open HelperFunctions


#set-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"

(*! Helper functions for testing*)
(**
when the client receives an acme authorization object from the server,
he tries to send http requests to trigger ALL challenge verifications given in the authorization
*)

val client_server_trigger_all_challenges_nw:
  client: principal ->
  server: principal ->
  serv_dom: domain ->
  client_authz_sessionid: nat ->
  num_of_challenges: nat ->
  challenge_idx: nat ->
  DYL unit
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)
  (decreases (num_of_challenges - challenge_idx))

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let rec client_server_trigger_all_challenges_nw client server serv_dom client_authz_sessionid num_of_challenges challenge_idx  =
  if challenge_idx < num_of_challenges then(
    print_string "step 5: client triggers challenge verification\n";
    let len_now = current_trace_len () in
    let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
    let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
    let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
    let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
    let msg_idx = acme_client_triggers_challenge_i_nw client client_authz_sessionid challenge_idx in
    print_string "step 6: server replies OK message\n";
    let _ = acme_server_challenge_response_nw server msg_idx in
    client_server_trigger_all_challenges_nw client server serv_dom client_authz_sessionid num_of_challenges (challenge_idx + 1)
  ) else ()

(**
 when the client receive and updated acme order object from the server, the two begins to process all necessary authorization:
   - client sends authorization request to each authorization url stored in updated acme order
   - server receives the request and replies an http response contaning an acme authorization object
   - client receives the authorization objects then trigger all challenges of the received authorizations
*)

val client_server_process_all_authorizations_nw:
  client: principal ->
  server: principal ->
  serv_dom: domain ->
  client_order_sessionid: nat ->
  num_of_authorization_urls:nat ->
  authz_url_idx: nat ->
  DYL unit
  (requires fun h -> valid_trace h)
  (ensures fun h0 _ h1 -> valid_trace h1)
  (decreases (num_of_authorization_urls -  authz_url_idx))

let rec client_server_process_all_authorizations_nw client server serv_dom client_order_sessionid num_of_authorization_urls authz_url_idx =
  if authz_url_idx < num_of_authorization_urls then (
    let len_now = current_trace_len () in
    let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
    let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
    let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
    let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
    let authz_req_idx = acme_client_send_authorization_request_i_nw client client_order_sessionid authz_url_idx in
    print_string "step 3: client sends authorization request \n" ;
    let authz_resp_idx = acme_server_identifier_authz_nw server authz_req_idx in
    print_string "step 4: server sends authorization object\n";
    let (client_authz_sessionid, num_of_challenges) = acme_client_receive_authorization_response_nw client authz_resp_idx in
    //client and server start to trigger all challenge verifications
    print_string "step 5: client receives authorization object\n";
    client_server_trigger_all_challenges_nw client server serv_dom client_authz_sessionid num_of_challenges 0;
    client_server_process_all_authorizations_nw client server serv_dom client_order_sessionid num_of_authorization_urls (authz_url_idx + 1)
  ) else ()



val server_client_verify_all_challenges_nw:
  server: principal ->
  client: principal ->
  num_of_challenges: nat ->
  idx:nat ->
  DYL unit
  (requires fun h -> valid_trace h)
  (ensures fun h0 _ h1 -> valid_trace h1)
  (decreases (num_of_challenges - idx))

let rec server_client_verify_all_challenges_nw server client num_of_challenges idx =
  if idx < num_of_challenges then (
    let challenge_req_idx = acme_server_trigger_challenge_verification_nw server in
    print_string "step 7: server send verification request\n";
    let challenge_resp_idx = acme_client_challenge_response_nw client challenge_req_idx in
    print_string "step 8: client send response for verification request\n";
    acme_server_receive_challenge_verification_nw server challenge_resp_idx;
    server_client_verify_all_challenges_nw server client num_of_challenges (idx+1)
  ) else ()

(**
attack version where FAULTY function (acme_server_receive_challenge_verification_nw_faulty) is used
*)

val server_client_verify_all_challenges_nw_faulty_inner:
  server: principal ->
  client: principal ->
  DYL nat
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let server_client_verify_all_challenges_nw_faulty_inner server client  =
    let challenge_req_idx = acme_server_trigger_challenge_verification_nw server in
    print_string "step 7: server send verification request\n";
    let challenge_resp_idx = acme_client_challenge_response_nw client challenge_req_idx in
    challenge_resp_idx
   

val server_client_verify_all_challenges_nw_faulty:
  server: principal ->
  client: principal ->
  num_of_challenges: nat ->
  idx:nat ->
  DYL unit
  (requires fun h -> valid_trace h)
  (ensures fun h0 _ h1 -> valid_trace h1)
  (decreases (num_of_challenges - idx))

#push-options "--max_ifuel 1"
let rec server_client_verify_all_challenges_nw_faulty server client num_of_challenges idx =
  if  idx < num_of_challenges then (
    let t = get () in
    let r, t' = reify (server_client_verify_all_challenges_nw_faulty_inner server client) t in
    //let r: result nat = r in
    put t';
    match r with
    | Success challenge_resp_idx ->          
       print_string "step 8: client send response for verification request\n";  
       let now = current_trace_len () in
       print_bytes (nat_to_bytes now);
       print_string "\n";
       print_bytes (nat_to_bytes challenge_resp_idx);
       //print_trace ();
       acme_server_receive_challenge_verification_nw_faulty server challenge_resp_idx;
       server_client_verify_all_challenges_nw_faulty server client num_of_challenges (idx+1)
       //print_trace ()
    | Error _ -> 
       //print_trace ();
       server_client_verify_all_challenges_nw_faulty server client num_of_challenges (idx+1)
       //print_trace ()
  ) else ()
#pop-options

(*
let rec server_client_verify_all_challenges_nw_faulty server client num_of_challenges idx =
  if  idx < num_of_challenges then (
    let challenge_req_idx = acme_server_trigger_challenge_verification_nw server in
    print_string "step 7: server send verification request\n";
    let challenge_resp_idx = acme_client_challenge_response_nw client challenge_req_idx in
    print_string "step 8: client send response for verification request\n";
    acme_server_receive_challenge_verification_nw_faulty server challenge_resp_idx;
    server_client_verify_all_challenges_nw_faulty server client num_of_challenges (idx+1)
  ) else ()
*)
(*! Test cases*)



(**
test 1: single domain, with network, client owns the domain
client asks the certificate for one domain owned by himself
This test passes iff the protocol run completetly, i.e.,
the string "PROTOCOL RUN (SUCCESS for jenkins): ACME regular run" is printed out
*)
val acme_test_1: unit -> DY unit
 (requires fun h -> valid_trace h)
 (ensures fun h0 _ h1 -> valid_trace h1)

let acme_test_1 _ =
  let client:principal = "client" in
  let server:principal = "server" in
  let serv_dom:domain = Root "server" in
  let client_dom:domain = Root "client" in
  domain_principal_mapping_lemma serv_dom;
  domain_principal_mapping_lemma client_dom;
  let i = current_trace_len () in
  let account_url = gen_publishable_url i serv_dom ["client"; "account1"] in
  let order_url = gen_publishable_url i serv_dom ["client"; "order-cert"] in
  let (client_acc_sessionid, server_acc_sessionid) = gen_account client server account_url order_url in
  let server_ca_privkey_sessionid = gen_private_ca_key server in
  let client_seq_doms = Seq.create 1 client_dom in
  //start protocol
  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in

  let client_order_idx = acme_client_orders_certificate_nw client client_seq_doms client_acc_sessionid in
  print_string "step 1\n";
  let server_order_idx = acme_server_new_order_nw server client_order_idx in
  print_string "step 2\n";  
  let (client_order_sessionid, num_of_authorization_urls) = acme_client_receive_order_response_nw client server_order_idx in
  print_string "step 3: client receives order response\n";
  client_server_process_all_authorizations_nw client server serv_dom client_order_sessionid num_of_authorization_urls 0;
  let server_challenge_idx = acme_server_trigger_challenge_verification_nw server in
  print_string "step 7\n";
  let client_challenge_resp_idx = acme_client_challenge_response_nw client server_challenge_idx in
  print_string "step 8\n";
  acme_server_receive_challenge_verification_nw server client_challenge_resp_idx;

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in

  let client_sendCSR_idx = acme_client_sends_CSR_nw client client_order_sessionid in
  print_string "step 9\n";
  let server_retriev_cert_idx = acme_server_finalize_order_nw server client_sendCSR_idx in
  print_string "step 10\n";

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
  (* The FStar server always responds with a Valid order. Therefore, we ignore the polling flag here. *)
  let (client_get_cert_idx,_) = acme_client_retrieves_certificate_nw client server_retriev_cert_idx in
  print_string "step 11\n";
  let server_cert_idx = acme_server_retrieve_cert_nw server client_get_cert_idx in
  print_string "step 12\n";
  let cert_sessionid = acme_client_receives_and_saves_certificate_nw client server_cert_idx in
  // Do NOT! change the following line! This string is matched by Jenkins to assure that the functional test still works as expected.
  print_string "PROTOCOL RUN (SUCCESS for jenkins): ACME regular run with network\n";
  () //protocol is done



(**
test 2: single domain, with network, client does not own the domain
client asks the certificate for one domain owned by himself
This test passes iff the protocol stops at step 7
*)
val acme_test_2_inner: unit -> DY unit
 (requires fun h -> valid_trace h)
 (ensures fun h0 _ h1 -> valid_trace h1)

let acme_test_2_inner _ =
  let client:principal = "client" in
  let server:principal = "server" in
  let serv_dom:domain = Root "server" in
  let client_dom:domain = Root "my_domain" in
  domain_principal_mapping_lemma serv_dom;
  domain_principal_mapping_lemma client_dom;
  let now = current_trace_len () in
  let account_url = gen_publishable_url now serv_dom ["client"; "account2"] in
  let order_url = gen_publishable_url now serv_dom ["client"; "order-cert"] in
  let (client_acc_sessionid, server_acc_sessionid) = gen_account client server account_url order_url in
  let server_ca_privkey_sessionid = gen_private_ca_key server in
  let client_seq_doms = Seq.create 1 client_dom in
  //start protocol
  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
  
  let client_order_idx = acme_client_orders_certificate_nw client client_seq_doms client_acc_sessionid in
  print_string "step 1\n";
  let server_order_idx = acme_server_new_order_nw server client_order_idx in
  print_string "step 2\n";
  let (client_order_sessionid, num_of_authorization_urls) = acme_client_receive_order_response_nw client server_order_idx in
  print_string "step 3: client receives order response\n";
  client_server_process_all_authorizations_nw client server serv_dom client_order_sessionid num_of_authorization_urls 0;
  let server_challenge_idx = acme_server_trigger_challenge_verification_nw server in
  print_string "step 7\n";
  let client_challenge_resp_idx = acme_client_challenge_response_nw client server_challenge_idx in
  print_string "step 8\n";
  acme_server_receive_challenge_verification_nw server client_challenge_resp_idx;

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
  
  let client_sendCSR_idx = acme_client_sends_CSR_nw client client_order_sessionid in
  print_string "step 9\n";
  let server_retriev_cert_idx = acme_server_finalize_order_nw server client_sendCSR_idx in
  print_string "step 10\n";

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
  let (client_get_cert_idx,_) = acme_client_retrieves_certificate_nw client server_retriev_cert_idx in
  print_string "step 11\n";
  let server_cert_idx = acme_server_retrieve_cert_nw server client_get_cert_idx in
  print_string "step 12\n";
  let _ = acme_client_receives_and_saves_certificate_nw client server_cert_idx in
  ()

val acme_test_2: unit -> DY unit
 (requires fun h -> valid_trace h)
 (ensures fun h0 _ h1 -> valid_trace h1)

#push-options "--max_ifuel 1"
let acme_test_2 _ =
  let t = get () in
  let r, t' = reify (acme_test_2_inner ()) t in
  let r:result unit = r in
  (match r with
  | Success _ ->
      // Do NOT! change the following line! This string is matched by Jenkins to assure that the functional test still works!
      print_string "PROTOCOL RUN (FAILS for jenkins): ACME client verified a domain he does not own\n"
  | Error "Could not extract challenge information from client state" ->
      // Do NOT! change the following line! This string is matched by Jenkins to assure that the functional test still works as expected.
      print_string "PROTOCOL RUN (SUCCESS for jenkins): ACME Client cannot verify a domain he doesn't own\n"
  | Error s -> print_string ("Test 2 Error: "^s^"\n"); error s);
  ()
#pop-options


(**
test 3: multiple domain, with network, client owns all domains
This test passes iff the protocol stops at step 9, i.e.,
the string "PROTOCOL RUN (SUCCESS for jenkins): ACME regular run" is printed out
*)
val acme_test_3: unit -> DYL unit
 (requires fun h ->  True )
 (ensures fun h0 _ h1 -> True)

#push-options "--z3rlimit 200 --max_ifuel 2 --max_fuel 5"
let acme_test_3 _ =
 let client:principal = "client" in
 let server:principal = "server" in
 let serv_dom:domain = Root "server" in
 let client_dom1:domain = Root "client" in
 let client_dom2:domain = Sub "sub" client_dom1 in 
 domain_principal_mapping_lemma serv_dom;
 domain_principal_mapping_lemma client_dom1;
 domain_principal_mapping_lemma client_dom2; 
  let now = current_trace_len ()  in 
 let account_url = gen_publishable_url now serv_dom ["client"; "account3"] in
 let order_url = gen_publishable_url now serv_dom ["client"; "order-cert"] in
 let (client_acc_sessionid, server_acc_sessionid) = gen_account client server account_url order_url in
 let server_ca_privkey_sessionid = gen_private_ca_key server in
 let list_doms = [client_dom1; client_dom2] in
 let client_seq_doms = init_seq_with_list list_doms in
 init_seq_with_list_length_lemma list_doms;
 assert(Seq.length client_seq_doms > 0); 
 //start protocol

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
  
 let order_http_req_idx = acme_client_orders_certificate_nw client client_seq_doms client_acc_sessionid in
 print_string "step 1\n";
 let order_http_resp_idx = acme_server_new_order_nw server order_http_req_idx in
 print_string "step 2\n";
 let (client_order_sessionid, num_of_authorization_urls) = acme_client_receive_order_response_nw client order_http_resp_idx in   
 print_string "step 3: client receives order response\n";
 client_server_process_all_authorizations_nw client server serv_dom client_order_sessionid num_of_authorization_urls 0;
 server_client_verify_all_challenges_nw server client num_of_authorization_urls 0; //each authorization have only one challenge

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
 let csr_http_req_idx = acme_client_sends_CSR_nw client client_order_sessionid in
 print_string "step 9\n";
 let retriev_cert_http_resp_idx = acme_server_finalize_order_nw server csr_http_req_idx in
 print_string "step 10\n";

    let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
 let (get_cert_http_req_idx,_) = acme_client_retrieves_certificate_nw client retriev_cert_http_resp_idx in
 print_string "step 11\n";
 let cert_http_resp_idx = acme_server_retrieve_cert_nw server get_cert_http_req_idx in
 print_string "step 12\n";
 let cert_sessionid = acme_client_receives_and_saves_certificate_nw client cert_http_resp_idx in
 // Do NOT! change the following line! This string is matched by Jenkins to assure that the functional test still works!
 print_string "PROTOCOL RUN (SUCCESS for jenkins): ACME regular run with network\n";
 ()
#pop-options


(**
test 4: multiple domain, with network, client owns only one domain
This test passes iff the protocol stops at step 9, i.e.,
the string "PROTOCOL RUN (SUCCESS for jenkins): ACME Client cannot verify a domain he doesn't own" is printed out
*)
val acme_test_4_inner: unit -> DY unit
 (requires fun h -> valid_trace h)
 (ensures fun h0 _ h1 -> valid_trace h1)

#push-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 3"
let acme_test_4_inner _ =
 let client:principal = "client" in
 let server:principal = "server" in
 let serv_dom:domain = Root "server" in
 let client_dom1:domain = Root "client" in
 let client_dom2:domain = Root "unknown" in
 domain_principal_mapping_lemma serv_dom;
 domain_principal_mapping_lemma client_dom1;
 domain_principal_mapping_lemma client_dom2;
 let now = current_trace_len () in
 let account_url = gen_publishable_url now serv_dom ["client"; "account4"] in
 let order_url = gen_publishable_url now serv_dom ["client"; "order-cert"] in
 let (client_acc_sessionid, server_acc_sessionid) = gen_account client server account_url order_url in
 let server_ca_privkey_sessionid = gen_private_ca_key server in
 let list_doms = [client_dom1; client_dom2] in
 let client_seq_doms = init_seq_with_list list_doms in
 init_seq_with_list_length_lemma list_doms;
 assert(Seq.length client_seq_doms > 0);
 //start protocol
   let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
  
 let order_http_req_idx = acme_client_orders_certificate_nw client client_seq_doms client_acc_sessionid  in
 print_string "step 1\n";
 let order_http_resp_idx = acme_server_new_order_nw server order_http_req_idx in
 print_string "step 2\n";
 let (client_order_sessionid, num_of_authorization_urls) = acme_client_receive_order_response_nw client order_http_resp_idx in
 print_string "step 3: client receives order response\n";
 client_server_process_all_authorizations_nw client server serv_dom client_order_sessionid num_of_authorization_urls 0;
 server_client_verify_all_challenges_nw server client num_of_authorization_urls 0; //each authorization have only one challenge

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
 let csr_http_req_idx = acme_client_sends_CSR_nw client client_order_sessionid in
 print_string "step 9\n";
 let retriev_cert_http_resp_idx = acme_server_finalize_order_nw server csr_http_req_idx in
 print_string "step 10\n";

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw client nonce_resp_idx in
 let (get_cert_http_req_idx,_) = acme_client_retrieves_certificate_nw client retriev_cert_http_resp_idx in
  print_string "step 11\n";
 let cert_http_resp_idx = acme_server_retrieve_cert_nw server get_cert_http_req_idx in
 print_string "step 12\n";
 let cert_sessionid = acme_client_receives_and_saves_certificate_nw client cert_http_resp_idx in 
 print_string "PROTOCOL RUN (FAILS for jenkins): ACME client verified a domain he does not own\n";
 () //protocol is done
                            
#pop-options

val acme_test_4: unit -> DY unit
 (requires fun h -> valid_trace h)
 (ensures fun h0 _ h1 -> valid_trace h1)

#push-options "--max_ifuel 1"
let acme_test_4 _ =
  let t = get () in
  let r, t' = reify (acme_test_4_inner ()) t in
  let r:result unit = r in
  (match r with
  | Success _ ->
      // Do NOT! change the following line! This string is matched by Jenkins to assure that the functional test still works!
      print_string "PROTOCOL RUN (FAILS for jenkins): ACME client verified a domain he does not own\n"
  | Error "Could not extract challenge information from client state" ->
      // Do NOT! change the following line! This string is matched by Jenkins to assure that the functional test still works as expected.
      print_string "PROTOCOL RUN (SUCCESS for jenkins): ACME Client cannot verify a domain he doesn't own\n"
  | Error s -> print_string ("Test 4 Error: "^s^"\n"); error s);
  ()
#pop-options


(**
test 5: multiple domain, with network, (corrupted) client owns only one domain, *FAULTY* server
This test is based on a faulty server implementation and carries out an attack of the same class as described in https://arstechnica.com/information-technology/2020/03/lets-encrypt-revoking-https-certs-due-to-certificate-authority-bug/
The server does not iterate on ALL domains to check authorization validity. Instead, the server only check if there exists one domain whose ownership has been validated.
The attack succeeds if the attacker can get certificate for an honest domain that he does not own, hence he can know the certificate private key and breaks the main secrecy property
*)
val acme_test_5_attack: unit -> DY unit
 (requires fun h -> valid_trace h)
 (ensures fun h0 _ h1 -> valid_trace h1)

#push-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 3"
let acme_test_5_attack _ =
 let corrupted_client:principal = "corrupted_client" in
 let honest_client:principal = "honest_client" in
 let server:principal = "server" in
 let serv_dom:domain = Root "server" in
 let client_dom1:domain = Root "corrupted_client" in
 let client_dom2:domain = Root "honest_client" in
 domain_principal_mapping_lemma serv_dom;
 domain_principal_mapping_lemma client_dom1;
 domain_principal_mapping_lemma client_dom2;
 assert(corrupted_client = domain_principal_mapping client_dom1);
 let now = current_trace_len () in
 let account_url = gen_publishable_url now serv_dom ["client"; "account5"] in
 let order_url = gen_publishable_url now serv_dom ["client"; "order-cert"] in
 let (client_acc_sessionid, server_acc_sessionid) = gen_account corrupted_client server account_url order_url in
 let server_ca_privkey_sessionid = gen_private_ca_key server in
 let list_doms = [client_dom2; client_dom1] in
 let client_seq_doms = init_seq_with_list list_doms in
 init_seq_with_list_length_lemma list_doms;
 assert(Seq.length client_seq_doms > 0);
 //attacker compromises the corrupted_client
 let _ = compromise corrupted_client 0 0 in 
 let current_trace = get() in
 //we must assume that the current trace is valid here, because compromise is a DY function not DYL function.
 assume(valid_trace current_trace); 
 //start protocol
   let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw corrupted_client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw corrupted_client nonce_resp_idx in
  
 let order_http_req_idx = acme_client_orders_certificate_nw corrupted_client client_seq_doms client_acc_sessionid  in 
 print_string "step 1\n"; 
 let order_http_resp_idx = acme_server_new_order_nw server order_http_req_idx in 
 print_string "step 2\n";
 let (client_order_sessionid, num_of_authorization_urls) = acme_client_receive_order_response_nw corrupted_client order_http_resp_idx in
 print_string "step 3: client receives order response\n"; 
 client_server_process_all_authorizations_nw corrupted_client server serv_dom client_order_sessionid num_of_authorization_urls 0;
 server_client_verify_all_challenges_nw_faulty server corrupted_client num_of_authorization_urls 0; //the faulty version of checking is used

  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw corrupted_client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw corrupted_client nonce_resp_idx in
  
 let csr_http_req_idx= acme_client_sends_CSR_nw corrupted_client client_order_sessionid in
 print_string "step 9\n";
 let retriev_cert_http_resp_idx = acme_server_finalize_order_nw server csr_http_req_idx in
 print_string "step 10\n";
  let len_now = current_trace_len () in
  let new_nonce_url = gen_new_replay_nonce_url len_now serv_dom in 
  let nonce_req_idx = acme_client_request_replay_nonce_nw corrupted_client new_nonce_url in
  let nonce_resp_idx = acme_server_new_nonce_nw server nonce_req_idx in
  let _ = acme_client_receives_and_saves_replay_nonce_nw corrupted_client nonce_resp_idx in
  
 let (get_cert_http_req_idx,_) = acme_client_retrieves_certificate_nw corrupted_client retriev_cert_http_resp_idx in
 print_string "step 11\n";
 let cert_http_resp_idx = acme_server_retrieve_cert_nw server get_cert_http_req_idx in
 print_string "step 12\n";
 let cert_sessionid = acme_client_receives_and_saves_certificate_nw corrupted_client cert_http_resp_idx in
 print_string "PROTOCOL RUN (SUCCESS for jenkins): Attack succeeds. The attacker get certificate for the domain it does not own\n";
 () //protocol is done
                             
#pop-options




(*! Main function*)
let main' () : DY unit (fun _ -> True) (fun _ _ _ -> True) =
  print_string "start\n";
  let h0 = get() in
  assume(valid_trace h0);
  print_string "======= test 1 ======== \n";
  let _ = acme_test_1 () in
  print_string "======= END test 1 ======== \n";
  print_string "======= test 2 ======== \n";
  let _ = acme_test_2 () in
  print_string "======= END test 2 ======== \n";
  print_string "======= test 3 ======== \n"; 
  let _ = acme_test_3 () in
  print_string "======= END test 3 ======== \n";
  print_string "======= test 4 ======== \n";
  let _ = acme_test_4 () in
  print_string "======= END test 4 ======== \n" ; 
  print_string "======= test 5: ATTACK!!! ======== \n";
  let _ = acme_test_5_attack () in
  print_string "======= END test 5 ======== \n"
  //print_trace ()


#set-options "--max_ifuel 2"
let main =
  IO.print_string "Starting with tests...\n";
  let t0 = Seq.empty in
  let r,t1 = (reify (main' ()) t0) in
  (match r with
   | Error s -> IO.print_string ("ERROR: "^s^"\n")
   | Success _ -> ());
  ()
