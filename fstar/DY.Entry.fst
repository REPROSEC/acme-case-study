/// DY.Entry (implementation)
/// ==========================
module DY.Entry

open DY.Principals
open DY.Labels
open DY.Crypto
open Helpers
module Seq = FStar.Seq

(** Generic event to log relevant protocol events (e.g., the start of a login session) to the trace. *)
type event = string & list bytes


/// Principal's state
/// -----------------
/// Generally, principals' states are organized as follows:
///
/// The state of a principal is stored in the trace as a sequence of maps (mapping from strings to
/// bytes).  This sequence represents different sessions of the principal. Some of these sessions
/// might be long-bytes sessions where, e.g., long-bytes private keys are stored.
///
/// In addition to that, there are "version vectors". These represent metadata about the current
/// protocol step (e.g., store in which protocol step the sessions of the principal currently are).
/// The content of the version vector (just a sequence of natural numbers) is freely chosen by the
/// application with one restriction: The version vector needs to have the same length as the
/// pricipal state sequence.

(** Type of session's state: A mapping from string to bytes *)
type session_state = (list string * (string -> option bytes))

let lookup (sess_st:session_state) (i:string) : option bytes =
  let (_,sess_st) = sess_st in
  sess_st i

(** Type of principal's state: A sequence of mappings from string to bytes *)
unfold type principal_state = Seq.seq session_state

(** Type of entries in the trace *)
noeq type entry_t =
  | (** The bytes for Gen is always a nonce, checked by is_nonce_generated_at (could be enforced
    in valid_trace if needed (not done yet). *)
    Gen: generated_value:bytes -> l:label -> u:usage -> p:usage_pred u -> entry_t
  | SetState: principal -> v:version_vec -> new_state:principal_state -> entry_t
  | Corrupt: corrupted_principal:principal -> session:nat -> version:nat -> entry_t
  | Event: sender:principal -> event -> entry_t // Application specific events, e.g., for authentication properties
  | Message: sender:principal -> receiver:principal -> message:bytes -> entry_t
  | AuthenticatedMessage: sender:principal -> receiver:principal -> message:bytes -> entry_t
(* Pretty-printer for trace entries *)

let sprint_session_state_iv (i:nat) (v:nat) (ss:session_state) : string =
  let (dic,sf) = ss in
  "Session "^string_of_int i^"(v"^string_of_int v^"): ["^
    String.concat "" (List.Tot.map (fun t -> 
			//t^": "^(match sf t with | None -> "_" | Some t -> sprint_bytes t)) dic) 
			match sf t with | None -> "" | Some tm -> t^": "^(sprint_bytes tm)^"; ") dic)
			^"]"

let rec sprint_principal_state_i (del:string) (i:nat) (vs:Seq.seq nat) (ps:principal_state) : Tot string (decreases (Seq.length ps - i))=
  if i < Seq.length ps && Seq.length ps = Seq.length vs
  then if i = Seq.length ps - 1 then sprint_session_state_iv i vs.[i] ps.[i]
       else sprint_session_state_iv i vs.[i] ps.[i]^del^sprint_principal_state_i del (i+1) vs ps
  else ""

let sprint_entry (i:nat) (e:entry_t) =
  (if i < 10 then " "^string_of_int i ^ ". "
   else string_of_int i ^ ". ") ^
 (match e with
  | Gen t l u p -> sprint_generated_nonce t
  | Corrupt p s v -> "Compromised "^sprint_versionid (sess_ver p s v)
  | Event p (n,tl) -> "Event "^p^": "^n^"("^String.concat "," (List.Tot.map sprint_bytes tl)^")"
  | Message s r t -> "Message "^s^"->"^r^": "^sprint_bytes t
  | SetState p v ns -> "SetState "^p^": \n    "^sprint_principal_state_i "\n    " 0 v ns
  | AuthenticatedMessage s r t -> "AuthenticatedMessage "^s^"->"^r^":"^sprint_bytes t)

