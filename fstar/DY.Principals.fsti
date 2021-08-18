/// DY.Principals
/// =============
///
/// This module defines the basic structures needed for modelling the principals of the system.
///
/// A principal (i.e., an instance of a procol role) can have an arbitrary number of (independent)
/// sessions. Each session has its own key-value storage inside the principal's state.
///
/// In addition to sessions, there are versions, each stored state of a session is "tagged" with a
/// version. The version itself is just a natural number and can be chosen freely by the protocol
/// implementation (e.g., all versions might always be zero). These can be used to explicitly model
/// and refeer to evolving session state as a session goes through various steps of the modeled
/// protocol.
/// Note that versions are really "just" metadata to sessions.
/// 
/// .. fst::
///    :class: hidden

module DY.Principals
open FStar.Seq

/// Principals, Session Identifiers and Version Identifiers
/// -------------------------------------------------------
///

(** Principals are just strings (public values) *)
type principal = string

/// Note that ``sessionid`` and ``versionid`` are not used in principal's internal state (or stored
/// anywhere else). They just serve as "search terms" to refeer to multiple versions/sessions at
/// once. This is useful in several places, e.g., when corrupting a principal: We can just corrupt
/// all sessions (and all their versions) of a principal at once. The "search" behavior is defined
/// in the ``covers`` function below.
(**
A [sessionid] identifies a set of sessions at a given principal (either exactly one or all sessions
of that principal). Note that [sessionid]s are just "search terms" which match none, exactly one or
all sessions of a principal.
*)
type sessionid = | AnySession: prin:principal -> sessionid
                 | Session: prin:principal -> session_index:nat -> sessionid

(**
A [versionid] identifies a set of versions of a session or all versions in all sessions at a
principal and can (only) be used as a "search term".
Versions are basically metadata for a session. The versions can be freely chosen by the application,
but are intended to represent protocol steps.
*)
type versionid = | AnyVersion: sid:sessionid -> versionid
                 | Version: sid:sessionid -> version_index:nat -> versionid

(**
A vector of version indices (usually describing the latest version number of all sessions of a
principal, e.g. a version vector [3,2,4] would mean that the first session is in version 3, the
second session in version 2 and the third session in version 4.).
A version_vec is usually accompanied by a principal's internal state (which is a sequence of
sessions - each entry in the version_vec corresponds to an entry in the session sequence and tells
us in which version the corresponding session is).
*)
type version_vec = seq nat

(** Get the sessionid from a versionid [vsid] *)
let get_sid (vsid:versionid) : sessionid =
  match vsid with
  | AnyVersion sid -> sid
  | Version sid _ -> sid

(** Get the principal from a versionid [vsid] *)
let get_principal (vsid:versionid) : principal = 
  match get_sid vsid with
  | AnySession prin -> prin
  | Session prin _ -> prin

(** Describes (as a search term, see the comments on versionid and sessionid) all sessions (and all
their versions) of the given principal. *)
let any principal : versionid = AnyVersion (AnySession principal)

(** Describes (as a search term, see the comments on versionid and sessionid) a specific session of
the given principal (without specifing the version, i.e., describing all versions of the given
session). *)
let sess principal session_index : versionid = AnyVersion (Session principal session_index)

(** Describes (as a search term, see the comments on versionid and sessionid) a specific version of
a specific session of the given principal. *)
let sess_ver principal session_index version_index : versionid = Version (Session principal session_index) version_index

(**
A [versionid] [s1] "covers" [s2] if [s1] describes the same principal, session at that principal
and version of that session as [s2]. Note that [s1] might describe [AnyVersion] of a session or even
[AnySession] at a principal.

Intuitions:
- If [s1] covers [s2], [s2] is "matched" by the "search term" [s1].
- [s1] is equal or less specific than [s2].
*)
let covers (s1:versionid) (s2:versionid) =
  match s1 with
  | AnyVersion (AnySession p1) -> p1 = get_principal s2
  | AnyVersion (Session p1 i1) -> Session p1 i1 = get_sid s2
  | _ -> s1 = s2

val covers_is_reflexive: s:versionid ->
  Lemma (ensures (covers s s))
        [SMTPat (covers s s)]
val covers_is_transitive: unit ->
  Lemma (forall s1 s2 s3. covers s1 s2 /\ covers s2 s3 ==> covers s1 s3)

