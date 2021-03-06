/// ACME.Data.Predicates (Implementation)
/// =====================================
module ACME.Data.Predicates
(**
 - To write/typecheck a protocol runs, we need that the input (which is the output of another function) satisfy some properties.
   For example: the authorization (generated by the server that then processed as the input of the client) must satisfy that the tokens embedded in it are publishable.
 - This module contains predicates used to refine the types in ACME.Client.* and ACME.Server.*
*)




