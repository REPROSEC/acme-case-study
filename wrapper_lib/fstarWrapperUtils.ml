open Acme


exception Fstar_error of (string * string)

(* Register a pretty-printer for Fstar_error *)
let () =
  Printexc.register_printer
    (function
      | Fstar_error (location, msg) -> Some (Printf.sprintf "FStar Error '%s' at: %s" msg location)
      | _ -> None (* for other exceptions *)
    )


(** "Unpacks" F* values of type [DY_Monad.repr] with [unit] content type.
@return The trace contained in [result]. *)
let split_fstar_result_unit result =
  match result with
  | Helpers.Success (), out_trace -> out_trace
  | Helpers.Error msg, _ ->
     raise (Fstar_error (__LOC__, "Error from F*: " ^ msg))


(** "Unpacks" F* values of type [DY_Monad.repr] with ['a] content type.
@return The "content" contained in [result] plus the contained trace. *)
let split_fstar_result1 result =
  match result with
  | Helpers.Success first, out_trace -> (first, out_trace)
  | Helpers.Error msg, _ ->
     raise (Fstar_error (__LOC__, "Error from F*: " ^ msg))


(** "Unpacks" F* values of type [DY_Monad.repr] with [('a * 'b)] content type.
@return The "content" contained in [result] plus the contained trace. *)
let split_fstar_result2 result =
  match result with
  | Helpers.Success (first, second), out_trace ->
     (first, second, out_trace)
  | Helpers.Error msg, _ ->
     raise (Fstar_error (__LOC__, "Error from F*: " ^ msg))


(** "Unpacks" F* values of type [DY_Monad.repr] with [('a * 'b * 'c)] content type.
@return The "content" contained in [result] plus the contained trace. *)
let split_fstar_result3 result =
  match result with
  | Helpers.Success (first, second, third), out_trace ->
     (first, second, third, out_trace)
  | Helpers.Error msg, _ ->
     raise (Fstar_error (__LOC__, "Error from F*: " ^ msg))


(** "Unpacks" F* values of type [DY_Monad.repr] with [('a * 'b * 'c * 'd)] content type.
@return The "content" contained in [result] plus the contained trace. *)
let split_fstar_result4 result =
  match result with
  | Helpers.Success (first, second, third, fourth), out_trace ->
     (first, second, third, fourth, out_trace)
  | Helpers.Error msg, _ ->
     raise (Fstar_error (__LOC__, "Error from F*: " ^ msg))


(** "Unpacks" F* values of type [DY_Monad.repr] with [('a & 'b & 'c)] content type (dependent triple).
@return The "content" contained in [result] plus the contained trace. *)
let split_fstar_result_dt3 result =
  match result with
  | Helpers.Success (FStar_Pervasives.Mkdtuple3 (first, second, third)), out_trace ->
     (first, second, third, out_trace)
  | Helpers.Error msg, _ ->
     raise (Fstar_error (__LOC__, "Error from F*: " ^ msg))


(** Convert an F* sequence to an OCaml list *)
let fstar_sequence_to_list seq =
  FStar_Seq_Base.__proj__MkSeq__item__l seq
