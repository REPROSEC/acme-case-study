open Pyops
open Log


let ensure_pyml_is_loaded () =
  if not (Py.is_initialized ()) then
    Py.initialize (*~verbose:true *) ~version:3 ()


let print_object_attributes obj =
  ensure_pyml_is_loaded ();
  let builtins = Py.Eval.get_builtins () in
  let dir_python = Py.Dict.find_string builtins "dir" in
  let dir_ocaml = Py.Callable.to_function dir_python in
  print_endline (Py.Object.to_string (dir_ocaml [| obj |] ))


let print_object_attributes_with_values ?(include_hidden = false) obj =
  ensure_pyml_is_loaded ();
  let dynamic_module = Py.Import.add_module "ocaml" in
  Py.Module.set dynamic_module "input_object" obj;
  if include_hidden then (
    let _ = Py.Run.eval ~start:Py.File
              "from ocaml import input_object \n\
               from pprint import pprint\n\
               pprint(dict([(a, getattr(input_object, a)) for a in dir(input_object)]))" in
    ()
  ) else (
    let _ = Py.Run.eval ~start:Py.File
              "from ocaml import input_object \n\
               from pprint import pprint\n\
               pprint(dict([(a, getattr(input_object, a)) for a in dir(input_object) if not a.startswith('_')]))" in
    ()
  )


let do_http_request
      ~http_method
      ?(data = Py.none)
      ?(additional_keyword_args = [])
      ?(headers = [])
      url =
  ensure_pyml_is_loaded ();
  let headers_py_tuples = List.map (fun (a, b) -> (a, Py.String.of_string b)) headers in
  let py_headers = ("headers", Py.Dict.of_bindings_string headers_py_tuples) in
  let py_data = ("data", data) in
  let keyword_args = py_headers :: py_data :: additional_keyword_args in
  let req_lib = Py.import "requests" in
  let response = Py.Callable.to_function_with_keywords
                   req_lib.@$(http_method)
                   [| Py.String.of_string url |]
                   keyword_args in
  Logs.debug (fun m -> m "Sent %s HTTP request to '%s' with headers '%s' body '%s' got response (%s) '%s'"
                         http_method
                         url
                         (Py.Object.to_string (response.@$("request").@$("headers")))
                         (Py.Object.to_string (response.@$("request").@$("body")))
                         (Py.Object.to_string response.@$("status_code"))
                         (Py.Bytes.to_string response.@$("content"))
    );
  (response, Py.Object.to_string response.@$("status_code"))


let parse_json_file_to_dict path =
  ensure_pyml_is_loaded ();
  let builtins = Py.Eval.get_builtins () in
  let open_python = Py.Dict.find_string builtins "open" in
  let f = Py.Callable.to_function open_python [| Py.String.of_string path |] in
  let json_lib = Py.import "json" in
  let json = json_lib.&("load") [| f |] in
  let _ = f.&("close") [| |] in
  json



(**
 Given a string [domain], this function returns a Python dictionary corresponding to an identifier.

  Example:
        input: domain = example.com
        return value: { "type": "dns", "value": "example.com" }
 *)
let create_pyobj_dict_from_domain_string (domain:string) : Pytypes.pyobject =
    ensure_pyml_is_loaded ();
    let identifier_object = Py.Dict.create () in
    identifier_object.%$["type"] <- Py.String.of_string "dns";
    identifier_object.%$["value"] <- Py.String.of_string domain;
    identifier_object


(**
  Given a list of identifiers (as pyobjects), this function returns a one-element python dictionary
  with the key "identifiers" and a Python list of the identifiers.
 *)
let create_payload_from_identifier_list
  (identifier_list:Pytypes.pyobject list) =
    ensure_pyml_is_loaded ();
    let identifier_object_list = Py.List.of_list identifier_list in
    let payload = Py.Dict.create () in
    payload.%$["identifiers"] <- identifier_object_list;
    payload
