(** Check whether Pyml is loaded and load it if not. Loads python version 3. *)
val ensure_pyml_is_loaded : unit -> unit

(** Print a pyobject's attributes *)
val print_object_attributes : Pytypes.pyobject -> unit

(** Print a pyobject's attributes with their values. Optionally including hidden attributes (i.e.,
   starting with '_'). *)
val print_object_attributes_with_values : ?include_hidden:bool -> Pytypes.pyobject -> unit


(** Send an HTTP request to the specified [url] using the given [http_method].  You may also provide
  headers, body data (if applicable for the request method) and
  additional keyword arguments to the underlying python requests library.

  @param http_method The HTTP method to use (lowercase)
  @param data Request body data (should usually be a python string)
  @param additional_keyword_args Keyword arguments to the underlying python requests library
  @param headers Headers for the request (as [(header name, value)])
  @param url The URL to send the request to

  @return (response, HTTP status)
*)
val do_http_request :
  http_method : string ->
  ?data : Pytypes.pyobject ->
  ?additional_keyword_args : ((string * Pytypes.pyobject) list) ->
  ?headers : (string * string) list ->
  string ->
  (Pytypes.pyobject * string)


val parse_json_file_to_dict : string -> Pytypes.pyobject


(**
 Given a string [domain], this function returns a Python dictionary corresponding to an identifier.

  Example:
        input: domain = example.com
        return value: { "type": "dns", "value": "example.com" }
 *)
val create_pyobj_dict_from_domain_string : string -> Pytypes.pyobject

(**
  Given a list of identifiers (as pyobjects), this function returns a one-element python dictionary
  with the key "identifiers" and a Python list of the identifiers.
 *)
val create_payload_from_identifier_list : Pytypes.pyobject list ->  Pytypes.pyobject
