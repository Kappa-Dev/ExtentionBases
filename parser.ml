open Angstrom

type result =
  | Mode of string
  | Add of string
  | Add_named of (int list * int list) list * string
  | List
  | Debug
  | Build of string*string
  | Load of string

let ws = skip_while (function ' ' -> true | _ -> false)

let inst name ret =
  string name *> ws *>
  take_while (function _ -> true) >>| fun mode_result ->
  ret mode_result

let mode = inst "mode" (fun x -> Mode x)
let load = inst "load" (fun x -> Load x)

let list_parser p = char '[' *> ws *> sep_by (ws *> (char ';') *> ws) p <* ws <* char ']'
let number = take_while1 (function '0'..'9' -> true | _ -> false) >>| fun s -> int_of_string s

let tuple elt_parser ret =
  char '(' *> ws *> elt_parser >>= fun elt1 ->
  ws *> char ',' *> ws *> elt_parser >>= fun elt2 ->
  ws *> char ')' *> return (ret (elt1,elt2))


let name = take_while (function 'a'..'z' | 'A'..'Z' | '0'..'9' -> true | _ -> false)

let int_list_tuple = tuple (list_parser number) (fun x -> x)

let nodes = list_parser int_list_tuple

let add = string "add" *> ws *> name >>| fun name_result -> Add name_result

let add_named =
  string "add" *> ws *> nodes >>= fun nodes_result ->
  ws *> string "as" *> ws *> name >>| fun name_result ->
  Add_named (nodes_result,name_result)

let list = string "list" *> return List

let debug = string "debug" *> return Debug

let build =
  string "build" *> ws *> tuple name (fun (x,y) -> Build (x,y))


let global p = p <* end_of_input

let line = choice (List.map global [mode ; add; add_named; list; build ; load])

let parse = parse_string line
