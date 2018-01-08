open Angstrom

type result = 
  | Mode of string
  | Add of string
  | Add_named of ((int list * int list) list * string)
  | List
  | Debug
  | Build of string*string

let ws = skip_while (function ' ' -> true | _ -> false)

let mode = 
  string "mode" *> ws *> 
  take_while (function _ -> true) >>| fun mode_result ->
  Mode mode_result

  let list_parser p = char '[' *> ws *> sep_by (ws *> (char ';') *> ws) p <* ws <* char ']' 
  let number = take_while (function '0'..'9' -> true | _ -> false) >>= (function
  | "" -> fail "Cannot find number"
  |  s -> return (int_of_string s))

  let tuple = 
    char '(' *> ws *> list_parser number >>= fun list1 ->
    ws *> char ',' *> ws *> list_parser number >>= fun list2 -> 
    ws *> char ')' *> return (list1,list2)

let nodes = list_parser tuple

let name = take_while (function 'a'..'z' | 'A'..'Z' | '0'..'9' -> true | _ -> false)

let add = string "add" *> ws *> name >>| fun name_result -> Add name_result

let add_named = 
  string "add" *> ws *> nodes >>= fun nodes_result -> 
  ws *> string "as" *> ws *> name >>| fun name_result ->
  Add_named (nodes_result,name_result)

let list = string "list" *> return List

let debug = string "debug" *> return Debug

let build = 
  string "build" *> ws *> char '(' *>
  name >>= fun name1 ->
  ws *> char ',' *> ws *>
  name >>= fun name2 ->
  ws *> char ')' *> return (Build (name1,name2))

let global p = p <* end_of_input

let line = choice (List.map global [mode ;add;add_named;list;build])

let parse s = parse_string line s
