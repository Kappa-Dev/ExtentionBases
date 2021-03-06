open Angstrom

let legal_modes = ["kappa";"kappaSym";"degree";"simple"]
let legal_output = ["positive" ; "negative"]


type base_type = Complete | Sparse | Tree
type share_type = MinShare of int | Adjust of int
type command =
  | Help
  | Mode of string
  | Add of string
  | Add_named of (int list * int list) list * string
  | List
  | Debug
  | Safe
  | Build of string*string
  | Load of string
  | Output of bool
  | Shell of string * string array
  | Exit
  | Reset
  | Blank
  | BaseShape of base_type
  | Sharing of share_type
  | MaxStep of int

let ws = skip_while (function ' ' -> true | _ -> false)
let ws1 = take_while1 (function ' ' -> true | _ -> false)


let inst name alt ret =
  string name *> ws *>
  (if alt = [] then take_while (function _ -> true) else choice (List.map string alt)) >>| fun mode_result ->
  ret mode_result

let mode mlist = inst "mode" mlist (fun x -> Mode x)
let load = inst "load" [] (fun x -> Load x)

let output olist = inst "output" olist (fun x -> Output (if x="positive" then true else false))

let exit_p = inst "exit" [] (fun _ -> Exit)

let list_parser p = char '[' *> ws *> sep_by (ws *> (char ';') *> ws) p <* ws <* char ']'
let pos_number = take_while1 (function '0'..'9' -> true | _ -> false) >>| fun s -> int_of_string s
let neg_number = char '-' *> take_while1 (function '0'..'9' -> true | _ -> false) >>| fun s -> -(int_of_string s)
let number = choice [pos_number ; neg_number]

let number_or_nothing = choice [(number >>| fun i -> Some i) ; ws >>| fun () -> None]


let arg = take_while1 (function ' ' -> false | _ -> true)
let args_parser = sep_by ws1 arg

let shell = char '!' *> args_parser >>| function
            | arg::tl as l ->
               let args = Array.make (List.length l) ""
               in
               let _ =
                 List.fold_left
                   (fun i argument -> args.(i) <- argument ; i+1
                   ) 0 l
               in
               Shell (arg,args)
            | [] -> Shell ("",Array.make 0 "")

let tuple elt_parser ret =
  char '(' *> ws *> elt_parser >>= fun elt1 ->
  ws *> char ',' *> ws *> elt_parser >>= fun elt2 ->
  ws *> char ')' *> return (ret (elt1,elt2))


let name = take_while (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '^' | '-' | '\'' -> true | _ -> false)

let int_list_tuple = tuple (list_parser number) (fun x -> x)

let nodes = list_parser int_list_tuple

let add = string "add" *> ws *> name >>| fun name_result -> Add name_result


let sharing = string "sharing" *> ws *> pos_number >>| fun i -> Sharing (MinShare i)
let self = string "adjust" *> ws *> pos_number >>| fun i -> Sharing (Adjust i)
let sparse = string "sparse" *> ws >>| fun () -> BaseShape Sparse
let tree = string "treelike" *> ws >>| fun () -> BaseShape Tree
let complete = string "complete" *> ws >>| fun () -> BaseShape Complete
let step = string "step" *> ws *> number >>| fun i -> MaxStep i
let help = string "help" *> ws >>| fun () -> Help
let set = string "set" *> ws *> choice [sharing ; sparse ; tree ; self ; complete ; step ; help ]


let blank = ws *> return Blank

let add_named =
  string "add" *> ws *> nodes >>= fun nodes_result ->
  ws *> string "as" *> ws *> name >>| fun name_result ->
  Add_named (nodes_result,name_result)

let list = string "list" *> return List

let debug = string "debug" *> return Debug
let safe = string "safe" *> return Safe


let build =
  string "build" *> ws1 *> tuple name (fun (x,y)-> Build (x,y))


let global p = ws *> p <* end_of_input
let reset = string "reset" *> ws *> return Reset

let line = choice
             (List.map global [mode legal_modes;
                               set ;
                               add;
                               debug ;
                               safe ;
                               add_named;
                               list;
                               build ;
                               load ;
                               output legal_output ;
                               exit_p ;
                               shell ;
                               reset ;
                               blank ;
             ])

let parse = parse_string line
