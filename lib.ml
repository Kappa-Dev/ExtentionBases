module type OrderedType = sig type t val compare : t -> t -> int val to_string : t -> string end

module IntMap = Map.Make (struct type t = int let compare = compare end)

module IntSet = Set.Make (struct type t = int let compare = compare end)
module Int2Set = Set.Make (struct type t = (int*int) let compare = compare end)

module StringMap = Map.Make (struct type t = string let compare = compare end)


module Dict =
  struct
    exception Clashing
    type t = {int_of_str : int StringMap.t ; str_of_int : string IntMap.t ; fresh : int}
    let empty = {int_of_str = StringMap.empty ; str_of_int = IntMap.empty ; fresh = 0}
    let to_id x d = StringMap.find x d.int_of_str
    let to_name x d = IntMap.find x d.str_of_int
    let add i n d =
      if StringMap.mem n d.int_of_str || IntMap.mem i d.str_of_int then raise Clashing
      else
        {d with str_of_int = IntMap.add i n d.str_of_int ; int_of_str = StringMap.add n i d.int_of_str}
    let fresh d = (d.fresh, {d with fresh = d.fresh+1})
  end

module Util =
  struct
    let histfile = "./session_history"
    let log s = print_endline s
    let db_mode = ref false
    let safe_mode = ref false
    let db () = !db_mode
    let safe () = !safe_mode
    let safe_mode () =
      if not !safe_mode then
        (print_string "Entering safe mode\n" ; safe_mode := true)
      else
        (print_string "Exiting safe mode\n" ; safe_mode := false)

    let flush_string = fun x -> print_string x ; flush stdout
    let debug_mode () =
      if not !db_mode then
        (print_string "Entering debug mode\n" ; db_mode := true ; Printexc.record_backtrace true)
      else
        (print_string "Exiting debug mode\n" ; db_mode := false ; Printexc.record_backtrace false)

    let proj_left = (fun (x,_) -> x)
    let proj_right = (fun (_,y) -> y)
    let myassert = fun b test -> assert (if b then test else true)

    let rec ask_until s f = match LNoise.linenoise s with
      | None ->
        log "Attempting to save session history";
        ignore (LNoise.history_save histfile);
        failwith "Could not read answer.";
      | Some resp ->
        ignore(LNoise.history_add resp);
        match f resp with
        | None -> failwith "bye"
        | Some value -> value


    let each_line file callback initial  =
      let channel = open_in file
      and line = ref ""
      and lineno = ref 0
      and acc = ref initial in
      try
        while true do
          line := input_line channel;
          incr lineno;
          (match callback !acc !lineno !line with
           | Some d -> acc := d
           | None -> raise End_of_file);
        done;
        !acc
      with End_of_file -> !acc


    let red str = "\027[91m"^str^"\027[0m"
    let green str = "\027[92m"^str^"\027[0m"
    let yellow str = "\027[93m"^str^"\027[0m"
    let blue str = "\027[94m"^str^"\027[0m"

    let to_list fold x =
      fold (fun i cont -> i::cont) x []
  end
