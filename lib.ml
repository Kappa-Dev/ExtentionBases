module type OrderedType = sig type t val compare : t -> t -> int val to_string : t -> string end

module IntMap = Map.Make (struct type t = int let compare = compare end)

module IntSet = Set.Make (struct type t = int let compare = compare end)

module StringMap = Map.Make (struct type t = string let compare = compare end)


module Dict =
  struct
    type t = {int_of_str : int StringMap.t ; str_of_int : string IntMap.t ; fresh : int}
    let empty = {int_of_str = StringMap.empty ; str_of_int = IntMap.empty ; fresh = 0}
    let to_id x d = StringMap.find x d.int_of_str
    let to_name x d = IntMap.find x d.str_of_int
    let add i n d = {d with str_of_int = IntMap.add i n d.str_of_int ; int_of_str = StringMap.add n i d.int_of_str}
    let fresh d = (d.fresh, {d with fresh = d.fresh+1})
  end

module Util =
  struct
    let db_mode = ref false
    let db () = !db_mode
    let debug_mode () =
      (print_string "Entering debug mode\n" ; db_mode := true)

    let proj_left = (fun (x,_) -> x)
    let proj_right = (fun (_,y) -> y)

    let ask_until str stop_cond =
      let inp = ref "" in
      while not (stop_cond !inp) do
        print_string str ; flush stdout ;
        inp := Pervasives.input_line stdin ;
      done ;
      !inp

    let red str = "\027[91m"^str^"\027[0m"
    let green str = "\027[92m"^str^"\027[0m"
    let yellow str = "\027[93m"^str^"\027[0m"
    let blue str = "\027[94m"^str^"\027[0m"

    let to_list fold x =
      fold (fun i cont -> i::cont) x []
  end
