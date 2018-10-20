open Lib.Util

module type NodeType =
  sig
    type t
    val id : t -> int
    val info : string
    val arity : int
    val compare : t -> t -> int
    val create : int list -> t
    val to_string : t -> string
    val to_dot : t -> ?highlight:(int option) -> int -> string
    val dot_of_edge : t -> int -> t -> int -> string
    val coh : (t*t) list -> (t*t) -> bool
    val rename : int -> t -> t
    val library : (t*t) list Lib.StringMap.t
    val compatible : t -> t -> bool
    val gluable : t -> t -> bool
    val tn : (int list * int list) list -> (t*t) list
  end



module SimpleNode =
  (struct
      type t = int
      let info = "Simple Graphs"
      let arity = 0
      let rename i u = i
      let id u = u
      let compatible = fun _ _ -> true
      let gluable = fun u u' -> id u = id u'
      let has_rigid_bonds = false

      let compare = Pervasives.compare

      let create l =
	match l with
	  [i] -> i
	| _ -> failwith "Cannot parse node"

      let to_string = string_of_int

      let to_dot u ?(highlight=None) i =
	let ref_node = string_of_int i in
	ref_node^" [label=\""^(to_string u)^"\" "^(hi2str highlight)^"]"

      let dot_of_edge u i v j =
	Printf.sprintf "%d -> %d [dir=none]" i j

      let coh _ _ = true

      let tn = List.map (fun (l,l') -> (create l,create l'))

      let library =
	let void = [] in
	let house =
	  [
	    ([0],[1]) ;
	    ([1],[2]) ;
	    ([2],[3]) ;
	    ([3],[0]) ;
	    ([3],[4]) ;
	    ([2],[4])
	  ]
	in
	let square =
	  [
	    ([0],[1]) ;
	    ([1],[2]) ;
	    ([2],[3]) ;
	    ([3],[0]) ;
	  ]
	in
	let dsquare =
	  [
	    ([0],[1]) ;
	    ([1],[2]) ;
	    ([2],[3]) ;
	    ([3],[0]) ;
	    ([0],[2]) ;
	  ]
	in
        let osquare =
	  [
	    ([0],[1]) ;
	    ([0],[3]) ;
	    ([2],[3]) ;
	  ]
	in
	let triangle =
	  [
	    ([0],[1]) ;
	    ([1],[2]) ;
	    ([0],[2])
	  ]
	in
	let one = [([3],[2])] in
	let two = [([0],[1]);([1],[2])]
	in
	let lib = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	let lib = Lib.StringMap.add "one" (tn one) lib in
	let lib = Lib.StringMap.add "two" (tn two) lib in
	let lib = Lib.StringMap.add "dsquare" (tn dsquare) lib in
        let lib = Lib.StringMap.add "osquare" (tn osquare) lib in
	Lib.StringMap.add "house" (tn house)
			  (Lib.StringMap.add "square" (tn square)
					     (Lib.StringMap.add "triangle" (tn triangle) lib))

  end:NodeType)
