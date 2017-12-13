
module type NodeType =
  sig
    type t
    val id : t -> int
    val arity : int
    val structure_preserving : (t -> t -> bool) array
    val get_structure : t -> int -> int
    val fold_structure : (int -> int -> 'a -> 'a) -> t -> 'a -> 'a
    val compare : t -> t -> int
    val create : int list -> t
    val to_string : t -> string
    val to_dot : t -> int -> string
    val dot_of_edge : t -> int -> t -> int -> string
    val coh : (t*t) list -> (t*t) -> bool
    val rename : int -> t -> t
    val library : (t*t) list Lib.StringMap.t
    val compatible : t -> t -> bool
    val gluable : t -> t -> bool
  end


module SimpleNode =
  (struct
      type t = int
      let arity = 0
      let rename i u = i
      let id u = u
      let compatible = fun _ _ -> true
      let gluable = fun u u' -> id u = id u'

      let structure_preserving = [||]

      let get_structure _ _ = raise Not_found
      let fold_structure _ _ cont = cont

      let compare = Pervasives.compare

      let create l =
	match l with
	  [i] -> i
	| _ -> failwith "Cannot parse node"

      let to_string = string_of_int

      let to_dot u i =
	let ref_node = string_of_int i in
	ref_node^" [label=\""^(to_string u)^"\"]"

      let dot_of_edge u i v j =
	Printf.sprintf "%d -> %d [dir=none]" i j

      let coh _ _ = true

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
	let tn = List.map (fun (l,l') -> (create l,create l')) in
	let lib = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	let lib = Lib.StringMap.add "one" (tn one) lib in
	let lib = Lib.StringMap.add "two" (tn two) lib in
	let lib = Lib.StringMap.add "dsquare" (tn dsquare) lib in
        let lib = Lib.StringMap.add "osquare" (tn osquare) lib in
	Lib.StringMap.add "house" (tn house)
			  (Lib.StringMap.add "square" (tn square)
					     (Lib.StringMap.add "triangle" (tn triangle) lib))

  end:NodeType)

module KappaNodeSym =
  (struct
      type t = {ag_id : int ; port_id : int ; label : int}

      let arity = 2
      let structure_preserving = [|
          (*f_port*)
          (fun u v -> (*trying port 0 and 1 of label 1 are indistinguishable*)
           match u.label,u.port_id with
             (1,0) -> v.port_id = 0 || v.port_id = 1
           | (1,1) -> v.port_id = 0 || v.port_id = 1
           | (_,p) -> v.port_id = p
          ) ;
          (*f_label*)
          (fun u v -> u.label = v.label)
         |]

      let id u = u.ag_id
      let rename i u = {u with ag_id = i}

      let get_structure u = function
	| 0 -> u.port_id
	| 1 -> u.label
	| _ -> raise Not_found

      let fold_structure f u cont = f 1 u.label (f 0 u.port_id cont)

      let compatible u v =
        try
          fold_structure (fun i _ b ->
		     assert (arity > i) ;
		     try
		       if structure_preserving.(i) u v then b
		       else raise Exit
		     with
		       Not_found -> raise Exit
		    ) u true
        with
          Exit -> false

      let gluable u v = (*same id, same label and different ports*)
        (id u = id v) && (structure_preserving.(0) u v) && (u.port_id <> v.port_id)

      let compare u v = Pervasives.compare (u.ag_id,u.port_id) (v.ag_id,v.port_id)

      let create l =
	match l with
	  [i;p;l] -> {ag_id = i ; port_id = p ; label = l}
	| _ -> failwith "Cannot parse node"


      let to_string u =
	(string_of_int u.ag_id)^"."^(string_of_int (u.port_id))

      let to_dot u i =
	let ref_node = string_of_int i in
	ref_node^" [label=\""^(string_of_int (id u))^"\"]"

      let dot_of_edge u i v j =
	let tl = string_of_int u.port_id in
	let hl = string_of_int v.port_id in
	Printf.sprintf "%d->%d [dir = none, taillabel = \"%s\", headlabel = \"%s\"]" i j tl hl


      let coh edges (w,x) =
	let ok u v =
	  if u.ag_id = v.ag_id then ((u.port_id != v.port_id) && (u.label = v.label))
	  else true
	in
	List.for_all
	  (fun (u,v) ->
	   ok u x && ok v x && ok u w && ok v w && ok w x
	  ) edges

      let library =
	let void = [] in
	let house =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([1;1;0],[2;1;0]) ;
	    ([2;0;0],[3;0;0]) ;
	    ([3;1;0],[0;1;0]) ;
	    ([3;2;0],[4;0;1]) ;
	    ([4;1;1]),[2;2;0]
	  ]
	in
	let square =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([1;1;0],[2;1;0]) ;
	    ([2;0;0],[3;0;0]) ;
	    ([3;1;0],[0;1;0])
	  ]
	in
	let osquare =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([0;1;0],[3;1;0]) ;
	    ([1;1;0],[2;1;0]) ;
	  ]
	in
        let dsquare =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([1;1;0],[2;1;0]) ;
	    ([2;0;0],[3;0;0]) ;
	    ([3;1;0],[0;1;0]) ;
            ([3;2;0],[1;2;0]) ;
	  ]
	in
	let triangle =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([0;2;0],[2;0;0]) ;
	    ([2;1;0],[1;2;0])
	  ]
	in
	let one = [([0;0;0],[1;0;0])] in
        let two = [([0;0;0],[1;0;0]);([2;0;0],[1;1;0])] in
	let tn = List.map (fun (l,l') -> (create l,create l'))
	in
	let lib = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	let lib = Lib.StringMap.add "house" (tn house) lib
	in
	let lib = Lib.StringMap.add "square" (tn square) lib
	in
        let lib = Lib.StringMap.add "osquare" (tn osquare) lib
	in
	let lib = Lib.StringMap.add "dsquare" (tn dsquare) lib
	in
	let lib = Lib.StringMap.add "one" (tn one) lib in
	let lib = Lib.StringMap.add "two" (tn two) lib in
	Lib.StringMap.add "triangle" (tn triangle) lib

    end:NodeType)


module KappaNode =
  (struct
      type t = {ag_id : int ; port_id : int ; label : int}

      let arity = 2
      let structure_preserving = [|
          (*f_port*)
          (fun u v -> u.port_id = v.port_id) ;
          (*f_label*)
          (fun u v -> u.label = v.label)
         |]

      let id u = u.ag_id
      let rename i u = {u with ag_id = i}

      let get_structure u = function
	| 0 -> u.port_id
	| 1 -> u.label
	| _ -> raise Not_found

      let fold_structure f u cont = f 1 u.label (f 0 u.port_id cont)

      let compatible u v =
        try
          fold_structure (fun i _ b ->
		          assert (arity > i) ;
		          try
		            if structure_preserving.(i) u v then b
		            else raise Exit
		          with
		            Not_found -> raise Exit
		         ) u true
        with
          Exit -> false

      let gluable u v = (*same id, same label and different ports*)
        (id u = id v) && (u.label = v.label) && (u.port_id <> v.port_id)

      let compare u v = Pervasives.compare (u.ag_id,u.port_id) (v.ag_id,v.port_id)

      let create l =
	match l with
	  [i;p;l] -> {ag_id = i ; port_id = p ; label = l}
	| _ -> failwith "Cannot parse node"


      let to_string u =
	(string_of_int u.ag_id)^"."^(string_of_int (u.port_id))

      let to_dot u i =
	let ref_node = string_of_int i in
	ref_node^" [label=\""^(string_of_int u.label)^"\"]"

      let dot_of_edge u i v j =
	let tl = string_of_int u.port_id in
	let hl = string_of_int v.port_id in
	Printf.sprintf "%d->%d [dir = none, taillabel = \"%s\", headlabel = \"%s\"]" i j tl hl


      let coh edges (w,x) =
	let ok u v =
	  if u.ag_id = v.ag_id then ((u.port_id != v.port_id) && (u.label = v.label))
	  else true
	in
	List.for_all
	  (fun (u,v) ->
	   ok u x && ok v x && ok u w && ok v w && ok w x
	  ) edges

      let library =
	let void = [] in
	let house =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([1;1;0],[2;1;0]) ;
	    ([2;0;0],[3;0;0]) ;
	    ([3;1;0],[0;1;0]) ;
	    ([3;2;0],[4;0;1]) ;
	    ([4;1;1]),[2;2;0]
	  ]
	in
	let square =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([1;1;0],[2;1;0]) ;
	    ([2;0;0],[3;0;0]) ;
	    ([3;1;0],[0;1;0])
	  ]
	in
	let osquare =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([0;1;0],[3;1;0]) ;
	    ([1;1;0],[2;1;0]) ;
	  ]
	in
        let dsquare =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([1;1;0],[2;1;0]) ;
	    ([2;0;0],[3;0;0]) ;
	    ([3;1;0],[0;1;0]) ;
            ([3;2;0],[1;2;0]) ;
	  ]
	in
	let triangle =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([0;2;0],[2;0;0]) ;
	    ([2;1;0],[1;2;0])
	  ]
	in
	let one = [([0;0;0],[1;0;0])] in
        let two = [([0;0;0],[1;0;0]);([2;0;0],[1;1;0])] in
	let tn = List.map (fun (l,l') -> (create l,create l'))
	in
	let lib = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	let lib = Lib.StringMap.add "house" (tn house) lib
	in
	let lib = Lib.StringMap.add "square" (tn square) lib
	in
        let lib = Lib.StringMap.add "osquare" (tn osquare) lib
	in
	let lib = Lib.StringMap.add "dsquare" (tn dsquare) lib
	in
	let lib = Lib.StringMap.add "one" (tn one) lib in
	let lib = Lib.StringMap.add "two" (tn two) lib in
	Lib.StringMap.add "triangle" (tn triangle) lib

    end:NodeType)

module DegreeNode =
  (struct
      type t = {id : int ; max_degree : int}

      let arity = 1
      let structure_preserving = [|fun u v -> u.max_degree <= v.max_degree|]

      let id u = u.id

      let rename i u = {u with id = i}

      let get_structure = fun u i -> if i = 0 then u.max_degree else raise Not_found

      let fold_structure f u cont = f 0 u.max_degree cont

      let compatible u v =
        try
          fold_structure (fun i _ b ->
		     assert (arity > i) ;
		     try
		       if structure_preserving.(i) u v then b
		       else raise Exit
		     with
		       Not_found -> raise Exit
		    ) u true
        with
          Exit -> false

      let gluable u v = (*same id, same label and different ports*)
        (id u = id v) && (u.max_degree = v.max_degree)


      let compare u v = Pervasives.compare u.id v.id

      let create l =
	match l with
	  [i;d] -> {id = i ; max_degree = d}
	| _ -> failwith "Cannot parse node"

      let to_string u =
	"["^(string_of_int u.id)^";"^(string_of_int (u.max_degree))^"]"

      let to_dot u i =
	let ref_node = string_of_int i in
	ref_node^" [label=\""^(string_of_int (id u))^"\"]"

      let dot_of_edge u i v j =
	Printf.sprintf "%d->%d [dir = none]" i j

      let coh edges (w,x) =
	let dw,dx =
	  List.fold_left
	    (fun (dw,dx) (u,v) ->
	     let dw = if (u.id = w.id) || (v.id=w.id) then dw+1 else dw in
	     let dx = if (u.id = x.id) || (v.id=x.id) then dx+1 else dx in
	     (dw,dx)
	    ) (1,1) edges
	in
	(dw <= w.max_degree) && (dx <= x.max_degree)

      let library =
	let void = [] in
	let house =
	  [
	    ([0;2],[1;2]) ;
	    ([1;2],[2;3]) ;
	    ([2;3],[3;3]) ;
	    ([3;3],[0;2]) ;
	    ([3;3],[4;2]) ;
	    ([2;3],[4;2])
	  ]
	in
	let square =
	  [
	    ([0;2],[1;2]) ;
	    ([1;2],[2;3]) ;
	    ([2;3],[3;3]) ;
	    ([3;3],[0;2]) ;
	  ]
	in
        let dsquare =
          [
	    ([0;3],[1;2]) ;
	    ([1;2],[2;3]) ;
	    ([2;3],[3;2]) ;
	    ([3;2],[0;3]) ;
	    ([0;3],[2;3]) ;
	  ]
	in
        let osquare =
	  [
	    ([0;3],[1;2]) ;
	    ([0;3],[2;3]) ;
	    ([2;3],[3;2]) ;
	  ]
	in
	let triangle =
	  [
	    ([0;3],[1;3]) ;
	    ([1;3],[2;2]) ;
	    ([0;3],[2;2])
	  ]
	in
	let one = [([0;3],[1;3])]
	in
        let tn = List.map (fun (l,l') -> (create l,create l'))
	in
	let lib = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	let lib = Lib.StringMap.add "house" (tn house) lib
	in
	let lib = Lib.StringMap.add "square" (tn square) lib
	in
        let lib = Lib.StringMap.add "osquare" (tn osquare) lib
	in
	let lib = Lib.StringMap.add "dsquare" (tn dsquare) lib
	in
	let lib = Lib.StringMap.add "one" (tn one) lib in
        Lib.StringMap.add "triangle" (tn triangle) lib
end:NodeType)
