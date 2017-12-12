
module Make (SiteEquivalence:Homology) =
  (struct
      type t = {ag_id : int ; port_id : int ; label : int}

      let arity = 2
      let structure = [|
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
		       let f_i = structure.(i) in
		       if f_i u v then b
		       else raise Exit
		     with
		       Not_found -> raise Exit
		    ) u true
        with
          Exit -> false


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

  end):Node.NodeType
