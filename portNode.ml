module type SymT =
  sig
    val compatible : int -> int -> int -> int -> bool
    val info : string
  end

module Make (Symmetry:SymT) =
  (struct
    type t = {ag_id : int ; port_id : int ; label : int}
    let arity = 2

    let info = Symmetry.info

    let id u = u.ag_id
    let rename i u = {u with ag_id = i}

    let compatible u v = Symmetry.compatible u.label u.port_id v.label v.port_id

    let gluable u v = (*same id, same label and different ports*)
      (id u = id v) && compatible u v

    let compare u v =
      let cmp i j =
        if i=j then 0
        else if i<j then -1
        else 1
      in
      let c = cmp u.ag_id v.ag_id in
      if c=0 then cmp u.port_id v.port_id
      else c
             (*Pervasives.compare (u.ag_id,u.port_id) (v.ag_id,v.port_id)*)

    let create l =
      match l with
	[i;p;l] -> {ag_id = i ; port_id = p ; label = l}
      | _ -> failwith "Cannot parse node"

    let to_string u =
      (string_of_int u.ag_id)^"."^(string_of_int (u.port_id))

    let to_dot u ?(highlight=None) i =
      let ref_node = string_of_int i in
      ref_node^" [label=\""^(string_of_int (id u))^"\" "^(Lib.Util.hi2str highlight)^"]"

      let dot_of_edge u i v j =
	let tl = string_of_int u.port_id in
	let hl = string_of_int v.port_id in
	Printf.sprintf "%d->%d [dir = none, taillabel = \"%s\", headlabel = \"%s\"]" i j tl hl

	let tn = List.map (fun (l,l') -> (create l,create l'))

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
	    ([0;2;0],[2;0;1]) ;
	    ([2;1;1],[1;2;0])
	  ]
	in
	let one = [([0;0;0],[1;0;0])] in
        let two = [([0;0;0],[1;0;0]);([2;0;0],[1;1;0])] in
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

    end:Node.NodeType)


module KappaNode =
  Make (struct let compatible = fun l p l' p' -> l=l' && p=p' let info = "Kappa Graphs" end)

module KappaNode01 = (*ports 0 and 1 of all agents are equivalent*)
  Make
    (struct
      let compatible = fun l p l' p' ->
        l=l' &&
          if p = 0 || p=1 then p'=0 || p'=1
          else p=p'
      let info = "Kappa Graphs (0~1)"
    end)

(*all ports of the same agents are equivalent!*)
module DegreeNode =
  Make (struct let compatible = fun l _ l' _ -> (l=l') let info = "Port Graphs" end)
