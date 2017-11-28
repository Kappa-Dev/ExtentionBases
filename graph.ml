module type GraphType =
  sig
    type t
    type node

    (**Constructors*)
    val empty : t
    val add_node : node -> t -> t
    val add_edge : ?weak:bool -> node -> node -> t -> t

    (**Pretty printing*)
    val to_string : t -> string
    val to_dot_cluster : ?sub:t -> t -> int -> int -> string * string * int

    (**Iterators*)
    val fold_edges : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a
    val fold_edge_types : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a
    val fold_nodes : (node -> 'a -> 'a) -> t -> 'a -> 'a

    (**Properties*)
    val bound_to : node -> t -> node list
    val has_edge : node -> node -> t -> bool
    val has_node : node -> t -> bool
    val nodes_of_id : int -> t -> node list
    val degree : node -> t -> int
    val nodes : t -> node list
    val connected_components : t -> node list
    val max_id : t -> int
    val size_edge : t -> int
    val size_node : t -> int
    val is_empty : t -> bool
    val is_equal : t -> t -> bool
    val is_connex : t -> bool

    (**Operators*)
    val join : ?weak:bool -> t -> t -> t
    val meet : t -> t -> t
    val sum : t -> t -> t
    val minus : t -> t -> t

    exception Incoherent
    val is_coherent : t -> bool
  end


module Make (Node:Node.NodeType) =
  (struct

    exception Incoherent

    module NodeSet = Set.Make(struct type t = Node.t let compare = Node.compare end)
    module NodeMap = Map.Make(struct type t = Node.t let compare = Node.compare end)

    type node = Node.t
    type t =
      {nodes : NodeSet.t ;
       edges : (Node.t list) NodeMap.t ;
       idmap : (Node.t list) Lib.IntMap.t ;
       size : int ;
       coherent : bool
      }

    let is_coherent g = g.coherent

    module EdgeSet = Set.Make(struct type t = Node.t * Node.t let compare = compare end)

    let empty = {nodes = NodeSet.empty ;
                 edges = NodeMap.empty ;
                 idmap = Lib.IntMap.empty ;
                 size = 0 ;
                 coherent = true}

    let is_empty g = g.size = 0

    let equal_support g h =
      try
	Lib.IntMap.fold
	  (fun id _ _ ->
	   if Lib.IntMap.mem id h.idmap then ()
	   else raise Pervasives.Exit
	  ) g.idmap () ;
	Lib.IntMap.fold
	  (fun id _ _ ->
	   if Lib.IntMap.mem id g.idmap then ()
	   else raise Pervasives.Exit
	  ) h.idmap () ; true
      with
	Pervasives.Exit -> false


    let nodes_of_id i g = try Lib.IntMap.find i g.idmap with Not_found -> []
    let nodes g = NodeSet.elements g.nodes

    let size_node g = NodeSet.cardinal g.nodes
    let size_edge g = g.size

    let fold_edges f g cont =
      NodeMap.fold
	(fun u bu cont ->
	 List.fold_left
	   (fun cont v ->
	    if Node.compare u v < 0 then (f u v cont)
	    else cont
	   ) cont bu
	) g.edges cont

    let fold_edge_types f g cont =
      let edge_types g =
        fold_edges
          (fun u v cont ->
           if List.exists (fun (w,x) -> Node.compatible u w && Node.compatible v x) cont then cont
           else
             (u,v)::cont
          ) g []
      in
      List.fold_left
        (fun cont (u,v) -> f u v cont) cont (edge_types g)


    let fold_nodes f g cont =
      NodeSet.fold
	(fun u cont ->
	 f u cont
	) g.nodes cont

    let bound_to u g =
      try NodeMap.find u g.edges with Not_found -> []

    let has_edge u v g =
      let bu = bound_to u g in
      List.mem v bu

    let has_node u g = NodeSet.mem u g.nodes

    let add_node u g =
      if has_node u g then g
      else
	let idmap' =
	  let l = nodes_of_id (Node.id u) g in
	  Lib.IntMap.add (Node.id u) (u::l) g.idmap
	in
	{g with nodes = NodeSet.add u g.nodes ; idmap = idmap'}

    let add_edge ?(weak=false) u v g =
      if has_edge u v g then g
      else
	let bu = bound_to u g in
	let bv = bound_to v g in
	let is_coherent =
	  let edges =
	    fold_edges
	      (fun u v cont ->
	       (u,v)::cont
	      ) g []
	  in
	  Node.coh edges (u,v)
	in
	if is_coherent || weak then
	  let edges' = NodeMap.add u (v::bu) (NodeMap.add v (u::bv) g.edges) in
	  {g with edges = edges' ;
                  nodes = g.nodes ;
                  size = g.size+1 ;
                  coherent = is_coherent && g.coherent}
	else
	  raise Incoherent

    let meet g h =
      try
	NodeMap.fold (fun u buG meet ->
		      try
			let buH = NodeMap.find u h.edges in
			let vGH = List.filter (fun v -> List.mem v buH) buG in
			List.fold_left (fun meet v ->
					let meet = add_node u meet in
					let meet = add_node v meet in
					add_edge u v meet
				       ) meet vGH
		      with
			Not_found -> meet
		     ) g.edges empty
      with
	Incoherent -> failwith "Invariant violation: meet operation is undefined"

    let join ?(weak=false) g h =
      NodeMap.fold
	(fun u buG join ->
	 List.fold_left
	   (fun join v ->
	    let join = add_node u join in
	    let join = add_node v join in
	    add_edge ~weak:weak u v join
	   ) join buG
	) g.edges h

    let minus g h =
	   fold_edges
	     (fun u v diff ->
	      if has_edge u v h then diff
	      else
		let diff = add_node u diff in
		let diff = add_node v diff in
		try add_edge u v diff with Incoherent -> failwith "Invariant violation"
	     ) g empty

    (*TODO: maintain max_id when adding a new node to the graph*)
    let max_id g =
      fold_nodes (fun u max -> if Node.id u > max then Node.id u else max) g 0

    let is_equal g h =
      if (size_node g = size_node h) && (size_edge g = size_edge h) then
	(fold_nodes (fun u b -> b && (has_node u h)) g true) &&
	  (fold_edges (fun u v b -> b && (has_edge u v h)) g true)
      else
	false

    let connected_components g =
      let ccmap,ccsize =
	fold_nodes
	  (fun u (ccmap,ccsize) ->
	   (NodeMap.add u u ccmap,NodeMap.add u 1 ccsize)
	  ) g (NodeMap.empty, NodeMap.empty)
      in
      let cc_map,cc_size =
	fold_edges
	  (fun i j (ccmap,ccsize) ->
	   let rep_i = NodeMap.find i ccmap in
	   let s_i = NodeMap.find rep_i ccsize in
	   let rep_j = NodeMap.find j ccmap in
	   let s_j = NodeMap.find rep_j ccsize in
	   let mn_size,mn_rep,mx_size,mx_rep =
	     if s_i < s_j then s_i,rep_i,s_j,rep_j else s_j,rep_j,s_i,rep_i in
	   let ccsize' = NodeMap.add mx_rep (mn_size+mx_size+1) ccsize in
	   let ccsize' = NodeMap.add mn_rep 0 ccsize' in
	   let ccmap' =
	     NodeMap.fold
	       (fun a b ccmap -> if b = mn_rep then NodeMap.add a mx_rep ccmap else ccmap
	       ) ccmap ccmap
	   in
	   (ccmap',ccsize')
	  ) g (ccmap,ccsize)
      in
      let _,cc =
	NodeMap.fold (fun u rep_u (visited,cc) ->
		      if NodeSet.mem rep_u visited then (visited,cc)
		      else
			(NodeSet.add rep_u visited, u::cc)
		     ) cc_map (NodeSet.empty,[])
      in
      cc

    let is_connex g =
      let rec iter cc = function
          [] -> cc
        | u::todo ->
           let cc',todo' =
             List.fold_left (fun (cc,todo) v ->
                 List.fold_left
                   (fun (cc,todo) v' ->
                     if NodeSet.mem v' cc then (cc,todo)
                     else (NodeSet.add v' cc,v'::todo)
                   ) (NodeSet.add v cc,if NodeSet.mem v cc then todo else v::todo)
                   (nodes_of_id (Node.id v) g)
               ) (NodeSet.add u cc,todo) (bound_to u g)
           in
           iter cc' todo'
      in
      NodeSet.cardinal (iter NodeSet.empty (nodes_of_id (max_id g) g)) = size_node g

    let subparts g =
      let rec enum edges subs =
	match edges with
	  [] -> subs
	| e::tl ->
	   let subs' =
	     List.fold_left (fun cont subpart -> subpart::((e::subpart)::cont)) [] subs
	   in
	   enum tl subs'
      in
      let edges = fold_edges (fun u v cont -> (u,v)::cont) g []
      in
      enum edges [[]]

    let degree u g = List.length (bound_to u g)

    let is_included g h =
      try
	fold_edges
	  (fun u v _ ->
	   if has_edge u v h then ()
	   else raise Pervasives.Exit
	  ) g () ;
	true
      with
	Pervasives.Exit -> false

    let to_string g =
      let str = String.concat ","
		    (fold_edges
		       (fun u v cont ->
			(Printf.sprintf "(%s,%s)" (Node.to_string u) (Node.to_string v))::cont
		       ) g [])
      in
      if is_coherent g then "{"^str^"}"
      else
        "{!!"^str^"!!}"

    let to_dot_cluster ?(sub=empty) g n fresh =
      let name = "cluster_"^(string_of_int n) in
      let nodes,fresh,map =
	fold_nodes
	  (fun u (cont,fresh,map) ->
	   if Lib.IntMap.mem (Node.id u) map then (cont,fresh,map)
	   else
	     let i = fresh in
	     let node_str = Node.to_dot u i in
	     (node_str::cont,fresh+1,Lib.IntMap.add (Node.id u) i map)
	  ) g ([],fresh,Lib.IntMap.empty)
      in
      let nodes = String.concat "\n" nodes in
      let edges =
	String.concat "\n"
		      (fold_edges
			 (fun u v cont ->
                          let edge_style =
                            if has_edge u v sub then "[color = red]" else ""
                          in
                          let edge_str =
			    let i = Lib.IntMap.find (Node.id u) map in
			    let j = Lib.IntMap.find (Node.id v) map in
			    Node.dot_of_edge u i v j
			  in
			  (edge_str^edge_style)::cont
			 ) g []
		      )
      in
      (Printf.sprintf "subgraph %s { \n label = \"%s\" %s \n %s \n }\n" name name nodes edges,name,fresh)

    let sum g h =
      let shift g d =
        fold_edges
          (fun u v g' ->
           let u',v' = Node.rename (d+(Node.id u)) u,Node.rename (d+(Node.id v)) v in
           let g' = add_node u' (add_node v' g') in
           add_edge u' v' g'
          ) h empty
      in
      join h (shift g ((max_id h)+1))
  end:GraphType with type node = Node.t)

