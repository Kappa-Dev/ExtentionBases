
module Make (Node:Node.NodeType) =
  struct
    
    type node =  Node.t
    exception Incoherent

    module NodeSet = Set.Make(struct type t = node let compare = Node.compare end)
    module NodeMap = Map.Make(struct type t = node let compare = Node.compare end)

    type t =
      {nodes : NodeSet.t ;
       edges : (node list) NodeMap.t ;
       idmap : (node list) Lib.IntMap.t ;
       size : int }
	       
    let empty = {nodes = NodeSet.empty ; edges = NodeMap.empty ; idmap = Lib.IntMap.empty ; size = 0}

    		  
    let nodes_of_id i g = try Lib.IntMap.find i g.idmap with Not_found -> []		 

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
	  
    let add_edge u v g =
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
	if is_coherent then
	  let edges' = NodeMap.add u (v::bu) (NodeMap.add v (u::bv) g.edges) in
	  {g with edges = edges' ; nodes = g.nodes ; size = g.size+1}
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
				    
    let join g h =
      NodeMap.fold
	(fun u buG join ->
	 List.fold_left
	   (fun join v ->
	    let join = add_node u join in
	    let join = add_node v join in 
	    add_edge u v join
	   ) join buG 
	) g.edges h

   
	
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
      let cc_map,_ =
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
      let edges = fold_edges (fun (u:node) (v:node) cont -> (u,v)::cont) g []
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
      "{"^String.concat ","
		    (fold_edges
		       (fun u v cont ->
			(Printf.sprintf "(%s,%s)" (Node.to_string u) (Node.to_string v))::cont
		       ) g []
		    )^"}"
  end
    
