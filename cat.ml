  
module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)

    module NodeSet = Set.Make (Node)
			      
    type arrows = {src : Graph.t ; auto_src : Hom.t list ; maps : Hom.t list ; trg : Graph.t; auto_trg : Hom.t list}
    type graph = Graph.t

		   
    let to_string cat =
      String.concat "," (List.map Hom.to_string cat.maps)
		    
		    
    let (=>) g h =
      let rec extend hom_list iG jG acc =
	match hom_list with
	  [] -> acc
	| phi::tl ->
	   try
	     let iH = Hom.find iG phi in
	     let opt = try Some (Hom.find jG phi) with Not_found -> None in
	     match opt with
	       None ->
	       let biH = Graph.bound_to iH h in
	       let ext =
		 List.fold_left
		   (fun cont jH ->
		    try
		      let phi_ext = Hom.add jG jH phi in
		      phi_ext::cont
		    with
		      Hom.Not_injective | Hom.Not_structure_preserving -> cont
		   ) [] biH
	       in
	       extend tl iG jG (ext@acc)
	     | Some jH ->
		if Graph.has_edge iH jH h then extend tl iG jG (phi::acc)
		else extend tl iG jG acc
	   with Not_found -> failwith "Invariant violation" 
      in
      let rec explore_cc i hom_list already_done =
	List.fold_left
	  (fun (hom_list,already_done) j ->
	   let hom_list' = extend hom_list i j [] in
	   if NodeSet.mem j already_done then
	     (hom_list',already_done)
	   else
	     explore_cc j hom_list' (NodeSet.add j already_done)
	  ) (hom_list,already_done) (Graph.bound_to i g) 
      in
      let extend_next_root u hom_list g h =
	List.fold_left (fun hom_list hom ->
			let fold_candidates_u =
			  match Hom.id_image u hom with
			    None -> (*if [Node.id u] is not yet constrained by [hom]*)
			    (fun f -> Graph.fold_nodes f h) 
			  | Some i -> (*Looking for a candidate among those having [hom (Node.id u)] as id*)
			     (fun f -> List.fold_right f (Graph.nodes_of_id i h)) 
			in
			let hom_extended_with_candidates_u =
			  fold_candidates_u 
			    (fun u' cont ->
			     if (Graph.degree u g) <= (Graph.degree u' h) then
			       try
				 (Hom.add u u' hom)::cont
			       with
				 Hom.Not_structure_preserving | Hom.Not_injective -> cont
			     else
			       cont
				 
			    ) []
			in
			hom_extended_with_candidates_u@hom_list
		       ) [] hom_list
      in
      
      let cc_roots = Graph.connected_components g in
      List.fold_left
	(fun hom_list u ->
	 let hom_list_u = extend_next_root u hom_list g h in
	 let hom_list_extended,_ = explore_cc u hom_list_u (NodeSet.singleton u) in
	 hom_list_extended
	) [Hom.empty] cc_roots

    let eq_class arrows dmem dfind dauto =
      let close_diagram hom hom' =
	try
	  Hom.fold (fun u v phi ->
		    assert (dmem u hom') ; 
		    let v' = dfind u hom' in
		    Hom.add v v' phi
		   ) hom Hom.empty
	with
	  Hom.Not_structure_preserving | Hom.Not_injective -> failwith "Invariant violation"
      in
      let reduced_maps = 
	List.fold_left
	  (fun extensions hom ->
	   if List.exists (fun hom' ->
			   (Hom.is_equal hom hom') ||
			     let phi = close_diagram hom hom' in
			     List.exists (fun psi -> Hom.is_sub phi psi) dauto
			  ) extensions
	   then extensions
	   else hom::extensions
	  ) []
	  (List.fast_sort (*keeping identity morphisms if possible*)
	     (fun hom hom' ->
	      if Hom.is_identity hom then -1 else
		if Hom.is_identity hom' then 1
		else 0
	     ) arrows.maps
	  )
      in
      {arrows with maps = reduced_maps}
	
    let extension_class arrows =
      let dmem = Hom.mem in
      let dfind = Hom.find in
      let dauto = arrows.auto_trg in
      eq_class arrows dmem dfind dauto

    let matching_class arrows =
      let dmem = Hom.comem in
      let dfind = Hom.cofind in
      let dauto = arrows.auto_src in
      eq_class arrows dmem dfind dauto

    let create g h =
      {src = g ;
       auto_src = (g => g) ;
       maps = (g => h) ;
       trg = h ;
       auto_trg = (h => h)}
      
    let tensor arrows arrows' =
      let src = Graph.join arrows.src arrows'.src in
      let trg = Graph.join arrows.trg arrows'.trg in
      let auto_src = src => src in
      let auto_trg = trg => trg in
      let maps =
	List.fold_left
	  (fun maps hom ->
	   let hom_added =
	     List.fold_left
	       (fun hom_added hom' ->
		try
		  (Hom.sum hom hom')::hom_added
		with
		  Hom.Not_structure_preserving | Hom.Not_injective -> hom_added
	       ) [] arrows'.maps
	   in
	   hom_added@maps
	  ) [] arrows.maps
      in
      {src = src ; trg = trg ; auto_src = auto_src ; auto_trg = auto_trg ; maps = maps}

    let multi_pushout maps g h =
      let extend_partial hom g fresh =
	let apply_ext_hom u hom fresh =
	  match Hom.id_image u hom with
	    None ->
	    let u' = Node.rename fresh u in
	    (u', Hom.add u u' hom, fresh+1)
	  | Some i -> 
	     try (Hom.find u hom,hom,fresh)
	     with Not_found ->
	       let u' = Node.rename i u in
	       (u',Hom.add u u' hom,fresh)
	in
	let g',hom',_ = 
	  Graph.fold_edges
	    (fun u v (homg,hom,fresh) ->
	     let u',hom',fresh' = apply_ext_hom u hom fresh
	     in
	     let v',hom'',fresh'' = apply_ext_hom v hom' fresh'
	     in
	     let homg' = Graph.add_node u' (Graph.add_node v' homg) in
	     let homg'' =
	       try
		 Graph.add_edge u' v' homg'
	       with
		 Graph.Incoherent ->
		 (
		   Printf.printf "Cannot add (%s,%s)\n" (Node.to_string u') (Node.to_string v') ;
		   failwith "Invariant violation"
		 )
	     in
	     (homg'',hom'',fresh'')
	  ) g (Graph.empty,hom,fresh)
	in
	(hom',g')
      in
      let fresh = (max (Graph.max_id g) (Graph.max_id h))+1
      in
      List.map
	(fun hom ->
	 let hom',g' = extend_partial hom g fresh in
	 try
	   let gh_sup = Graph.join g' h
	   in
	   (Some gh_sup,hom')
	 with
	   Graph.Incoherent -> (None,hom')
	 | Hom.Not_injective | Hom.Not_structure_preserving ->
				failwith "Invariant violation: cannot build homomorphism"
	) maps
	
    	
    let gluings g h =
      let rec enumerate_gluings one_gluings partial_gluings complete_gluings already_done =
	match partial_gluings with
	  [] -> complete_gluings
	| n_gluing::tl ->
	   let succ_n_gluings,complete_gluings',already_done' = 
	     List.fold_left
	       (fun (succ_n_gluings,complete_gluings,already_done) one_gluing ->
		try
		  let src_1 = one_gluing.src in
		  let src_n = n_gluing.src in
		  if Graph.is_included src_1 src_n then (succ_n_gluings,complete_gluings,already_done)
		  else
		    let succ_n_arrows = tensor one_gluing n_gluing
		    in
		    (*On verifie ici que succ_n_arrows n'est pas deja dans succ_n_gluings*)
		    if List.exists
			 (fun g ->
			  Graph.is_equal g succ_n_arrows.src
			 ) already_done
		    then (succ_n_gluings,complete_gluings,already_done)
		    else
		      let complete_gluings' = succ_n_arrows::complete_gluings in
		      (succ_n_arrows::succ_n_gluings,complete_gluings',succ_n_arrows.src::already_done)
		with
		  Hom.Not_structure_preserving ->
		  failwith "Invariant violation: not structure preserving"
		| Hom.Not_injective -> (succ_n_gluings,complete_gluings,already_done)
	       ) ([],complete_gluings,already_done) one_gluings
	   in
	   enumerate_gluings one_gluings (tl@succ_n_gluings) complete_gluings' already_done'
      in
      let subgraphs_of_edges g =
	try
	  Graph.fold_edges
	    (fun u v subgraphs ->
	     let subg = Graph.add_node u (Graph.add_node v Graph.empty) in
	     (Graph.add_edge u v subg)::subgraphs
	    ) g []
	with
	  Graph.Incoherent -> failwith "Invariant violation: graph is incoherent"
      in
      let one_gluings = 
	List.fold_left
	  (fun arr_list subg ->
	   (create subg h)::arr_list
	  ) [] (subgraphs_of_edges g)
      in
      let gluings = 
	List.map extension_class (enumerate_gluings one_gluings one_gluings one_gluings [])
      in
      List.fold_left (fun cont arrows ->
		      let is_max subG =
			try
			  (List.fold_left
			    (fun _ arrows ->
			     if (Graph.size_edge subG < Graph.size_edge arrows.src)
				&& (Graph.is_included subG arrows.src)
			     then raise Pervasives.Exit
			    ) () gluings ; true)
			with
			  Pervasives.Exit -> false
		      in
		      let mpo = multi_pushout arrows.maps g h in
		      let subG = arrows.src in
		      let gluings =
			List.fold_left
			  (fun maps (sup_opt,hom) ->
			   match sup_opt with
			     None -> if is_max subG then (subG,g,h,hom,sup_opt)::maps else maps
			   | Some _ ->  (subG,g,h,hom,sup_opt)::maps
			  ) [] mpo
		      in
		      gluings@cont
		     ) [] gluings
	
  end
    
