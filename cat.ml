
module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)

    module NodeSet = Set.Make (Node)
			     			      
    exception Undefined		
    type embeddings = {src : Graph.t ; trg : Graph.t ; maps : Hom.t list}
    type tile = {span : embeddings * embeddings ; cospan : (embeddings * embeddings) option}

		  
    let inf_of_tile tile =
      let (emb,_) = tile.span in emb.src

				   
    let sup_of_tile tile =
      match tile.cospan with
	None -> None
      | Some (emb,_) -> Some emb.trg

    let left_of_tile tile = 
      let (emb,_) = tile.span in
      emb.trg
	
    let right_of_tile tile = 
      let (_,emb') = tile.span in
      emb'.trg
	
    let is_span emb1 emb2 =
      Graph.is_equal emb1.src emb2.src
		     
    let is_co_span emb1 emb2 =
      Graph.is_equal emb1.trg emb2.trg
		     
    let string_of_embeddings emb = 
      "\027[91m"^(String.concat " + " (List.map Hom.to_string emb.maps))^"\027[0m"

    let string_of_span (emb,emb') =
      assert (is_span emb emb') ;
      let str = Printf.sprintf " %s " (Graph.to_string emb.src) in
      let str' = Printf.sprintf " %s " (Graph.to_string emb.trg) in
      let str'' = Printf.sprintf " %s " (Graph.to_string emb'.trg) in
      str'^"<-"^(string_of_embeddings emb)^"-"^str^"-"^(string_of_embeddings emb')^"->"^str''^"\n"
												

    let string_of_co_span (emb,emb') =
      assert (is_co_span emb emb') ;
      let str = Printf.sprintf " %s " (Graph.to_string emb.trg) in
      let str' = Printf.sprintf " %s " (Graph.to_string emb.src) in
      let str'' = Printf.sprintf " %s " (Graph.to_string emb'.src) in
      str'^"-"^(string_of_embeddings emb)^"->"^str^"<-"^(string_of_embeddings emb')^"-"^str''^"\n"

    let string_of_tile tile = 
      match tile.cospan with
	None -> (string_of_span tile.span)^"\n[NO_SUP]"
      | Some co_span ->
	 (string_of_co_span co_span)^"\n"^(string_of_span tile.span)
												
												
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

    let embed g h = 
      match g=>h with
	[] -> raise Undefined
      | maps -> {src = g ; trg = h ; maps = maps}

    let identity g h =
      {src = g ; trg = h ; maps = [Hom.identity (Graph.nodes g)]}

    let horizontal_compose emb emb' = 
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
	       ) [] emb'.maps
	   in
	   hom_added@maps
	  ) [] emb.maps
      in
      if maps = [] then raise Undefined
      else
	let src = Graph.join emb.src emb'.src in
	let trg = Graph.join emb.trg emb'.trg in
	{src = src ; trg = trg ; maps = maps}	

    let vertical_compose emb emb' =
      let maps =
	List.fold_left
	  (fun maps hom ->
	   let hom_ext_list = 
	     List.fold_left 
	       (fun maps hom' ->
		try
		  (Hom.compose hom hom')::maps
		with
		  Hom.Not_injective -> maps
	       ) maps emb'.maps
	   in
	   hom_ext_list@maps
	  ) [] emb.maps
      in
      if maps = [] then raise Undefined
      else
	{src = emb.src ; 
	 trg = emb'.trg ; 
	 maps = maps}
      	  

    let eq_class matching emb auto =
      let close_span hom hom' =
	try
	  Hom.fold (fun u v phi ->
		    assert (Hom.mem u hom') ; 
		    let v' = Hom.find u hom' in
		    Hom.add v v' phi
		   ) hom Hom.empty
	with
	  Hom.Not_structure_preserving | Hom.Not_injective -> failwith "Invariant violation"
      in
      let close_co_span hom hom' =
	try
	  Hom.fold (fun u v phi ->
		    assert (Hom.comem v hom') ; 
		    let u' = Hom.cofind v hom' in
		    Hom.add u u' phi
		   ) hom Hom.empty
	with
	  Hom.Not_structure_preserving | Hom.Not_injective -> failwith "Invariant violation"
      in
      let reduced_maps = 
	List.fold_left
	  (fun quotient hom ->
	   if List.exists (fun hom' ->
			   (Hom.is_equal hom hom') ||
			     let phi =
			       if matching then close_co_span hom hom'
			       else close_span hom hom'
			     in
			     List.exists (fun psi -> Hom.is_sub phi psi) auto
			  ) quotient
	   then quotient
	   else hom::quotient
	  ) []
	  (List.fast_sort (*keeping identity morphisms if possible*)
	     (fun hom hom' ->
	      if Hom.is_identity hom then -1 else
		if Hom.is_identity hom' then 1
		else 0
	     ) emb.maps
	  )
      in
      assert (reduced_maps <> []) ;
      {emb with maps = reduced_maps}
	
    let extension_class emb =
      let auto = (emb.trg => emb.trg) in
      eq_class false emb auto
	       
    let matching_class emb =
      let auto = (emb.src => emb.src) in
      eq_class true emb auto
	       
    let flatten emb =
      let src = emb.src in
      let trg = emb.trg in
      List.fold_left
	(fun emb_list hom ->
	 {src = src ; trg = trg ; maps = [hom]}::emb_list
	) [] emb.maps
	       
    let mpo (emb_h,emb_g) =
      assert (match emb_h.maps with [id] -> Hom.is_identity id | _ -> false) ;
      let h,g = emb_h.trg,emb_g.trg in
      let inf_gh = emb_h.src in
      let to_h = List.hd emb_h.maps in
      let fresh = (Graph.max_id g) + 1 in
      List.fold_left
	(fun tiles to_g ->
	 try
	   let h',h_to_h',_ =
	     Graph.fold_edges
	       (fun u v (h',h_to_h',fresh) ->
		let map u h' h_to_h' fresh =
		  if Graph.has_node u inf_gh then
		    let u' = Hom.find u to_g in
		    (u',Graph.add_node u' h',Hom.add u u' h_to_h',fresh)
		  else
		    if Hom.comem_sub (Node.id u) to_h then
		      let j = Hom.find_sub (Node.id u) to_g in
		      let u' = Node.rename j u in
		      if Graph.has_node u' g then raise Graph.Incoherent (*Not a pullback*)
		      else
			(u', Graph.add_node u' h', Hom.add u u' h_to_h',fresh)
		    else
		      let i,fresh = try (Hom.find_sub (Node.id u) h_to_h',fresh) with Not_found -> (fresh,fresh+1)
		      in
		      let u' = Node.rename i u in
		      (u', Graph.add_node u' h', Hom.add u u' h_to_h',fresh)
		in
		let (u',h',h_to_h',fresh) = map u h' h_to_h' fresh in
		let (v',h',h_to_h',fresh) = map v h' h_to_h' fresh in
		(Graph.add_edge u' v' h',h_to_h',fresh)
	       ) h (Graph.empty,Hom.empty,fresh)
	   in
	   let sup_gh = Graph.join h' g in
	   let emb_h_to_sup = {src = h ; trg = sup_gh ; maps = [h_to_h']} in
	   let emb_g_to_sup = extension_class (embed g sup_gh)
	   in
	   let emb_g = {src = inf_gh ; trg = g ; maps = [to_g]} in
	   let new_tiles =
	     List.fold_left
	       (fun tiles emb_g_to_sup ->
		{span = (emb_h,emb_g) ; cospan = Some (emb_h_to_sup,emb_g_to_sup)}::tiles
	       ) [] (flatten emb_g_to_sup)
	   in
	   new_tiles@tiles
	 with
	   Graph.Incoherent ->
	   let emb_g = {src = inf_gh ; trg = g ; maps = [to_g]} in
	   {span = (emb_h,emb_g) ; cospan = None}::tiles
	) [] emb_g.maps
	
(*	
    let multi_pushout maps g1 g2 = (*maps: infG1G2 -> G2*)
      
      let extend_partial hom0 graph fresh =
	let apply_ext_hom u hom fresh =
	  match Hom.id_image u hom with
	    None ->
	    let u' = Node.rename fresh u in
	    (u', Hom.add u u' hom, fresh+1)
	  | Some i -> 
	     let u' = Node.rename i u in
	     (u',Hom.add u u' hom,fresh)
	in
	let renamed_opt,hom,_ = 
	  Graph.fold_edges
	    (fun u v (renamed_opt,hom,fresh) ->
	     let subst_opt,hom =
	       try
		 let u',hom,fresh = apply_ext_hom u hom fresh
		 in
		 let v',hom,fresh = apply_ext_hom v hom fresh
		 in
		 (Some (u',v',fresh),hom)
	       with
		 Hom.Not_injective -> (None,hom)
	     in
	     match (renamed_opt,subst_opt) with
	       (None, Some (u',v',fresh)) -> (None,hom,fresh)
	     | (_, None) -> (None,hom,fresh)
	     | (Some renamed_graph, Some (u',v',fresh)) ->
		begin
		  let renamed_graph = Graph.add_node u' (Graph.add_node v' renamed_graph) in
		  let renamed_graph =
		    try
		      Graph.add_edge u' v' renamed_graph
		    with
		      Graph.Incoherent ->
		      (
			Printf.printf "Cannot add (%s,%s)\n" (Node.to_string u') (Node.to_string v') ;
			failwith "Invariant violation"
		      )
		  in
		  (Some renamed_graph,hom,fresh)
		end		
	    ) graph (Some Graph.empty,hom0,fresh)
	in
	(hom,renamed_opt)
      in
      
      let fresh = (max (Graph.max_id g1) (Graph.max_id g2))+1
      in
      List.map
	(fun hom ->
	 let hom,renamed_opt =
	   extend_partial hom g1 fresh
	 in
	 match renamed_opt with
	   None -> (None,hom)
	 | Some renamed_g1 ->
	    try
	      let gh_sup = Graph.join g2 renamed_g1
	      in
	      (Some gh_sup,hom)
	    with
	      Graph.Incoherent -> (None,hom)
	) maps
 *)	 
    	
    let (><) g h =
      (*one_gluings: embeddings of one edge of h into g, partial_gluings: embeddings of n edges of h into g*)
      let rec enumerate_gluings one_gluings partial_gluings complete_gluings already_done =
	match partial_gluings with
	  [] -> complete_gluings
	| (n_gluing)::tl ->
	   let succ_n_gluings,complete_gluings',already_done' = 
	     List.fold_left
	       (fun (succ_n_gluings,complete_gluings,already_done) one_gluing ->
		try
		  if Graph.is_included one_gluing.src n_gluing.src then (succ_n_gluings,complete_gluings,already_done)
		  else
		    match try Some (horizontal_compose one_gluing n_gluing) with Undefined -> None
		    with
		      None -> (succ_n_gluings,complete_gluings,already_done)
		    | Some succ_n_emb -> (*defines an n+1 gluing*)
		       (*On verifie ici que succ_n_hset n'est pas deja dans succ_n_gluings*)
		       if List.exists
			    (fun emb ->
			     Graph.is_equal emb.src succ_n_emb.src
			    ) already_done
		       then (succ_n_gluings,complete_gluings,already_done)
		       else
			 let complete_gluings' = succ_n_emb::complete_gluings in
			 (succ_n_emb::succ_n_gluings,complete_gluings', succ_n_emb::already_done)
		with
		  Hom.Not_structure_preserving -> failwith "Invariant violation: not structure preserving"
		| Hom.Not_injective -> (succ_n_gluings,complete_gluings,already_done)
	       ) ([],complete_gluings,already_done) one_gluings
	   in
	   enumerate_gluings one_gluings (tl@succ_n_gluings) complete_gluings' already_done'
      in
      let subgraphs_of_edges graph =
	try
	  Graph.fold_edges
	    (fun u v subgraphs ->
	     let subg = Graph.add_node u (Graph.add_node v Graph.empty) in
	     (Graph.add_edge u v subg)::subgraphs
	    ) graph []
	with
	  Graph.Incoherent -> failwith "Invariant violation: graph is incoherent"
      in
      let one_gluings = 
	List.fold_left
	  (fun arr_list subh ->
	   try 
	     let embeddings = embed subh g 
	     in
	     embeddings::arr_list
	   with
	     Undefined -> arr_list
	  ) [] (subgraphs_of_edges h)
      in
      let gluing_points = enumerate_gluings one_gluings one_gluings one_gluings [] in
      let spans =
	List.fold_left
	  (fun spans emb ->
	   let to_h = identity emb.src h in 
	   let to_g = extension_class emb in
	   (to_h,to_g)::spans
	  ) [] gluing_points
      in
      (***)
      print_string "Gluings:\n" ;
      List.iter (fun span -> print_string (string_of_span span) ; print_newline()) spans ;
      (***)
      let mpos =
	List.fold_left
	  (fun tiles span ->
	   (mpo span)@tiles
	  ) [] spans
      in
      (***)
      print_string "Multi pushouts:\n" ;
      List.iter (fun tile -> print_string (string_of_tile tile) ; print_newline()) mpos ;
      (***)
      
      List.fold_left
	(fun cont tile ->
	 let is_max infGH mpos = (*checks whether infGH is not included in the inf of another tile*)
	   try
	     (List.fold_left
		(fun _ tile ->
		 if (Graph.size_edge infGH < Graph.size_edge (inf_of_tile tile))
		    && (Graph.is_included infGH (inf_of_tile tile))
		 then raise Pervasives.Exit
		) () mpos ; true)
	   with
	     Pervasives.Exit -> false
	 in
	 match sup_of_tile tile with
	   None -> if is_max (inf_of_tile tile) mpos then tile::cont else cont
	   | Some _ -> tile::cont
	) [] mpos

    let minimize_tile tile min_opt =
      let size_src = Graph.size_edge (inf_of_tile tile) in
      List.fold_left
	(fun sharings tile' ->
	 let size_src' = Graph.size_edge (inf_of_tile tile') in
	 if
	   match min_opt with
	     None -> true
	   | Some n ->  (size_src' - size_src) >= n
	 then
	   let sharing =
	     {src = inf_of_tile tile ;
	      trg = inf_of_tile tile' ;
	      maps = [Hom.identity (Graph.nodes (inf_of_tile tile))]
	     }
	   in
	   (sharing,tile')::sharings
	 else
	   sharings
	) []  ((left_of_tile tile) >< (right_of_tile tile))
        
	
  end
