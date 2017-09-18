module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)

    module NodeSet = Set.Make (Node)

    exception Undefined
    type embeddings = {src : Graph.t ; trg : Graph.t ; maps : Hom.t list}
    type tile = {span : embeddings * embeddings ; cospan : (embeddings * embeddings) option}

    let is_domain_identity emb =
      List.for_all Hom.is_identity emb.maps

    let images g emb =
      List.fold_left
        (fun images hom ->
         let im =
	   Graph.fold_edges
	     (fun u v cod ->
	      let (u',v') = Hom.find2 (u,v) hom in
	      let cod = Graph.add_node u' (Graph.add_node v' cod) in
	      Graph.add_edge u' v' cod
	     ) g Graph.empty
	 in
	 im::images
        ) [] emb.maps

    let co_domains emb = images emb.src emb

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
      Lib.InOut.red (String.concat "+" (List.map Hom.to_string emb.maps))

    let dot_of_embeddings emb =
      let cluster0,ref_cluster0,fresh = Graph.to_dot_cluster emb.src 0 0 in
      let cluster1,ref_cluster1,_ = Graph.to_dot_cluster emb.trg 1 fresh in
      let arrows =
	String.concat ";\n"
		      (List.map (fun hom -> ref_cluster0^"->"^ref_cluster1^(Hom.to_dot_label hom)) emb.maps)
      in
      String.concat "\n" ["digraph G {\n";cluster0;cluster1;arrows;"}"]


    let string_of_span (emb,emb') =
      assert (is_span emb emb') ;
      let str = Printf.sprintf " %s " (Graph.to_string emb.src) in
      let str' = Printf.sprintf " %s " (Graph.to_string emb.trg) in
      let str'' = Printf.sprintf " %s " (Graph.to_string emb'.trg) in
      str'^"<-"^(string_of_embeddings emb)^"-"^str^"-"^(string_of_embeddings emb')^"->"^str''


    let string_of_co_span (emb,emb') =
      assert (is_co_span emb emb') ;
      let str = Printf.sprintf " %s " (Graph.to_string emb.trg) in
      let str' = Printf.sprintf " %s " (Graph.to_string emb.src) in
      let str'' = Printf.sprintf " %s " (Graph.to_string emb'.src) in
      str'^"-"^(string_of_embeddings emb)^"->"^str^"<-"^(string_of_embeddings emb')^"-"^str''

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
      let rename fresh h (to_h,inf_gh,to_g,g) =
	Graph.fold_edges
	  (fun u v (h',h_to_h',fresh) ->
	   let map u h' h_to_h' fresh =
	     try
	       let u0 = Hom.cofind u to_h in (*u is in the inf*)
	       let u' = Hom.find u0 to_g in
	       (u',Graph.add_node u' h',Hom.add u u' h_to_h',fresh)
	     with
	       Hom.Not_injective -> failwith "Invariant violation"
	     | Not_found -> (*u is not in the inf*)
		begin
		  try
		    let i0 = Hom.cofind_sub (Node.id u) to_h in
		    let j = Hom.find_sub i0 to_g in
		    let u' = Node.rename j u in
		    if Graph.has_node u' g then raise Graph.Incoherent (*Not a pullback*)
		    else
		      (u', Graph.add_node u' h', Hom.add u u' h_to_h',fresh)
		  with Not_found -> (*id u is not in the inf*)
		    if fresh < 0 then
		      (u,Graph.add_node u h', Hom.add u u h_to_h',fresh)
		    else
		      let i,fresh = try (Hom.find_sub (Node.id u) h_to_h',fresh) with Not_found -> (fresh,fresh+1)
		      in
		      let u' = Node.rename i u in
		      (u', Graph.add_node u' h', Hom.add u u' h_to_h',fresh)
		end
	   in
	   let (u',h',h_to_h',fresh) = map u h' h_to_h' fresh in
	   let (v',h',h_to_h',fresh) = map v h' h_to_h' fresh in
	   (Graph.add_edge u' v' h',h_to_h',fresh)
	  ) h (Graph.empty,Hom.empty,fresh)
      in

      let h,g = emb_h.trg,emb_g.trg in
      let inf_gh = emb_h.src in
      let fresh = (max (Graph.max_id g) (Graph.max_id h)) + 1 in
      List.fold_left
	(fun tiles to_h ->
	 let mpos_for_h =
	   List.fold_left
	     (fun tiles to_g ->
	      try
		let g',g_to_g',fresh = rename fresh g (to_g,inf_gh,to_h,h) in
		(*let h',h_to_h',_ = rename (-1) h (to_h,inf_gh,Hom.identity (Graph.nodes h),g) in*)

		let sup_gh = Graph.join h g' in
		let emb_h_to_sup = {src = h ; trg = sup_gh ; maps = [Hom.identity (Graph.nodes h)]} in
		let emb_g_to_sup = {src = g ; trg = sup_gh ; maps = [g_to_g']} in
		let emb_g =  {src = inf_gh ; trg = g ; maps = [to_g]} in
		let emb_h =  {src = inf_gh ; trg = h ; maps = [to_h]} in
		{span = (emb_h,emb_g) ; cospan = Some (emb_h_to_sup,emb_g_to_sup)}::tiles
	      with
		Graph.Incoherent ->
		let emb_g = {src = inf_gh ; trg = g ; maps = [to_g]} in
		let emb_h = {src = inf_gh ; trg = h ; maps = [to_h]} in
		{span = (emb_h,emb_g) ; cospan = None}::tiles
	     ) [] emb_g.maps
	 in
	 mpos_for_h@tiles
	) [] emb_h.maps

    let glue g h span_option =
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
      let subgraphs_of_edges graph inf =
	try
	  Graph.fold_edges
	    (fun u v subgraphs ->
	     let subg = Graph.add_node u (Graph.add_node v inf) in
	     (Graph.add_edge u v subg)::subgraphs
	    ) graph []
	with
	  Graph.Incoherent -> failwith "Invariant violation: graph is incoherent"
      in
      let one_gluings =
	let cstr_edges =
	  match span_option with
	    None -> Graph.empty
	  | Some (_,emb_to_g) ->
	     match co_domains emb_to_g with
	       [cod] -> cod
	     | _ -> failwith "Invariant violation: Gluing under constraint should use flat embeddings"
	in
	List.fold_left
	  (fun arr_list sub_g ->
	   try
	     let embeddings = embed sub_g h
	     in
	     embeddings::arr_list
	   with
	     Undefined -> arr_list
	  ) [] (subgraphs_of_edges g cstr_edges)
      in
      let gluing_points = enumerate_gluings one_gluings one_gluings one_gluings [] in
      let spans =
	List.fold_left
	  (fun spans inf_to_h ->
	   let to_h = extension_class inf_to_h in
	   let to_g =  identity inf_to_h.src g in (*Asymmetry is important here because all subparts of g are added edges*)
	   (to_h,to_g)::spans
	  ) [] gluing_points
      in
      let mpos =
	List.fold_left
	  (fun tiles span ->
	   (mpo span)@tiles
	  ) [] spans
      in
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

    let (><) g h = glue g h None

    (*if [max] then only retains gluings with maximal size. May contain isomorphic gluings.*)
    let share max = function
	(emb,emb') as span ->
	let compare_tile tile tile' =
	  let src = inf_of_tile tile in
	  let src' = inf_of_tile tile' in
	  compare (Graph.size_edge src') (Graph.size_edge src) (*to have list sorted in increasing order*)
	in
	let gluings = glue emb.trg emb'.trg (Some span) in
	let ordered_gluings =
	  List.fast_sort compare_tile gluings
	in
        let sharings = List.map (fun tile -> ({emb' with trg = inf_of_tile tile},tile)) ordered_gluings
        in
	let rec cut = function
	    [] | [_] as l -> l
	    | (emb,tile)::(emb',tile')::tl ->
	       if (compare_tile tile tile') = 0 then ((emb,tile)::(cut ((emb',tile')::tl)))
	       else [(emb,tile)]
	in
	if max then cut sharings
        else sharings

    let is_iso emb =
      List.for_all (fun trg -> Graph.is_equal trg emb.trg) (images emb.src emb)

    let invert emb =
      {src = emb.trg ; trg = emb.src ; maps = List.map Hom.invert emb.maps}
  end
