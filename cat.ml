module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)

    module NodeSet = Set.Make (Node)
    open Lib.Util

    exception Undefined
    type embeddings = {src : Graph.t ; trg : Graph.t ; maps : Hom.t list ; partial : bool}
    type tile = {span : embeddings * embeddings ; cospan : (embeddings * embeddings) option}

    let is_domain_identity emb =
      List.for_all Hom.is_identity emb.maps

    let inf_of_tile tile =
      let (emb,_) = tile.span in emb.src

    let size emb =
      Hom.size (List.hd emb.maps)

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

    let is_span (emb1,emb2) =
      Graph.is_equal emb1.src emb2.src

    let is_co_span (emb1,emb2) =
      Graph.is_equal emb1.trg emb2.trg

    let string_of_embeddings ?(full=false) ?(nocolor=false) emb =
      let str0 =
        if full then
          Printf.sprintf "%s -" (Graph.to_string emb.src)
        else
          ""
      in
      let str1 =
        if full then
          Printf.sprintf "-> %s" (Graph.to_string emb.trg)
        else
          ""
      in
      let col = if nocolor then fun x -> x else red
      in
      str0^(col (String.concat "+" (List.map Hom.to_string emb.maps)))^str1

    let dot_of_embeddings emb =
      let cluster0,ref_cluster0,fresh = Graph.to_dot_cluster emb.src 0 0 in
      let cluster1,ref_cluster1,_ = Graph.to_dot_cluster emb.trg 1 fresh in
      let arrows =
	String.concat ";\n"
		      (List.map (fun hom -> ref_cluster0^"->"^ref_cluster1^(Hom.to_dot_label hom)) emb.maps)
      in
      String.concat "\n" ["digraph G {\n";cluster0;cluster1;arrows;"}"]


    let string_of_span (emb,emb') =
      assert (is_span (emb,emb')) ;
      let str = Printf.sprintf " %s " (Graph.to_string emb.src) in
      let str' = Printf.sprintf " %s " (Graph.to_string emb.trg) in
      let str'' = Printf.sprintf " %s " (Graph.to_string emb'.trg) in
      str'^"<-"^(string_of_embeddings emb)^"-"^str^"-"^(string_of_embeddings emb')^"->"^str''


    let string_of_co_span (emb,emb') =
      assert (is_co_span (emb,emb')) ;
      let str = Printf.sprintf " %s " (Graph.to_string emb.trg) in
      let str' = Printf.sprintf " %s " (Graph.to_string emb.src) in
      let str'' = Printf.sprintf " %s " (Graph.to_string emb'.src) in
      str'^"-"^(string_of_embeddings emb)^"->"^str^"<-"^(string_of_embeddings emb')^"-"^str''

    let string_of_tile tile =
      match tile.cospan with
	None -> (string_of_span tile.span)^"\n[NO_SUP]"
      | Some co_span ->
	 (string_of_co_span co_span)^"\n"^(string_of_span tile.span)

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

    let (===) emb emb' =
      let commute =
        try
          List.iter2
            (fun hom hom' ->
              Hom.fold
                (fun u v () ->
                  if v <> Hom.find u hom' then raise Exit
                ) hom ()
            ) emb.maps emb'.maps ;
          true
        with
          Exit -> false
      in
      if not commute then false
      else
        try
          List.iter2
            (fun cod cod' ->
              if not (Graph.is_equal cod cod') then raise Exit
            ) (co_domains emb) (co_domains emb') ;
          true
        with
          Exit -> false


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
      | maps -> {src = g ; trg = h ; maps = maps ; partial = false}

    let identity g h =
      {src = g ; trg = h ; maps = [Hom.identity (Graph.nodes g)] ; partial = false}

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
	{src = src ; trg = trg ; maps = maps ; partial = emb.partial || emb'.partial}

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
	{src = emb'.src ;
	 trg = emb.trg ;
	 maps = maps;
         partial = emb.partial || emb'.partial}


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
	  {src = src ; trg = trg ; maps = [hom]; partial = false}::emb_list
	) [] emb.maps

    let merge_embeddings emb emb' =
      assert (Graph.is_equal emb.src emb'.src && Graph.is_equal emb.trg emb'.trg) ;
      extension_class {src = emb.src ; trg = emb.trg ; maps = emb.maps@emb'.maps; partial = false}

    let merge_tile tile tile' =
      let merge_pair (emb0,emb0') (emb1,emb1') =
        ((merge_embeddings emb0 emb1), (merge_embeddings emb0' emb1'))
      in
      let span = merge_pair tile.span tile'.span in
      let cospan =
        match (tile.cospan,tile'.cospan) with
          None,None -> None
        | Some csp,Some csp' -> Some (merge_pair csp csp')
        | _ -> failwith "Cannot merge tiles"
      in
      {span = span ; cospan = cospan}

    let (@@) = vertical_compose

    let is_iso emb =
      List.for_all (fun trg -> Graph.is_equal trg emb.trg) (images emb.src emb)

    let invert emb =
      let emb' = {src = emb.trg ; trg = emb.src ; maps = List.map Hom.invert emb.maps ; partial = false}
      in
      try
        let _ = co_domains emb' in
        emb'
      with Not_found -> {emb' with partial = true}

    let complete left ls sup il inf ir =
      let comp u u' h =
        if Hom.mem_sub (Node.id u) h then
          Hom.find_sub (Node.id u) h = Node.id u'
        else
          not (Hom.comem_sub (Node.id u') h)
      in
      let name_in u to_g g =
        try
          let i = Hom.cofind_sub (Node.id u) to_g in
          Node.rename i u
        with
          Not_found ->
          Node.rename ((Graph.max_id g) + 1) u
      in
      let extend u p_hom sup inf_to_left inf inf_to_right continuation =
        assert (not (Hom.mem u p_hom)) ;
        let ext_uu' = (*list of all possible extensions of p_hom to the association u |--> u' (for some u' in sup)*)
          Graph.fold_nodes
            (fun u' cont ->
              if not (comp u u' p_hom) then cont
              else
                try
                  let hom_uu' = Hom.add u u' p_hom in
                  let sup',il',inf',ir' =
                    List.fold_left
                      (fun (sup,il,inf,ir) v ->
                        try
                          let v' = Hom.find v hom_uu' in
                          let il',inf',ir' =
                            if Graph.has_edge u' v' sup then
                              let u_inf = name_in u il inf in
                              let inf = Graph.add_node u_inf inf in
                              let v_inf = name_in v il inf in
                              let inf = Graph.add_node v_inf inf in
                              let inf' = Graph.add_edge u_inf v_inf inf
                              in
                              (Hom.add u_inf u (Hom.add v_inf v il),inf',Hom.add u_inf u' (Hom.add v_inf v' ir))
                            else
                              (il,inf,ir) (*unchanged*)
                          in
                          let sup' = Graph.add_edge ~weak:true u' v' sup
                          in
                          (sup',il',inf',ir')
                        with
                          Not_found -> (sup,il,inf,ir) (*v has no image by p_hom*)
                        | Graph.Incoherent -> failwith "Invariant violation (inf should be a coherent graph)"
                      ) (sup,inf_to_left,inf,inf_to_right) (Graph.bound_to u left)
                  in
                  (hom_uu',sup',il',inf',ir')::cont
                with
                  Hom.Not_injective | Hom.Not_structure_preserving -> cont
            ) sup continuation
        in
        (*Trying to add a fresh version of u in sup if possible*)
        try
          let u_sup =
            if Hom.mem_sub (Node.id u) p_hom then
              if Graph.has_node (Node.rename (Hom.find_sub (Node.id u) p_hom) u) sup then raise Hom.Not_injective
              else
                (Node.rename (Hom.find_sub (Node.id u) p_hom) u)
            else
              Node.rename (Graph.max_id sup + 1) u
          in
          let hom_uu_sup = Hom.add u u_sup p_hom in
          let sup' =
            List.fold_left
              (fun sup' v ->
                try
                  let v' = Hom.find v hom_uu_sup in
                  Graph.add_edge ~weak:true u_sup v' sup'
                with
                  Not_found -> sup'
              ) (Graph.add_node u_sup sup) (Graph.bound_to u left)
          in
          (hom_uu_sup,sup',inf_to_left,inf,inf_to_right)::ext_uu'
        with
          Hom.Not_injective | Hom.Not_structure_preserving -> ext_uu'
      in
      Graph.fold_nodes
        (fun u ext_list ->
          (*Printf.printf "looking for an association for node %s\n" (Node.to_string u) ;*)
          let all_ext_u =
            List.fold_left
              (fun cont (ls,sup,il,inf,ir) ->
                if Hom.mem u ls then (ls,sup,il,inf,ir)::cont
                else
                  (*[extend u ls sup il inf ir cont] extends ls with all possible associations of u to u' in sup or fresh*)
                  extend u ls sup il inf ir cont
              ) [] ext_list
          in
          all_ext_u
        ) left [(ls,sup,il,inf,ir)]

    let hom_of_embeddings emb =
      match emb.maps with
        [hom] -> hom
      | _ -> failwith "Invariant violation, not a flat embedding"

    (*given a span, returns a cospan where the left upper map is a partial morphism*)
    let ipo (inf_to_left,inf_to_right) =
      (*Printf.printf "Computing ipo of %s\n" (string_of_span (inf_to_left,inf_to_right)) ;*)
      let right_to_sup = identity inf_to_right.trg inf_to_right.trg in
      let part_left_to_sup = inf_to_right @@ (invert inf_to_left) in
      let inf = inf_to_left.src in
      let left = inf_to_left.trg in
      let right = inf_to_right.trg in
      let sup = right_to_sup.trg in
      let hom_p =  hom_of_embeddings part_left_to_sup in
      let inf_to_right = hom_of_embeddings inf_to_right in
      let inf_to_left = hom_of_embeddings inf_to_left in
      List.fold_left
        (fun sharing_tiles (left_to_sup',sup',inf_to_left',inf',inf_to_right') ->
          let emb_inf_left = {src = inf' ; trg = left ; maps = [inf_to_left'] ; partial = false} in
          let emb_inf_right = {src = inf' ; trg = right ; maps = [inf_to_right']; partial = false} in
          let csp_opt =
            if sup'.Graph.coherent then
              Some ({src = left ; trg = sup' ; maps = [left_to_sup'] ; partial = false},identity right sup')
            else
              None
          in
          let tile = {span = (emb_inf_left,emb_inf_right) ; cospan = csp_opt} in
          (identity inf inf',tile)::sharing_tiles
        ) [] (complete left hom_p sup inf_to_left inf inf_to_right)

    let glue g h =
      let subparts g h =
        Graph.fold_edges
          (fun u v cont ->
            let g1 = Graph.add_edge u v (Graph.add_node u (Graph.add_node v Graph.empty))
            in
            let emb_list = flatten (extension_class (embed g1 h)) in
            List.fold_left
            (fun cont emb ->
              (identity g1 g,emb)::cont
            ) cont emb_list
          ) g []
      in
      let sh_tiles =
        List.fold_left
        (fun cont (to_g,to_h) ->
          (ipo (to_g,to_h))@cont
        ) [] (subparts g h)
      in
      List.fold_left
        (fun cont (emb,tile) ->
          if Graph.is_empty (inf_of_tile tile) then cont
          else
            match tile.cospan with
              None -> cont
            | Some _ -> tile::cont
        ) [] sh_tiles

    let share f g =
      let compare_sharing (emb,_) (emb',_) =
        compare (size emb) (size emb')
      in
      let sh_tiles = List.fast_sort compare_sharing (ipo (f,g))
      in
      match sh_tiles with
        [] ->
        None
      | h::_ -> Some h
  end
