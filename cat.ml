module type Category =
  sig
    type arrows
    type tile
    type obj

    (**Constructors*)
    val identity : obj -> obj -> arrows
    val (=>) : obj -> obj -> arrows
    val (|>) : obj -> obj -> tile list

    (**Pretty printing*)
    val string_of_arrows : ?full:bool -> ?nocolor:bool -> arrows -> string
    val string_of_tile : tile -> string
    val string_of_span : arrows * arrows -> string
    val string_of_cospan : arrows * arrows -> string

    val arrows_of_tile : tile -> arrows
    val left_of_tile : tile -> obj
    val right_of_tile : tile -> obj
    val lower_bound : tile -> (arrows * arrows)
    val upper_bound : tile -> (arrows * arrows) option

    val src : arrows -> obj
    val trg : arrows -> obj

    val share : arrows -> arrows -> (arrows * tile) list
    val is_iso : arrows -> bool
    val is_identity : arrows -> bool
    val invert : arrows -> arrows
    val flatten : arrows -> arrows list
    val extension_class : arrows -> arrows
    val matching_class : arrows -> arrows
    val images : obj -> arrows -> obj list

    (**Operators*)
    val (@@) : arrows -> arrows -> arrows
    val (^^) : arrows -> arrows -> (arrows * tile) list
    val (===) : arrows -> arrows -> bool

    (**Exceptions*)
    exception Undefined
  end

module Make (Node:Node.NodeType) =
  (struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)

    type obj = Graph.t

    module NodeSet = Set.Make (Node)
    open Lib.Util

    exception Undefined

    type arrows = {src : obj ; trg : obj ; maps : Hom.t list ; partial : bool}

    type tile = {span : arrows * arrows ; cospan : (arrows * arrows) option}


    let is_identity f = List.for_all (fun h -> Hom.is_identity h) f.maps
    let lower_bound tile = tile.span
    let upper_bound tile = tile.cospan

    let src f = f.src
    let trg f = f.trg

    let is_domain_identity f =
      List.for_all Hom.is_identity f.maps

    let inf_of_tile tile =
      let (f,_) = tile.span in f.src

    let sup_of_tile tile =
      match tile.cospan with
	None -> None
      | Some (f,_) -> Some f.trg

    let left_of_tile tile =
      let (f,_) = tile.span in
      f.trg

    let right_of_tile tile =
      let (_,f') = tile.span in
      f'.trg

    let is_span (f1,f2) =
      Graph.is_equal f1.src f2.src

    let is_cospan (f1,f2) =
      Graph.is_equal f1.trg f2.trg

    let string_of_arrows ?(full=false) ?(nocolor=false) f =
      let str0 =
        if full then
          Printf.sprintf "%s -" (Graph.to_string f.src)
        else
          ""
      in
      let str1 =
        if full then
          Printf.sprintf "-> %s" (Graph.to_string f.trg)
        else
          ""
      in
      let col = if nocolor then fun x -> x else red
      in
      str0^(col (String.concat "+" (List.map Hom.to_string f.maps)))^str1

    let dot_of_arrows f =
      let cluster0,ref_cluster0,fresh = Graph.to_dot_cluster f.src 0 0 in
      let cluster1,ref_cluster1,_ = Graph.to_dot_cluster f.trg 1 fresh in
      let arrows =
	String.concat ";\n"
		      (List.map (fun hom -> ref_cluster0^"->"^ref_cluster1^(Hom.to_dot_label hom)) f.maps)
      in
      String.concat "\n" ["digraph G {\n";cluster0;cluster1;arrows;"}"]


    let string_of_span (f,f') =
      if (is_span (f,f')) then
        begin
          let str = Printf.sprintf " %s " (Graph.to_string f.src) in
          let str' = Printf.sprintf " %s " (Graph.to_string f.trg) in
          let str'' = Printf.sprintf " %s " (Graph.to_string f'.trg) in
          str'^"<-"^(string_of_arrows f)^"-"^str^"-"^(string_of_arrows f')^"->"^str''
        end
      else
        let str0 = Printf.sprintf " %s " (Graph.to_string f.src) in
        let str1 = Printf.sprintf " %s " (Graph.to_string f'.src) in
        let str' = Printf.sprintf " %s " (Graph.to_string f.trg) in
        let str'' = Printf.sprintf " %s " (Graph.to_string f'.trg) in
        print_string (str'^"<-"^(string_of_arrows f)^"-"^str0^"<<>>"^str1^"-"^(string_of_arrows f')^"->"^str'') ;
        failwith "Invalid argument"


    let string_of_cospan (f,f') =
      assert (is_cospan (f,f')) ;
      let str = Printf.sprintf " %s " (Graph.to_string f.trg) in
      let str' = Printf.sprintf " %s " (Graph.to_string f.src) in
      let str'' = Printf.sprintf " %s " (Graph.to_string f'.src) in
      str'^"-"^(string_of_arrows f)^"->"^str^"<-"^(string_of_arrows f')^"-"^str''

    let string_of_tile tile =
      match tile.cospan with
	None -> "[No SUP]\n"^(string_of_span tile.span)
      | Some co_span ->
	 (string_of_cospan co_span)^"\n"^(string_of_span tile.span)

    let images g f =
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
        ) [] f.maps

    let co_domains f = images f.src f

    let (===) f f' =
      let commute =
        try
          List.iter2
            (fun hom hom' ->
              Hom.fold
                (fun u v () ->
                  if v <> Hom.find u hom' then raise Exit
                ) hom ()
            ) f.maps f'.maps ;
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
            ) (co_domains f) (co_domains f') ;
          true
        with
          Exit -> false


    let embed _G _H =
      let rec extend hom_list iG jG acc =
	match hom_list with
	  [] -> acc
	| phi::tl ->
	   try
	     let iH = Hom.find iG phi in
	     let opt = try Some (Hom.find jG phi) with Not_found -> None in
	     match opt with
	       None ->
	       let biH = Graph.bound_to iH _H in
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
		if Graph.has_edge iH jH _H then extend tl iG jG (phi::acc)
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
	  ) (hom_list,already_done) (Graph.bound_to i _G)
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
      let cc_roots = Graph.connected_components _G in
      List.fold_left
	(fun hom_list u ->
	  let hom_list_u = extend_next_root u hom_list _G _H in
	  let hom_list_extended,_ = explore_cc u hom_list_u (NodeSet.singleton u) in
	  hom_list_extended
	) [Hom.empty] cc_roots

    let (=>) _G _H =
      match embed _G _H with
	[] -> raise Undefined
      | maps -> {src = _G ; trg = _H ; maps = maps ; partial = false}

    let identity _G _H =
      {src = _G ; trg = _H ; maps = [Hom.identity (Graph.nodes _G)] ; partial = false}

    let tensor f f' =
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
	        ) [] f'.maps
	    in
	    hom_added@maps
	  ) [] f.maps
      in
      if maps = [] then raise Undefined
      else
	let src = Graph.join f.src f'.src in
	let trg = Graph.join f.trg f'.trg in
	{src = src ; trg = trg ; maps = maps ; partial = f.partial || f'.partial}

    let compose f f' =
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
	        ) maps f'.maps
	    in
	    hom_ext_list@maps
	  ) [] f.maps
      in
      if maps = [] then raise Undefined
      else
	{src = f'.src ;
	 trg = f.trg ;
	 maps = maps;
         partial = f.partial || f'.partial}


    let eq_class matching f auto =
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
	     ) f.maps
	  )
      in
      assert (reduced_maps <> []) ;
      {f with maps = reduced_maps}

    let extension_class f =
      let auto = (embed f.trg f.trg) in
      eq_class false f auto

    let matching_class f =
      let auto = (embed f.src f.src) in
      eq_class true f auto


    let flatten f =
      let src = f.src in
      let trg = f.trg in
      List.fold_left
	(fun emb_list hom ->
	  {src = src ; trg = trg ; maps = [hom]; partial = false}::emb_list
	) [] f.maps

    let (@@) = compose

    let is_iso f =
      List.for_all (fun trg -> Graph.is_equal trg f.trg) (images f.src f)

    let invert f =
      let f' = {src = f.trg ; trg = f.src ; maps = List.map Hom.invert f.maps ; partial = false}
      in
      try
        let _ = co_domains f' in
        f'
      with Not_found -> {f' with partial = true}

    let complete left ls sup0 il inf ir =
      let comp u u' h =
        if Hom.mem u h then u' = Hom.find u h
        else
          if Hom.mem_sub (Node.id u) h then
            Hom.find_sub (Node.id u) h = Node.id u'
          else
            not (Hom.comem_sub (Node.id u') h)
      in
      let name_in_inf u from_inf inf =
        try
          if Hom.comem u from_inf then Hom.cofind u from_inf
          else
            let i = Hom.cofind_sub (Node.id u) from_inf in
            Node.rename i u
        with
          Not_found -> Node.rename ((Graph.max_id inf) + 1) u (*Make u fresh in inf*)
      in
      let extend u p_hom sup inf_to_left inf inf_to_right continuation =
        (*list of all possible extensions of p_hom to the association
          u |--> u' (for some u' in sup)*)
        
        let () = Printf.printf "(%s) + %s|-> ...\n"  (Hom.to_string p_hom) (Node.to_string u) in
        
        let ext_uu' =
          Graph.fold_nodes
            (fun u' cont -> (*for all u' in sup*)
              
              let () = Printf.printf "%s\n" (Node.to_string u') in
              
              if not (comp u u' p_hom) then cont
              else
                try
                  let hom_uu' = Hom.add u u' p_hom in
                  let il',inf',ir',sup' =
                    List.fold_left
                      (*for all v bound to u in left*)
                      (fun (il,inf,ir,sup) v ->
                        try
                          let v' = Hom.find v hom_uu' in
                          if Graph.has_edge u' v' sup0 then
                            let u_inf = name_in_inf u il inf in
                            let inf = Graph.add_node u_inf inf in
                            let v_inf = name_in_inf v il inf in
                            let inf = Graph.add_node v_inf inf in
                            let inf' = Graph.add_edge u_inf v_inf inf in
                            (Hom.add u_inf u (Hom.add v_inf v il),
                             inf',Hom.add u_inf u' (Hom.add v_inf v' ir),
                             sup)
                          else
                            (il,inf,ir,Graph.add_edge ~weak:true u' v' sup)
                        with
                          (*v has no image by p_hom*)
                          Not_found -> (il,inf,ir,sup)
                        | Graph.Incoherent ->
                           failwith
                             "Invariant violation
                              (inf should be a coherent graph)"
                      )
                      (inf_to_left,inf,inf_to_right,sup)
                      (Graph.bound_to u left)
                  in
                  
                  let () = Printf.printf "%s\n" (Hom.to_string hom_uu') in
                  
                  (hom_uu',sup',il',inf',ir')::cont
                with
                  Hom.Not_injective | Hom.Not_structure_preserving -> cont
            ) sup continuation
        in
        (*Trying to add a fresh version of u in sup if possible*)
        try
          if Hom.mem u p_hom then raise Hom.Not_injective
          else
            let u_sup =
              if Hom.mem_sub (Node.id u) p_hom then
                let u_sup = Node.rename (Hom.find_sub (Node.id u) p_hom) u in
                if Graph.has_node u_sup sup then raise Hom.Not_injective
                else
                  u_sup
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
            
            let () = Printf.printf "%s\n" (Hom.to_string hom_uu_sup)
            in
            
            (hom_uu_sup,sup',inf_to_left,inf,inf_to_right)::ext_uu'
        with
          Hom.Not_injective | Hom.Not_structure_preserving -> ext_uu'
      in
      Graph.fold_nodes
        (fun u ext_list ->
          
          let () = Printf.printf "looking for an association for node %s\n" (Node.to_string u) in
          
          let all_ext_u =
            List.fold_left
              (fun cont (ls,sup,il,inf,ir) ->
                (*[extend u ls sup il inf ir cont] extends ls with all possible associations of u to u' in sup or fresh*)
                  extend u ls sup il inf ir cont
              ) [] ext_list
          in
          all_ext_u
        ) left [(ls,sup0,il,inf,ir)]

    let hom_of_arrows f =
      match f.maps with
        [hom] -> hom
      | _ -> failwith "Invariant violation, not a flat embedding"

    (*given a span, returns a cospan where the left upper map is a partial morphism*)
    let (^^) inf_to_left inf_to_right =
      let close_rs right_to_sup cont =
        let part_left_to_sup = inf_to_right @@ (invert inf_to_left) in
        let inf = inf_to_left.src in
        let left = inf_to_left.trg in
        let right = inf_to_right.trg in
        let sup = right_to_sup.trg in
        let hom_p =  hom_of_arrows part_left_to_sup in
        let inf_to_right = hom_of_arrows inf_to_right in
        let inf_to_left = hom_of_arrows inf_to_left in
        List.fold_left
          (fun sharing_tiles (left_to_sup',sup',inf_to_left',inf',inf_to_right') ->
           let emb_inf_left = {src = inf' ; trg = left ; maps = [inf_to_left'] ; partial = false} in
           let emb_inf_right = {src = inf' ; trg = right ; maps = [inf_to_right']; partial = false} in
           let csp_opt =
             if Graph.is_coherent sup' then
               Some ({src = left ; trg = sup' ; maps = [left_to_sup'] ; partial = false},identity right sup')
             else
               None
           in
           let tile = {span = (emb_inf_left,emb_inf_right) ; cospan = csp_opt} in
           (identity inf inf',tile)::sharing_tiles
          ) cont (complete left hom_p sup inf_to_left inf inf_to_right)
      in
      close_rs (identity inf_to_right.trg inf_to_right.trg) []

    let arrows_of_tile tile =
      match tile.cospan with
        None -> raise Undefined
      | Some (ls,_) ->
         let (il,_) = tile.span in
         ls @@ il

    let merge_arrows f f' =
      assert (Graph.is_equal f.src f'.src && Graph.is_equal f.trg f'.trg) ;
      extension_class {src = f.src ; trg = f.trg ; maps = f.maps@f'.maps; partial = false}

    let share f g =
      let compare_sharing (f,tile) (f',tile') =
        match upper_bound tile,upper_bound tile' with
          None,Some _ -> 1
        | Some _ ,None -> -1
        | Some (f,_), Some (g,_) ->
           compare (Graph.size_node f.trg,Graph.size_edge f.trg) (Graph.size_node g.trg,Graph.size_edge g.trg)
        | _ -> 0
      in
      let ipos =
        List.filter (fun (f,tile) -> Graph.is_connex f.trg) (f ^^ g)
      in
      let sh_tiles = List.fast_sort compare_sharing ipos
      in
      match sh_tiles with
        [] -> []
      | h::_ -> List.fold_left
                  (fun cont sh ->
                   let hd = List.hd cont in
                   if (compare_sharing hd sh) = 0 then sh::cont
                   else
                     cont
                  ) [List.hd sh_tiles] (List.rev sh_tiles)

    let glue g h =
      (*returns spans of the form g <-id- g1 -f-> h where g1 is an edge of g*)
      (*both branches of the spans are up to eq class*)
      let subparts g h =
        let subs =
          Graph.fold_edge_types
            (fun u v cont ->
             let g1 = Graph.add_edge u v (Graph.add_node u (Graph.add_node v Graph.empty))
             in
             (flatten (extension_class (g1 => g)))@cont
            ) g []
        in
        List.fold_left
          (fun cont emb_g1_g ->
           let g1 = emb_g1_g.src in
           let emb_g1_h_list = try flatten (extension_class (g1 => h)) with Undefined -> [] in
           List.fold_left
             (fun cont emb_g1_h ->
              (emb_g1_g,emb_g1_h)::cont
             ) cont emb_g1_h_list
          ) [] subs
      in
      List.fold_left
        (fun cont (to_g,to_h) ->
         (to_g ^^ to_h)@cont
        ) [] (subparts g h)

    (** [h |> obs] [h] may create/destroy an instance of obs*)
    let (|>) h obs =
      let eq_tile obs_right tile tile' =
        try
          match tile.cospan,tile'.cospan with
            None,_ -> raise Undefined
          | _,None -> raise Undefined
          | Some (left_to_sup,right_to_sup),Some (left_to_sup',right_to_sup') ->
             assert (Graph.is_equal left_to_sup.src left_to_sup'.src
                     && Graph.is_equal right_to_sup.src right_to_sup'.src) ;
             let ext,ext' = if obs_right then (left_to_sup,left_to_sup') else (right_to_sup,right_to_sup') in
             (*optim*)
             let sup,sup' = left_to_sup.trg,left_to_sup'.trg in
             if (Graph.size_node sup <> Graph.size_edge sup')
                && (Graph.size_edge sup <> Graph.size_edge sup)
             then false
             else
               match share ext ext' with
                 [] -> false
               | (_,sh_tile)::_ ->
                  let (inf_to_left,inf_to_right) = sh_tile.span in
                  (is_iso inf_to_left) && is_iso (inf_to_right)
        with
          Undefined -> false
      in
      List.fold_left
        (fun cont (f,tile) ->
         if Graph.is_empty (inf_of_tile tile) then cont
         else
           match tile.cospan with
             None -> cont
           | Some _ ->
              if List.exists
                   (fun tile' ->
                    eq_tile true tile tile'
                   ) cont then cont
              else tile::cont
        ) [] (glue h obs)


  end:Category with type obj = Graph.Make(Node).t)
