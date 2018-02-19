module type Category =
  sig
    type arrows
    type tile
    type obj

    (**Constructors*)
    val unit : arrows
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
    val fold_arrow : arrows -> (int * int) list


    val share : arrows -> arrows -> (arrows * tile) list
    val share_new : arrows -> arrows -> (arrows * tile) list
    val is_iso : arrows -> bool
    val is_identity : arrows -> bool
    val invert : arrows -> arrows
    val flatten : arrows -> arrows list
    val extension_class : arrows -> arrows
    val matching_class : arrows -> arrows
    val equalize : arrows -> arrows -> arrows option
    val compare : arrows -> arrows -> int

    (**Operators*)
    val (@@) : arrows -> arrows -> arrows
    val (/|) : arrows -> arrows -> (arrows * tile) list
    val (|/) : arrows -> arrows -> (arrows * arrows) list
    val (===) : arrows -> arrows -> bool
    val (-->) : obj -> arrows -> obj list
    val (=~=) : arrows -> arrows -> bool

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
    let unit = {src = Graph.empty ; trg = Graph.empty ; maps = [] ; partial = false}

    type tile = {span : arrows * arrows ; cospan : (arrows * arrows) option}

    let flat f = match f.maps with [_] -> true | _ -> false

    let fold_arrow ars =
      let ar = List.hd ars.maps in
      Hom.fold (fun u v cont -> (Node.id u, Node.id v)::cont) ar []

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
	  (List.map
             (fun hom ->
               ref_cluster0^"->"^ref_cluster1^(Hom.to_dot_label hom)
             ) f.maps
          )
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
        print_string
          (str'^"<-"^(string_of_arrows f)^"-"^str0^"<<>>"^str1^"-"
           ^(string_of_arrows f')^"->"^str'') ;
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

    let (-->) _G f =
      List.fold_left
        (fun images hom ->
          (Graph.image hom _G)::images
        ) [] f.maps

    let co_domains f = f.src --> f

    let (===) f f' =
      if not (Graph.is_equal f.src f'.src) then false
      else
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
	      | Some i ->
                 (*Looking for a candidate among those having [hom (Node.id u)] as id*)
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
      try
        assert (flat f && flat f') ;
        let hom = List.hd f.maps in
        let hom' = List.hd f'.maps in
        {src = f'.src ;
         trg = f.trg ;
         maps = [Hom.compose hom hom'];
         partial = f.partial || f'.partial
        }
      with
        Hom.Not_injective | Hom.Not_structure_preserving -> raise Undefined


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
      assert (flat f) ;
      let trg = List.hd (f.src --> f) in
      Graph.is_equal trg f.trg

    let invert f =
      let f' = {src = f.trg ;
                trg = f.src ;
                maps = List.map Hom.invert f.maps ;
                partial = false}
      in
      try
        let _ = co_domains f' in
        f'
      with Not_found -> {f' with partial = true}

    let arrows_of_tile tile =
      match tile.cospan with
        None -> raise Undefined
      | Some (ls,_) ->
         let (il,_) = tile.span in
         ls @@ il

    exception Found of arrows

    (**returns g -if it exists- s.t gf = f'*)
    let complete f f' =
      try
        let arrows = flatten (f.trg => f'.trg) in
        List.iter
          (fun g ->
            if (g @@ f) === f' then raise (Found g)
            else ()
          ) arrows ; raise Undefined
      with
      | Found g -> g

    (**returns Some iso phi -if it exists- s.t (phi o f) = f', None otherwise*)
    let equalize f f' =
      try
        if Graph.is_equal f.src f'.src
           && Graph.size_edge f.trg = Graph.size_edge f'.trg
           && Graph.size_node f.trg = Graph.size_node f'.trg
        then
          Some (complete f f')
        else
          None
      with
        Undefined -> None

    let extend left ls sup0 il inf ir =
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
      let extend_point u p_hom sup inf_to_left inf inf_to_right continuation next =
        let next =
          let ext,next =
            List.fold_left
              (fun (ext,next) v ->
                if Hom.mem v p_hom || List.mem v next then (ext,next)
                else
                  (true,v::next)
              ) (false,next) (Graph.nodes_of_id (Node.id u) left)
          in
          if ext then next
          else
            List.fold_left
              (fun next v -> if List.mem v next then next else v::next)
              next (Graph.bound_to u left)
        in
        let iter_candidates f =
          let candidates =
            try
              let id' = Hom.find_sub (Node.id u) p_hom in
              try Graph.nodes_of_id id' sup with Not_found -> failwith "Invariant violation"
            with
              Not_found -> []
          in
          match candidates with
            [] -> (*id of u is not constrained by p_hom yet*)
             (*Optim for graphs with rigidity*)
             if Node.has_rigid_bonds then
               match Graph.bound_to u left with
                 [v] ->
                  let candidates =
                    try
                      let id' = Hom.find_sub (Node.id v) p_hom in
                      List.fold_left
                        (fun cont v' ->
                          if Node.rename id' v = v' then (Graph.bound_to v' sup)@cont
                          else cont
                        ) [] (Graph.nodes_of_id id' sup)
                    with
                      Not_found -> []
                  in
                  if candidates = [] then failwith "Rigidity violation"
                  else
                    fun cont -> List.fold_left (fun cont u' -> f u' cont) cont candidates
               | _ -> failwith "Rigidity violation"
             else
               Graph.fold_nodes f sup
          | _ ->
             (*Since u_id is already constrained by p_hom,
               candidates for matching u are nodes with the same id*)
             fun cont -> List.fold_left (fun cont u' -> f u' cont) cont candidates
        in

        (*list of all possible extensions of p_hom to the association
          u |--> u' (for some u' in sup)*)
        let ext_uu' =
          iter_candidates
            (fun u' cont ->
              if not (comp u u' p_hom) && (Graph.compatible u' sup) then cont
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
                            let sup = Graph.add_node u' (Graph.add_node v' sup) in
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
                  (hom_uu',sup',il',inf',ir')::cont
                with
                  Hom.Not_injective | Hom.Not_structure_preserving -> cont
            ) continuation
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
                    let sup' = Graph.add_node v' sup' in
                    Graph.add_edge ~weak:true u_sup v' sup'
                  with
                    Not_found -> sup'
                ) (Graph.add_node u_sup sup) (Graph.bound_to u left)
            in
            ((hom_uu_sup,sup',inf_to_left,inf,inf_to_right)::ext_uu',next)
        with
          Hom.Not_injective | Hom.Not_structure_preserving -> (ext_uu',next)
      in
      let rec iter_extend ext_list next =
        match next with
          [] -> ext_list
        | _ ->
           let ext_list,next =
             List.fold_left
               (fun (ext_list,next) u ->
                 List.fold_left
                   (fun (cont,next) (ls,sup,il,inf,ir) ->
                     extend_point u ls sup il inf ir cont next
                   ) ([],next) ext_list
               ) (ext_list,[]) next
           in
           iter_extend ext_list next
      in
      iter_extend [(ls,sup0,il,inf,ir)] (Hom.fold (fun u _ cont -> u::cont) ls [])

    let hom_of_arrows f =
      match f.maps with
        [hom] -> hom
      | _ -> failwith "Invariant violation, not a flat embedding"

    let (|/) left_to_sup right_to_sup =
      List.fold_left
        (fun pb f ->
          let sup_l = Graph.image f left_to_sup.src in
          List.fold_left
            (fun pb g ->
              let sup_r =  Graph.image g right_to_sup.src in
              let inf = Graph.meet sup_l sup_r in
              let inf_to_left =
                {src = inf ;
                 trg = left_to_sup.src ;
                 maps = [Hom.invert f] ;
                 partial = false}
              in
              let inf_to_right =
                {src = inf ;
                 trg = right_to_sup.src ;
                 maps = [Hom.invert g] ;
                 partial = false}
              in
              (inf_to_left,inf_to_right)::pb
            ) pb right_to_sup.maps
        ) [] left_to_sup.maps

    let (=~=) f f' = match equalize f f' with Some _ -> true | None -> false

    let (/|) inf_to_left inf_to_right =
      let close_rs right_to_sup =
        let part_left_to_sup = inf_to_right @@ (invert inf_to_left) in
        let inf = inf_to_left.src in
        let left = inf_to_left.trg in
        let right = inf_to_right.trg in
        let sup = right_to_sup.trg in
        let hom_p =  hom_of_arrows part_left_to_sup in
        let inf_to_right = hom_of_arrows inf_to_right in
        let inf_to_left = hom_of_arrows inf_to_left in
        let sharing_tiles = extend left hom_p sup inf_to_left inf inf_to_right in
        print_endline "Sharing tiles computed";
        List.fold_left
          (fun (sharing_tiles,exts) (left_to_sup',sup',inf_to_left',inf',inf_to_right') ->
            let emb_inf_left = {src = inf' ;
                                trg = left ;
                                maps = [inf_to_left'] ;
                                partial = false}
            in
            let emb_inf_right = {src = inf' ;
                                 trg = right ;
                                 maps = [inf_to_right'];
                                 partial = false}
            in
            let csp_opt =
              if Graph.is_coherent sup' then
                Some ({src = left ;
                       trg = sup' ;
                       maps = [left_to_sup'] ;
                       partial = false
                      },identity right sup')
              else
                None
            in
            let tile = {span = (emb_inf_left,emb_inf_right) ; cospan = csp_opt} in
            let inf_to_tile = identity inf inf' in
            let arr = try (arrows_of_tile tile) @@ inf_to_tile with Undefined -> inf_to_tile in
            if List.exists (fun arr' -> arr' =~= arr) exts then (sharing_tiles,exts)
            else ((inf_to_tile, tile)::sharing_tiles, arr::exts)
          ) ([],[]) sharing_tiles
      in
      let sharings,_ = close_rs (identity inf_to_right.trg inf_to_right.trg) in
      sharings

    let merge_arrows f f' =
      if (Graph.is_equal f.src f'.src && Graph.is_equal f.trg f'.trg) then
        extension_class {src = f.src ; trg = f.trg ; maps = f.maps@f'.maps; partial = false}
      else
        raise Undefined

    (*[compare f f'] = -1 if exists h: h.f = f', +1 if f = h.f' and 0 otherwise (incomp or iso)*)
    let compare f f' =
      let opt = try Some (complete f f') with Undefined -> None
      in
      let inf,iso =
        match opt with
          Some g -> if not (is_iso g) then true,false else false,true
        | None -> false,false
      in
      if inf then -1 else if iso then 0
      else
        try
          let _ = complete f' f in
          1
        with
          Undefined -> 0


    exception Impossible

    (*fun_next may raise Not_found*)
    let rec extend_to left f inf g right continuation fun_next fun_inf todo =
      List.fold_left
        (fun cont u ->
          List.fold_left
            (fun cont (f,inf,g,todo') ->
              assert (Hom.mem u f && Hom.mem u g) ;
              let u_f,u_g = Hom.find u f,Hom.find u g in
              try
                let candidates_f = fun_next u_f left in
                let candidates_g =  fun_next u_g right in
                List.fold_left
                  (fun cont v_f ->
                    List.fold_left
                      (fun cont v_g ->
                        let new_v =
                          if Hom.comem v_f f then
                            if Hom.comem v_g g then
                              let new_v,new_v' = Hom.cofind v_f f, Hom.cofind v_g g in
                              if new_v = new_v' then new_v
                              else raise Hom.Not_injective
                            else raise Hom.Not_injective
                          else
                            if Hom.comem v_g g then raise Hom.Not_injective
                            else
                              Node.rename ((Graph.max_id inf)+1) v_g
                        in
                        let inf' = fun_inf u new_v inf in
                        try
                          (Hom.add new_v v_f f,
                           inf',
                           Hom.add new_v v_g g,
                           new_v::todo')::cont
                        with
                          Hom.Not_injective | Hom.Not_structure_preserving -> cont
                      ) cont candidates_g
                  ) cont candidates_f
              with
                Not_found -> raise Impossible
            ) cont continuation
        ) [] todo


    let extend_meet fun_next fun_inf left right meet_list best =
      List.fold_left
        (fun (continuation,best) (f,inf,g,todo) ->
          match todo with
            [] -> (continuation,(f,inf,g)::best)
          | _ ->
             begin
               try
                 (extend_to left f inf g right continuation fun_next fun_inf todo,best)
               with Impossible -> (continuation,best)
             end
        ) ([],best) meet_list

    let share_new f g =
      let fun_next_ids u g =
        List.fold_left (fun cont v -> if v<>u then v::cont else cont) [] (Graph.nodes_of_id (Node.id u) g)
      in
      let fun_inf_ids u v g =
        assert (Node.id u = Node.id v) ;
        Graph.add_node v g
      in
      let fun_next_bnd u g =
        Graph.bound_to u g
      in
      let fun_inf_bnd u v g =
        Graph.add_edge u v (Graph.add_node v g)
      in
      let left,right,inf0 = trg f,trg g,src f in
      let rec iter_extend best = function
          [] -> best
        | meet_list ->
           let meet_list,best = (*extending meet list by adding all nodes whose id is already constrained*)
             extend_meet fun_next_ids fun_inf_ids left right meet_list best
           in
           (*extending meet list by adding all nodes that are bound to a node of the domain of the span *)
           let meet_list,best =
             extend_meet fun_next_bnd fun_inf_bnd left right meet_list best
           in
           iter_extend best meet_list
      in
      let spans = iter_extend [] [(hom_of_arrows f,inf0,hom_of_arrows g,Graph.nodes inf0)] in
      let sharings =
        List.map (fun (f,inf,g) ->
            let span = ({src = inf ; trg = left ; maps = [f] ; partial = false},
                       {src = inf ; trg = right ; maps = [g]; partial = false})
            in
            let co_span = None (*TODO*) in
            (identity inf0 inf ,{span = span ; cospan = co_span})
          ) spans
      in
      sharings

    let share f g = (*one should add here all midpoints (partially ordered), what about kappa??*)
      print_endline "Entering sharing function" ;
      let compare_sharing (f,tile) (f',tile') =
        let n = compare f f' in
        if n = 0 then
          match upper_bound tile, upper_bound tile' with
            None, None | Some _, Some _ -> 0
            | None, Some _ -> -1
            | Some _ , None -> 1
        else
          n
      in
      let tiles = (f /| g) in
      print_endline "Mpos computed" ;
      let ipos =
        List.filter
          (fun (f,tile) ->
            Graph.is_connex f.trg
          ) tiles
      in
      List.fold_left
        (fun cont (f,tile as sh) ->
          if List.for_all (fun sh' -> (compare_sharing sh sh') = 0) cont
          then
            sh::cont
          else cont
        ) [] (List.rev (List.fast_sort compare_sharing ipos))

    let glue g h =
      (*returns spans of the form g <-id- g1 -f-> h where g1 is an edge of g*)
      (*both branches of the spans are up to eq class*)
      let subparts g h =
        let subs =
          Graph.fold_edge_types
            (fun u v cont ->
              let g1 = Graph.add_edge u v (Graph.add_node u (Graph.add_node v Graph.empty))
              in
              (flatten (g1 => g))@cont
            ) g []
        in
        List.fold_left
          (fun cont emb_g1_g ->
            let g1 = emb_g1_g.src in
            (*optim: restricting to extension class will not miss matches of obs*)
            let emb_g1_h_list = try flatten (extension_class (g1 => h)) with Undefined -> [] in
            List.fold_left
              (fun cont emb_g1_h ->
                (emb_g1_g,emb_g1_h)::cont
              ) cont emb_g1_h_list
          ) [] subs
      in
      List.fold_left
        (fun cont (to_g,to_h) ->
          (to_g /| to_h)@cont
        ) [] (subparts g h)

    (** [h |> obs] [h] may create/destroy an instance of obs*)
    let (|>) h obs =
      try
        let wit_list = flatten (extension_class (h => obs)) in
        List.fold_left (fun tiles h_to_o ->
            {span = (identity h h, h_to_o) ; cospan = Some (h_to_o,identity obs obs)}::tiles
          ) [] wit_list
      with Undefined -> []

                          (*
      let eq_tile obs_right tile tile' =
        match tile.cospan,tile'.cospan with
          None,_ -> raise Undefined
        | _,None -> raise Undefined
        | Some (left_to_sup,right_to_sup),Some (left_to_sup',right_to_sup') ->
           if db () then
             assert (Graph.is_equal left_to_sup.src left_to_sup'.src
                     && Graph.is_equal right_to_sup.src right_to_sup'.src) ;

           if obs_right then (left_to_sup  =~= left_to_sup') else (right_to_sup  =~= right_to_sup')
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
                      ) cont then
                   cont
                 else
                   tile::cont
          ) [] (glue h obs)
                           *)

                          end:Category with type obj = Graph.Make(Node).t)
