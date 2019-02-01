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

    val size : arrows -> int
    val wf : arrows -> bool


    (* val share : arrows -> arrows -> (arrows * tile) list*)
    val share : arrows -> arrows -> (arrows * arrows * arrows * bool
) list

    val is_iso : arrows -> bool
    val is_identity : arrows -> bool
    val invert : arrows -> arrows
    val flatten : arrows -> arrows list
    val extension_class : arrows -> arrows
    val matching_class : arrows -> arrows
    (*val equalize : arrows -> arrows -> arrows option*)
    (*val compare : arrows -> arrows -> int*)

    (**Operators*)
    val compose : ?check:bool -> arrows -> arrows -> arrows
    val aliasing : arrows -> arrows -> arrows option
    (*    val (|/) : arrows -> arrows -> (arrows * arrows) list*)
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
    module Term = ANSITerminal
    type obj = Graph.t

    module NodeSet = Set.Make (Node)
    open Lib.Util

    exception Undefined

    type arrows = {src : obj ; trg : obj ; maps : Hom.t list ; partial : bool}
    let unit = {src = Graph.empty ; trg = Graph.empty ; maps = [] ; partial = false}

    let size f = (Graph.size_edge f.trg) - (Graph.size_edge f.src)

    type tile = {span : arrows * arrows ; cospan : (arrows * arrows) option}

    let flat f = match f.maps with [_] -> true | _ -> false

    let fold_arrow ars =
      let ar = List.hd ars.maps in
      Hom.fold (fun u v cont -> (Node.id u, Node.id v)::cont) ar []

    let is_identity f = List.for_all (fun h -> Hom.is_identity h) f.maps

    let is_partial f =
      match f.maps with
        [] -> true
      | h::_ ->
         try
           Graph.fold_nodes
             (fun u _ ->
               if not (Hom.mem u h) then raise Exit
             ) f.src () ;
           false
         with Exit -> true

    let wf f =
      assert (flat f) ;
      try
        List.iter
          (fun hom -> Hom.fold
                        (fun u v _ ->
                          if Graph.has_node u f.src && Graph.has_node v f.trg then ()
                          else
                            let () =
                              if db() then
                                Printf.printf "(%s,%s) is problematic" (Node.to_string u) (Node.to_string v)
                            in
                            raise Exit
                        ) hom ()
          ) f.maps ; true
      with
        Exit -> false

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
      str0^(col (String.concat "+" (List.map (Hom.to_string ~full:full) f.maps)))^str1

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
          str'^"<-"^(Hom.to_string ~full:true (List.hd f.maps))
          ^"-"^str^"-"^(Hom.to_string ~full:true (List.hd f'.maps))^"->"^str''
        end
      else
        let str0 = Printf.sprintf " %s " (Graph.to_string f.src) in
        let str1 = Printf.sprintf " %s " (Graph.to_string f'.src) in
        let str' = Printf.sprintf " %s " (Graph.to_string f.trg) in
        let str'' = Printf.sprintf " %s " (Graph.to_string f'.trg) in
        print_string
          (str'^"<-"^(string_of_arrows ~full:true f)^"-"^str0^"<<>>"^str1^"-"
           ^(string_of_arrows ~full:true f')^"->"^str'') ;
        failwith "Invalid argument"


    let string_of_cospan (f,f') =
      if safe() then assert (is_cospan (f,f')) ;
      let str = Printf.sprintf " %s " (Graph.to_string f.trg) in
      let str' = Printf.sprintf " %s " (Graph.to_string f.src) in
      let str'' = Printf.sprintf " %s " (Graph.to_string f'.src) in
      str'^"-"^(Hom.to_string ~full:true (List.hd f.maps))^"->"^str^"<-"^(Hom.to_string ~full:true (List.hd f'.maps))^"-"^str''

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

    (*Assuming two coinitial and cofinal arrows*)
    let (===) f f' =
      assert (not (f.partial || f'.partial) && flat f && flat f') ;
      let h,h' = List.hd f.maps,List.hd f'.maps in
      Hom.is_equal h h'

    let embed _G _H =
      let rec extend hom_list iG jG acc =
	match hom_list with
	  [] -> acc
	| phi::tl ->
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
	    hom_extended_with_candidates_u @ hom_list
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

    let compose ?(check=true) f f' =
      if safe() then assert (flat f && flat f') ;
      let hom = List.hd f.maps in
      let hom' = List.hd f'.maps in
      try
        {src = f'.src ;
         trg = f.trg ;
         maps = [Hom.compose ~check:check hom hom'];
         partial = f.partial || f'.partial
        }
      with
        Hom.Undefined ->
        let () = if db() then
                   Printf.printf "Cannot compose %s and %s\n"
                     (string_of_arrows ~full:true f)
                     (string_of_arrows ~full:true f')
        in
        let () = if safe () then
                   assert (Graph.wf f.src && Graph.wf f.trg && wf f && wf f')
        in
        raise Undefined


    let eq_class matching f auto =
      let close_span hom hom' =
	try
	  Hom.fold (fun u v phi ->
	      if safe() then assert (Hom.mem u hom') ;
	      let v' = Hom.find u hom' in
	      Hom.add v v' phi
	    ) hom Hom.empty
	with
	  Hom.Not_structure_preserving | Hom.Not_injective -> failwith "Invariant violation"
      in
      let close_co_span hom hom' =
	try
	  Hom.fold (fun u v phi ->
	      if safe() then assert (Hom.comem v hom') ;
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
      if safe() then assert (reduced_maps <> []) ;
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

    let (@@) = compose ~check:true

    let is_iso f =
      not f.partial
      && (Graph.size_edge f.trg) = (Graph.size_edge f.src)
      && Graph.size_node f.trg = Graph.size_node f.trg

    let invert f =
      let f' = {src = f.trg ;
                trg = f.src ;
                maps = List.map Hom.invert f.maps ;
                partial = false}
      in
      {f' with partial = Graph.size_node f'.src > Graph.size_node f'.trg}


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

    let hom_of_arrows f =
      if safe() then assert (wf f) ;
      match f.maps with
        [hom] -> hom
      | _ -> failwith "Invariant violation, not a flat embedding"

    let aliasing f g =
      let () =
        if safe() then assert (is_cospan (f,g)) ;
        if db() then
          Printf.printf "Building iso from cospan: \n <%s,%s>\n"
            (string_of_arrows ~full:true f) (string_of_arrows ~full:true g)
      in
      if (Graph.size_node f.src, Graph.size_edge f.src) <> (Graph.size_node g.src, Graph.size_edge g.src)
      then None
      else
        let hom = hom_of_arrows f in
        let hom' = Hom.invert (hom_of_arrows g) in
        let () =
          if db() then
            Term.printf [Term.yellow] "Composing (%s o %s)"
              (Hom.to_string ~full:true hom') (Hom.to_string ~full:true hom)
        in
        try
          let h = {src = f.src ; trg = g.src ; maps = [Hom.compose hom' hom] ; partial = false} in
          if is_iso h then
            Some h
          else
            None
        with Hom.Undefined -> None

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
                 maps = [Hom.restrict (Hom.invert f) (Graph.nodes inf)] ;
                 partial = false}
              in
              let inf_to_right =
                {src = inf ;
                 trg = right_to_sup.src ;
                 maps = [Hom.restrict (Hom.invert g) (Graph.nodes inf)] ;
                 partial = false}
              in
              let () =
                if safe() then
                  begin
                    assert (Graph.wf inf_to_left.src) ;
                    assert (Graph.wf inf_to_left.trg) ;
                    assert (Graph.wf inf_to_right.src) ;
                    assert (Graph.wf inf_to_right.trg) ;
                  end
              in
              (inf_to_left,inf_to_right)::pb
            ) pb right_to_sup.maps
        ) [] left_to_sup.maps

    let (=~=) f f' = match equalize f f' with Some _ -> true | None -> false

    let span_of_partial f_part =
      let p_hom = hom_of_arrows f_part in
      let () =
        if db() then
          (Term.printf [Term.red] "Building span of partial map %s --%s--\\ %s\n"
             (Graph.to_string f_part.src)
             (Hom.to_string ~full:true p_hom)
             (Graph.to_string f_part.trg) ; flush stdout)
      in
      let dom =
        Graph.fold_nodes (fun u d ->
            if Hom.mem u p_hom then
              if List.exists
                   (fun v ->
                     Hom.mem v p_hom
                     && Graph.has_edge (Hom.find u p_hom) (Hom.find v p_hom) f_part.trg
                   ) (Graph.bound_to u d)
              then d
              else
                let () =
                  if db() then
                    Printf.printf "removing %s because it has no binding partner\n" (Node.to_string u)
                in
                Graph.remove u d
            else
              let () = if db() then
                         Printf.printf
                           "removing %s because it is not in the domain of partial hom\n" (Node.to_string u)
              in
              Graph.remove u d
          ) f_part.src f_part.src
      in
      let inf_to_left = identity dom f_part.src in
      let inf_to_right =
        {src = dom ; trg = f_part.trg ; maps = [p_hom] ; partial = false}
      in
      if safe() then assert (not (is_partial inf_to_right)) ;
      (inf_to_left,inf_to_right)


    let share f g =
      let left,right = f.trg,g.trg in
      let f_0 = hom_of_arrows (g @@ invert f) in
      let todo_0 =
        List.fold_left (fun cont u ->
            List.fold_left
              (fun cont v -> if Hom.mem v f_0 then cont else v::cont
              ) cont (Graph.nodes_of_id (Node.id u) left)
          ) [] (Hom.domain f_0)
      in
      let rec iter_extend hom_p todo conflict =
        match todo with
          [] -> (hom_p,conflict)
        | u::tl ->
           if Hom.mem u hom_p then iter_extend hom_p tl conflict
           else
             let () = if db() then Printf.printf "Extending node %s \n" (Node.to_string u) in
             let candidates =
               Graph.nodes_of_id (Hom.find_sub (Node.id u) hom_p) right
             in
             match (List.filter (fun v -> Node.compatible u v) candidates) with
               [] -> iter_extend hom_p tl conflict
             | [v] ->
                begin
                  try
                    let u' = List.hd (Graph.bound_to u left) in
                    let v' = List.hd (Graph.bound_to v right) in
                    let () = if db() then
                               Term.printf [] "Trying (%s,%s0 |-> (%s,%s) \n"
                                 (Node.to_string u) (Node.to_string u') (Node.to_string v) (Node.to_string v')
                    in
                    let hom_p' = Hom.add u v (Hom.add u' v' hom_p) in
                    let () = if db() then Term.printf [Term.green] "Success!\n" in
                    let todo' =
                      List.fold_left
                        (fun cont v -> if Hom.mem v hom_p' then cont else v::cont
                        ) tl (Graph.nodes_of_id (Node.id u') left)
                    in
                    iter_extend hom_p' todo' conflict
                  with
                    Hom.Not_injective | Hom.Not_structure_preserving ->
                                         let () = if db() then Term.printf [Term.red] "Failed!\n"
                                         in iter_extend hom_p tl true
                end
             | _ -> failwith "rigidity violation"
      in
      let hom_p,conflict = iter_extend f_0 todo_0 false in
      let (f',g') = span_of_partial {src=left ; trg = right ; maps = [hom_p] ; partial = true} in
      (*Construction guarantees that f' is the identity*)
      assert (is_identity f') ;
      if db () then Printf.printf "Returning span %s\n\n" (string_of_span (f',g')) ;
      if safe() then assert (Graph.wf left && Graph.wf right) ;
      let sh =
        {src = f.src ; trg = f'.src ; maps = [hom_of_arrows f] ; partial = false}
      in
      let () =
        if safe() then assert (Graph.wf f.src);
        if safe() then assert (Graph.wf f'.src);
      in
      [(sh,f',g',conflict)]

    (** [h |> obs] [h] may create/destroy an instance of obs*)
    let (|>) h obs =
      try
        let arrows = h => obs in
        let wit_list = flatten (extension_class arrows) in
        List.fold_left (fun tiles h_to_o ->
            {span = (identity h h, h_to_o) ; cospan = Some (h_to_o,identity obs obs)}::tiles
          ) [] wit_list
      with Undefined -> []


 end:Category with type obj = Graph.Make(Node).t)

