module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    module Term = ANSITerminal

    let (-->) = Cat.(-->)
    let (@@) = Cat.compose ~check:false
    let (=~=) = Cat.(=~=)
    let (++) = Lib.IntSet.union

    type arrows = Cat.arrows
    type obj = Cat.obj
    open Lib.Util

    type point = {value : Graph.t ;
                  next : Cat.arrows Lib.IntMap.t ;
                  prev : Lib.IntSet.t ;
                  obs : (Cat.arrows * int) list ;
                  conflict : Lib.IntSet.t ;
                 }

    type t = {points : point Lib.IntMap.t ; (*corresp int -> point *)
              (*set of points that are witnesses (not midpoints) *)
              witnesses : Lib.IntSet.t ;
              (* i |-->  (0 -->i) --extension from root to i*)
              extensions : Cat.arrows Lib.IntMap.t ;
              max_elements : Lib.IntSet.t ;
              mutable fresh : int ;
             }

    exception Invariant_failure of string * t

    let point g =
      {value = g ;
       next = Lib.IntMap.empty ;
       prev = Lib.IntSet.empty ;
       obs = [] ;
       conflict = Lib.IntSet.empty ;
      }

    let empty h_eps =
      {points = Lib.IntMap.add 0 (point h_eps) Lib.IntMap.empty ;
       witnesses = Lib.IntSet.empty;
       extensions = Lib.IntMap.add 0 (Cat.identity h_eps h_eps) Lib.IntMap.empty ;
       max_elements = Lib.IntSet.singleton 0 ;
       fresh = 1
      }

    let dump eb =
      Lib.IntMap.iter
      (fun i p ->
        let next = Lib.IntMap.fold (fun j _ cont -> (Printf.sprintf "%d" j)::cont) p.next []
        in
        Term.printf [] "%d |--> [%s]\n" i (String.concat "," next);
      ) eb.points


    let to_dot show_conflict dict ext_base =
      let l =
        Lib.IntMap.fold
          (fun i p dot_string ->
            let str =
              match p.obs with
                [] -> Printf.sprintf "%d [label =\"%d\" , shape = none] ;" i i
              | ol ->
                 Printf.sprintf
                   "%d [label=\"%d [obs: %s]\" , shape = \"%s\"];" i
                   i
                   (String.concat ","
                      (List.map (fun (_,x) ->
                           Lib.Dict.to_name x dict
                         ) ol))
                   (if Lib.IntMap.is_empty p.next then "rectangle" else "oval")
            in
            let str2 =
              String.concat "\n"
                (Lib.IntMap.fold
                   (fun j _ dot_string ->
                     (Printf.sprintf "%d -> %d ;" i j)::dot_string
                   ) p.next [])
            in
            let str3 =
              String.concat
                "\n"
                (Lib.IntSet.fold
                   (fun j dot_string ->
                     if i < j then
                       (Printf.sprintf
                          "%d -> %d [conflict = \"true\" style = \"dotted\", dir = \"none\", constraint = false];" i j)::dot_string
                     else
                       dot_string
                   ) p.conflict [])
            in
            (str^"\n"^str2^"\n"^(if show_conflict then str3 else ""))::dot_string
          ) ext_base.points []
      in
      "digraph G{\n"^(String.concat "\n" l)^"\n}"

    let add i p ext_p ext_base =
      {points = Lib.IntMap.add i p ext_base.points ;
       witnesses =
         begin
           match p.obs with
             [] -> ext_base.witnesses
           | _ -> Lib.IntSet.add i ext_base.witnesses
         end ;
       extensions = Lib.IntMap.add i ext_p ext_base.extensions ;
       max_elements = Lib.IntSet.add i ext_base.max_elements ;
       fresh = ext_base.fresh
      }

    let get_fresh ext_base =
      let i = ext_base.fresh in
      ext_base.fresh <- ext_base.fresh + 1 ;
      i

    let replace i p ext_base =
      if safe() then assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let is_empty ext_base = (Lib.IntMap.cardinal ext_base.points = 1)

    let find i ext_base = Lib.IntMap.find i ext_base.points

    let find_extension i ext_base =
      if not (mem i ext_base) then
        failwith ("Unkown point "^(string_of_int i)^" in extension base")
      else
        Lib.IntMap.find i ext_base.extensions

    (**[is_in_sup i j eb] evaluates to true if [j] is in the sup of [i] in extension base [eb]*)
    let is_in_sup i j ext_base =
      assert (mem i ext_base && mem j ext_base) ;
      let pj = find j ext_base
      in
      let size_of p = (Graph.size_edge p.value, Graph.size_node p.value) in
      let (<<) (u,v) (u',v') = u <= u' && v<= v' in
      let sj = size_of pj in
      let rec iter_search todo visited =
        match todo with
          [] -> false
        | k::todo' ->
           if Lib.IntSet.mem k visited then
             iter_search todo' visited
           else
             let pk = find k ext_base in
             if (size_of pk) << sj then
               if k = j || Lib.IntMap.mem j pk.next then true
               else
                 iter_search
                   (Lib.IntMap.fold (fun j' _ todo' -> j'::todo') pk.next todo')
                   (Lib.IntSet.add k visited)
             else  (*j cannot be above k*)
               iter_search todo' (Lib.IntSet.add k visited)
      in
      iter_search [i] Lib.IntSet.empty

    (*returns the set of pairs (u,v) that would violate Hasse property if i |-->j is added*)
    let hasse_violation i j ext_base =
      assert (mem i ext_base && mem j ext_base) ;
      let pi = find i ext_base in
      let size_of p = (Graph.size_edge p.value, Graph.size_node p.value) in
      let (<<) (u,v) (u',v') = u <= u' && v<= v' in
      let si = size_of pi in
      let rec iter_search todo visited violations =
        match todo with
          [] -> violations
        | k::todo' ->
           if Lib.IntSet.mem k visited then
             iter_search todo' visited violations
           else
             let pk = find k ext_base in
             let violations' =
               Lib.IntSet.fold
                 (fun k' violations ->
                   let pk' = find k' ext_base in
                   if size_of pk' << si then
                     if is_in_sup k' i ext_base then Lib.Int2Set.add (k',k) violations
                     else violations
                   else
                     violations
                 ) pk.prev violations
             in
             iter_search
               (Lib.IntMap.fold (fun j' _ todo' -> j'::todo') pk.next todo')
               (Lib.IntSet.add k visited)
               violations'
      in
      iter_search [j] Lib.IntSet.empty Lib.Int2Set.empty


    let add_conflict i j ext_base =
      if db() then Printf.printf "\t %d...#...%d\n" i j ;
      let pi = find i ext_base in
      let pj = find j ext_base in
      replace i {pi with conflict = Lib.IntSet.add j pi.conflict}
        (replace j {pj with conflict = Lib.IntSet.add i pj.conflict} ext_base)

    let add_obs i ext obs_id ext_base =
      let pi = find i ext_base in
      let pi =
        match pi.obs with
          [] -> {pi with obs = [ext,obs_id]}
        | obs_ids -> {pi with obs = (ext,obs_id)::obs_ids}
      in
      replace i pi ext_base

    let remove_step i j ext_base =
      let pi =
        try
          find i ext_base
        with Not_found -> raise (Invariant_failure (Printf.sprintf "Point %d is not in the base" i,ext_base))
      in
      let pj =
        try
          find j ext_base
        with Not_found -> raise (Invariant_failure (Printf.sprintf "Point %d is not in the base" j,ext_base))
      in
      let _ = if db() then
                if Lib.IntMap.mem j pi.next then
                  print_string
                    (red (Printf.sprintf "\t Removing step %d |-x-> %d\n" i j))
      in
      let eb =
        replace j {pj with prev = Lib.IntSet.remove i pj.prev}
          (replace i {pi with next = Lib.IntMap.remove j pi.next} ext_base)
      in
      if safe () then
        begin
          let pi = find i eb in
          let pj = find j eb in
          assert (not (Lib.IntMap.mem j pi.next || Lib.IntSet.mem j pj.prev)) ;
        end ;
      eb

    let add_step i j emb_ij ext_base =
      let () =
        if db() then Printf.printf "Verifying if %d|->%d should be added...\n" i j
      in
      let pi =
        try find i ext_base
        with Not_found -> raise (Invariant_failure (Printf.sprintf "Point %d is not in the base" i,ext_base))
      in
      (*optim*)
      if Lib.IntMap.mem j pi.next || is_in_sup i j ext_base then
        begin
          if db() then Printf.printf "Point %d is in the future of %d, not adding step.\n" j i ;
          ext_base
        end
      else
      let rm_edges = hasse_violation i j ext_base in
      if db() then
        begin
          Printf.printf
            "\t Add Step %d |-> %d = %s-%s->%s\n" i j
            (Graph.to_string (Cat.src emb_ij))
            (Cat.string_of_arrows emb_ij)
            (Graph.to_string (Cat.trg emb_ij)) ;
          if not (Lib.Int2Set.is_empty rm_edges) then
            Printf.printf "this step would generate violations {%s}!\n"
              (String.concat "," (List.map (fun (x,y) -> Printf.sprintf "(%d,%d)" x y) (Lib.Int2Set.elements rm_edges)))
        end ;
      let ext_base =
        Lib.Int2Set.fold
          (fun (x,y) ext_base ->
            remove_step x y ext_base
          ) rm_edges ext_base
      in
      (*NB pi might have changed in the ext_base because of previous step*)
      let pi,pj = find i ext_base, find j ext_base in
      if safe() then assert (not (Lib.Int2Set.mem (i,j) rm_edges)) ;
      replace j
        {pj with prev = Lib.IntSet.add i pj.prev}
        (replace i
           {pi with next = Lib.IntMap.add j emb_ij pi.next}
           {ext_base with max_elements = Lib.IntSet.remove i ext_base.max_elements})

    type comparison =
      Iso of Cat.arrows
    | Below of Cat.arrows
    | Above of Cat.arrows
    | Incomp of (Cat.arrows * Cat.arrows * Cat.arrows) list (*inf_to_sh,sh_to_base,sh_to_w*)

    let compare inf_to_i inf_to_w =
      if db() then
        Printf.printf "\t Sharing %s\n"  (Cat.string_of_span (inf_to_i,inf_to_w)) ; flush stdout ;
      match Cat.share inf_to_i inf_to_w with
        [] -> failwith "Empty sharing"
      | (inf_to_sh,sh_to_base,sh_to_w)::_ as sharings ->
         let iso_to_w = Cat.is_iso sh_to_w in
         let iso_to_base = Cat.is_iso sh_to_base in
         if iso_to_w then
           if iso_to_base then
             let () = if safe() then
                        if (inf_to_i =~= inf_to_w) then assert true
                        else
                          begin
                            Term.printf [Term.red] "Error: %s and %s are not extensionally equivalent!\n"
                            (Cat.string_of_arrows ~full:true inf_to_i) (Cat.string_of_arrows ~full:true inf_to_w) ;
                            assert false
                          end

             in
             let () = if safe () then assert (List.length sharings = 1)
             in
             Iso (sh_to_base @@ (Cat.invert sh_to_w))
           else
             let () = if safe () then assert (List.length sharings = 1)
             in
             Below (sh_to_base @@ (Cat.invert sh_to_w))
         else
           if not iso_to_base then
             Incomp sharings
           else
             let () = if safe () then assert (List.length sharings = 1)
             in
             Above (sh_to_w @@ (Cat.invert sh_to_base))

    exception Found_iso of Cat.arrows * int

    type inf_path = {beta : (int*arrows*arrows*arrows) list Lib.IntMap.t ; alpha: (int*arrows) Lib.IntMap.t}

    let print_inf_path ip =
      Lib.IntMap.iter
        (fun i inf_list ->
          Term.printf [] "Beta(%d) := [%s]\n " i
            (String.concat ","
               (List.map
                  (fun (j,_,_,_) ->
                    Term.sprintf [Term.blue] "%d" j
                  ) inf_list
               )
            )
        ) ip.beta ;
      Lib.IntMap.iter
        (fun i (j,f) ->
          Printf.printf "%d ~> %d\n" i j
        ) ip.alpha

    let alias i inf_path =
      try Lib.Util.proj_left (Lib.IntMap.find i inf_path.alpha) with Not_found -> i

    let add_step_alpha i j a_ij ext_base inf_path =
      let i',to_i' = try Lib.IntMap.find i inf_path.alpha with Not_found -> (i,Cat.identity (Cat.src a_ij) (Cat.src a_ij)) in
      let j',to_j' = try Lib.IntMap.find j inf_path.alpha with Not_found -> (j,Cat.identity (Cat.trg a_ij) (Cat.trg a_ij)) in
      if safe() then assert (Cat.is_iso to_i') ;
      let f = a_ij @@ (Cat.invert to_i') in
      let g = to_j' @@ f in
      add_step i' j' g ext_base

    let find_extension_alpha i ext_base inf_path =
      find_extension (alias i inf_path) ext_base

    let add_conflict_alpha i j ext_base inf_path =
      add_conflict (alias i inf_path) (alias j inf_path) ext_base

    let string_of_sharings sharings =
      String.concat "," (List.map (fun (to_midpoint,_,_) -> Graph.to_string (Cat.trg to_midpoint)) sharings)

    exception Iso_found of (int * Cat.arrows) Lib.IntMap.t

    let rec progress ext_base dry_run compared inf_path queue max_step cut =

      (************* DEBUGING INFO ***************)
      let () =
        if safe () then
          let _ =
            QueueList.fold (fun (k,_,i) lhs ->
                let i' = alias i inf_path in
                assert (if  (Lib.IntSet.mem i' lhs) then
                          let () =
                            Printf.printf
                              "Queue is not well formed for %d (%d) : \n {%s}\n" i i'
                              (String.concat
                                 ","
                                 (QueueList.fold
                                    (fun (i,_,j) cont ->
                                      ("("^(string_of_int i)^"|->"^(string_of_int j)^")")::cont
                                    ) queue [])
                              )
                          in
                          (flush stdout ; false)
                        else true
                  ) ;
                Lib.IntSet.add k lhs
              ) queue Lib.IntSet.empty
          in
          ()
      in
      let () = if db() then
                begin
                  Printf.printf
                    "Queue: {%s}\n"
                    (String.concat
                       ","
                       (QueueList.fold
                          (fun (i,_,j) cont ->
                            ("("^(string_of_int i)^"|->"^(string_of_int j)^")")::cont
                          ) queue [])
                    ) ;
                  Printf.printf
                    "Compared {%s}\n"
		    (String.concat ","
		       (List.map (fun (x,y) -> Term.sprintf [Term.yellow] "%d|->%d" x y) (Lib.Int2Set.elements compared))
		    ) ;
                  flush stdout
                end
      in
      (************* DEBUGING INFO ***************)

      let subst i j set =
        Lib.IntSet.add i (Lib.IntSet.remove j set)
      in
      let dec_step ext_base = function
          None -> None
        | Some i ->
           if i=1 then raise (Invariant_failure (red "Max iteration reached", ext_base))
           else
             Some (i-1)
      in
      let add_alias i i' to_i' alpha =
        if safe () then
          begin
            assert (alias i inf_path = i) ;
            assert (not (mem i ext_base))
          end ;
        let i',to_i' =
          try
            let j,to_j = Lib.IntMap.find i' alpha in (j,to_j @@ to_i')
          with Not_found -> (i',to_i')
        in
        let alpha =
          Lib.IntMap.fold
            (fun j (j',to_j') alpha ->
              if j'=i then Lib.IntMap.add j (i', to_i' @@ to_j') alpha
              else
                alpha
            ) alpha alpha
        in
        Lib.IntMap.add i (i',to_i') alpha
      in
(*
      let update_inf i (newp,root_to_newp,newp_to_i,newp_to_w as new_inf) inf_path ext_base =
        let alpha', beta' =
          try
            let oldp,root_to_oldp,oldp_to_i,oldp_to_w = Lib.IntMap.find i inf_path.beta
            in
            if newp = oldp then inf_path.alpha,inf_path.beta
            else
              let iso_old_to_new = Cat.aliasing oldp_to_i newp_to_i in
              if safe() then
                begin
                  Term.printf [Term.yellow] "Checking that both midpoints (%d,%d) are isomorphic...\n" oldp newp ; flush stdout ;
                  assert (Cat.is_iso iso_old_to_new) ;
                  Term.printf [Term.yellow] "OK\n" ; flush stdout
                end;
              if newp > oldp then
                (*let new_to_old = to_oldp @@ (Cat.invert to_newp) in*)
                add_alias newp oldp (Cat.invert iso_old_to_new) inf_path.alpha,inf_path.beta
              else
                add_alias oldp newp iso_old_to_new inf_path.alpha,Lib.IntMap.add i new_inf inf_path.beta
          with Not_found -> inf_path.alpha,Lib.IntMap.add i new_inf inf_path.beta
        in
        let inf_path' = {beta = beta' ; alpha = alpha'} in
        if db() then print_inf_path inf_path' ;
        inf_path'
      in
 *)

      let update_infs i inf_list inf_path ext_base =
        (*newp might be a hard point while oldp a temporary one*)
        let unify_meet ((newp,root_to_newp,newp_to_i,newp_to_w) as nw) old_infs alpha =
          List.fold_left
            (fun (is_found,alpha,infs) ((oldp,root_to_oldp,oldp_to_i,oldp_to_w) as old) ->
              if is_found then (is_found,alpha,old::infs)
              else
                if newp = oldp then (true,alpha,old::infs)
                else
                  let old_to_new = Cat.aliasing oldp_to_i newp_to_i in
                  if Cat.is_iso old_to_new then
                    if newp > oldp then
                      (true,add_alias newp oldp (Cat.invert old_to_new) alpha,old::infs)
                    else
                      (true, add_alias oldp newp old_to_new alpha, nw::infs)
                  else
                    (is_found, alpha, old::infs)
            ) (false,alpha,[]) old_infs
        in
        match (try Lib.IntMap.find i inf_path.beta with Not_found -> []) with

          (*inf_list is the first comparison between i and the witness*)
          [] -> {inf_path with beta = Lib.IntMap.add i inf_list inf_path.beta}
        | old_inf_list ->
           let alpha,updated_inf_list =
             List.fold_left
               (fun (alpha,infs) new_inf ->
                 let iso_found,alpha,infs = unify_meet new_inf infs alpha in
                 if iso_found then (alpha,infs)
                 else (alpha,new_inf::infs)
               ) (inf_path.alpha,old_inf_list) inf_list
           in
           {alpha=alpha ; beta=Lib.IntMap.add i updated_inf_list inf_path.beta}
      in

      let get_best_inf i ip =
        List.map
          (fun (inf,root_to_inf,inf_to_k,inf_to_w) ->
            try
              let inf',to_inf' = Lib.IntMap.find inf ip.alpha in
              let from_inf' = Cat.invert to_inf' in
              (inf', to_inf' @@ root_to_inf, inf_to_k @@ from_inf', inf_to_w @@ from_inf')
            with
              Not_found -> (inf,root_to_inf,inf_to_k,inf_to_w)
          ) (Lib.IntMap.find i ip.beta)
      in

      if QueueList.is_empty queue then (inf_path,dry_run,cut)
      else
        let k,step_ki,i =
          let k,step_ki,i = QueueList.pop queue in

          if safe() then assert (alias k inf_path = k) ;
          try
            let i',to_i' = Lib.IntMap.find i inf_path.alpha in
            (k, to_i' @@ step_ki, i')
          with Not_found -> (k,step_ki,i)
        in
        let pi = find i ext_base in
        let is_complete =
          Lib.IntSet.fold
            (fun j b ->
              let j' = alias j inf_path in
              if j' = j && j<>k then Lib.Int2Set.mem (j,i) compared && b
              else b
            ) pi.prev true
        in

        let dry_run',compared',inf_path',queue',max_step',cut'=

          (*folding over the list of best infs of k and w*)
          List.fold_left
            (fun (dry_run,compared,inf_path,queue,max_step,cut) (inf,root_to_inf,inf_to_k,inf_to_w) ->
              let () = if safe() then assert (alias inf inf_path = inf) in
              let inf_to_i = step_ki @@ inf_to_k in
              let () = if db() then (
                         Printf.printf "Visiting (%d -*-> %d |-> %d )\n" inf k i ;
                         flush stdout )
              in

              match compare inf_to_i inf_to_w with

              (************************** Case inf_to_w factors inf_to_i ********************************)
              (*1. best_inf,aliases = (root_to_inf,inf_to_i,inf,inf_to w) +!> best_inf (i) *)
              (*2. add inf |-x-> i and w |-> i to dry_run NB: inf |-> w will eventually be added*)
              (*3. add i to visited *)
              (*NB no todo list to update here*)
              | Below w_to_i -> (* w --w_to_i--> i *)
                 let () = if db() then print_string (blue ("below "^(string_of_int i)^"\n")) in
                 let dry_run' =
	           ((fun w ext_base inf_path ->
                     let ext_base = add_step_alpha inf w inf_to_w ext_base inf_path in
                     add_step_alpha w i w_to_i ext_base inf_path
                   )::dry_run)
                 in
                 let compared' = Lib.Int2Set.add (k,i) compared in
                 (dry_run',compared',inf_path,queue,dec_step ext_base max_step, cut)

              (************************** Case inf_to_i factors inf_to_w *******************)
              (*1. best_inf,_ = (root_to_i,id_i,i,i_to_w) +!> best_inf (i) *)
              (*NB: no new alias here. no dry_run to add*)
              (*2. add step i |-> k (for all succ k) to TODO to emulate Depth first*)
              (*3. add i to visited *)

              | Above i_to_w -> (* i --i_to_w--> w *)
                 if db() then print_string
                                ((yellow ("above "))
                                 ^(string_of_int i)
                                 ^" through "^
                                   (Cat.string_of_arrows ~full:true i_to_w)^"\n") ;
                 if safe() then assert (
                                    if not (alias i inf_path = i) then
                                      (Printf.printf "Something wrong point %d is aliased to %d\n" i (alias i inf_path) ;
                                       false)
                                    else
                                      true
                                  ) ;
                 let g_i = Cat.src i_to_w in
                 let inf_path' =
                   update_infs i
                     [(i, inf_to_i @@ root_to_inf, Cat.identity g_i g_i, i_to_w)]
                     inf_path
                     ext_base
                 in
                 let queue' =
                   if not is_complete then (*if not complete, the step i |--> x should not be pushed on the queue*)
                     queue
                   else
                     Lib.IntMap.fold
                       (fun j step_ij cont ->
                         QueueList.add_hp (i, step_ij, j) cont (*trying to find iso first*)
                       ) pi.next queue
                 in
                 let compared' = Lib.Int2Set.add (k,i) compared
                 in
                 (dry_run, compared' , inf_path' ,queue', dec_step ext_base max_step, subst i inf cut)

              (************************** Case inf_to_w =~= inf_to_i *************************)
              (*NB drop dry_run*)
              | Iso iso_w_i ->
                 if db() then print_string (red "iso\n") ;
                 raise (Found_iso (iso_w_i,i))

              (************** Case both inf_to_w and inf_to_i have a common factor ***********)
              | Incomp sh_info ->
                 let queue' =
                   if not is_complete then (*if not complete, the step i |--> x should not be pushed on the queue*)
                     queue
                   else
                     Lib.IntMap.fold
                       (fun j step_ij cont ->
                         QueueList.add_lp (i, step_ij, j) cont
                       ) (find i ext_base).next queue
                 in
                 let to_midpoint,to_base,to_w = List.hd sh_info in
                 let has_sup = true in
                 let compared' = Lib.Int2Set.add (k,i) compared
                 in
                 if db() then print_string
			        (green (Printf.sprintf
                                          "I found %d midpoint(s) {%s}!\n"  (List.length sh_info) (string_of_sharings sh_info)
                                   )
			        );
	         (*No better comparison with w exists*)
                 (*1. best_inf,_ = (root_to_inf,inf_to_i,inf,inf_to_w) +!> best_inf (i)*)
                 (*2. add i |-> succ i to next_layer if i not visited*)
                 (*3. if sharing span has no sup add i ..#.. w to dry_run*)
                 (*4. mark i as visited *)

                 if Cat.is_iso to_midpoint then
                   let () = if db() then print_string (green "...that is not worth adding\n") in
                   let inf_path' =
                     update_infs i [inf,root_to_inf,inf_to_i,inf_to_w] inf_path ext_base
                   in
                   let dry_run' =
                     if not has_sup then
                       (fun w ext_base inf_path -> add_conflict_alpha i w ext_base inf_path)::dry_run
                     else
                       dry_run
	           in
                   (dry_run',compared',inf_path',queue',dec_step ext_base max_step, cut)
                 else
                   (*Not a trivial midpoint*)
                   let fresh_ids,inf_list =
                     List.fold_left (fun (fresh_ids,inf_list) (to_midpoint,to_base,to_w) ->
                         let id = get_fresh ext_base in (*side effect*)
                         let () =
                           if db() then
                             Term.printf [Term.cyan] "Midpoint %d: %s\n" id (Graph.to_string (Cat.trg to_midpoint))
                         in
                         (id::fresh_ids,(id,to_midpoint @@ root_to_inf,to_base,to_w)::inf_list)
                       ) ([],[]) sh_info
                   in
                   let inf_path' =
                     update_infs i
                       inf_list
                       inf_path
                       ext_base
                   in
                   let dry_run' =
                     (fun w ext_base inf_path ->
                       List.fold_left (fun ext_base fresh_id ->
                           let mp_id,iso_mp =  (* fresh_id ---iso_mp--> mp_id *)
                             try Lib.IntMap.find fresh_id inf_path.alpha
                             with Not_found -> (fresh_id,Cat.identity (Cat.trg to_midpoint)  (Cat.trg to_midpoint))
                           in
                           let mp = point (Cat.trg iso_mp) in
                           let inf_id,iso_inf = (* inf ---iso_inf--> inf_id *)
                             try Lib.IntMap.find inf inf_path.alpha
                             with Not_found ->
                               (inf, Cat.identity (Cat.src to_midpoint)  (Cat.src to_midpoint))
                           in
                           let inf_to_mp = iso_mp @@ (to_midpoint @@ (Cat.invert iso_inf)) in (*inf_to_mp: inf_id |--> mp_id*)
                           let mp_to_base = to_base @@ (Cat.invert iso_mp) in (* mp_to_base : mp_id |--> i *)
                           let ext_to_mp = inf_to_mp @@ (find_extension inf_id ext_base) in (*ext_to_mp: root |--> mp_id *)

                           (*adding root --*--> mp_id in the extension base *)
                           let ext_base =
                             if mem mp_id ext_base then ext_base
                             else
                               add mp_id mp ext_to_mp ext_base
                           in
                           let ext_base = add_step mp_id i mp_to_base ext_base
                           in
                           (*adding step from inf to midpoint or its alias
                     (in this    case verify that inf is not already below the alias*)
                           let ext_base = add_step inf_id mp_id inf_to_mp ext_base
                           in
		           if has_sup then ext_base else add_conflict i w ext_base
                         ) ext_base fresh_ids
                     )::dry_run
                   in
	           (dry_run',compared',inf_path',queue',dec_step ext_base max_step,
                    List.fold_left (fun cut fresh_id -> subst fresh_id inf cut) cut fresh_ids)
            ) (dry_run,compared,inf_path,queue,max_step,cut) (get_best_inf k inf_path)
        in
        progress ext_base dry_run' compared' inf_path' queue' max_step' cut'


    let insert ~max_step ext_w obs_emb obs_id ext_base =
      let p0 = find 0 ext_base in
      let id_0 = Cat.identity p0.value p0.value in
      try
        let beta_0 = Lib.IntMap.add 0 [0,id_0,id_0,ext_w] Lib.IntMap.empty in
        let alpha_0 = Lib.IntMap.empty in
        let inf_path_0 = {beta = beta_0 ; alpha = alpha_0} in
        let queue_0 =
          QueueList.add_hp (0,id_0,0) (QueueList.create ())
        in
        let compared_0 = Lib.Int2Set.empty in
        let dry_run_0 = [] in
        let inf_path,dry_run,cut = progress ext_base dry_run_0 compared_0 inf_path_0 queue_0 max_step (Lib.IntSet.singleton 0)
        in
        let () = if db() then print_inf_path inf_path in
        (* 1. Adding witness point *)
        let w = get_fresh ext_base in
        let _ =
          if db() then
            begin
              print_string (blue (Printf.sprintf "Inserting witness with id %d\n" w)) ;
              print_string (Printf.sprintf "Cut is {%s}\n" (String.concat "," (List.map string_of_int (Lib.IntSet.elements cut)))) ;
              flush stdout
            end
        in
        let ext_base = add w (point (Cat.trg ext_w)) ext_w ext_base in
        let ext_base = add_obs w obs_emb obs_id ext_base in

        (* 2. Executing dry run, i.e inserting midpoints *)
        let ext_base =
          List.fold_left
            (fun ext_base act ->
              let eb = act w ext_base inf_path in
              eb
            ) ext_base (List.rev dry_run)
        in
        if db() then
          (Term.printf [Term.Blink ; Term.magenta] "Dry run executed!\n" ;
           dump ext_base) ;
        (* 3. Connecting witness w to its best predecessors in the base*)
        let inf_list =
          Lib.IntSet.fold
          (fun i inf_list ->
              try (Lib.IntMap.find i inf_path.beta)@inf_list with Not_found -> inf_list
          ) ext_base.max_elements []
        in

        let () =
          if db() then
            Printf.printf "best infs for witness %d are {%s}\n"
              w
              (String.concat "," (List.map (fun (i,_,_,_) -> string_of_int i) inf_list))
        in
        let ext_base =
          List.fold_left
            (fun ext_base (inf,_,_,inf_to_w) ->
              if inf=w || not (Lib.IntSet.mem inf cut) then (if db() then Printf.printf "%d not in cut skipping\n" inf ; ext_base)
              else
                add_step_alpha inf w inf_to_w ext_base inf_path
            ) ext_base (List.rev inf_list)
        in
        ext_base
      with
        Found_iso (iso_w_i,i) -> add_obs i (iso_w_i @@ obs_emb) obs_id ext_base


    let of_sharings tiles_l =
      let rec iter_convert z l r tiles ext_base =
        match tiles with
          [] -> let z,l,r = get_fresh ext_base, get_fresh ext_base, get_fresh ext_base in (ext_base,z,l,r)
        | (root_to_inf,tile)::tiles' ->
           let ext_base =
             if mem z ext_base then ext_base
             else
               let root = Cat.src root_to_inf in
               add z (point root) (Cat.identity root root) ext_base in
           let ext_base =
             let (inf_to_left,inf_to_right) = Cat.lower_bound tile in
             let i = get_fresh ext_base in
             let conflict = match Cat.upper_bound tile with None -> true | _ -> false in
             let inf = point (Cat.src inf_to_left) in
             let left = point (Cat.trg inf_to_left) in
             let right = point (Cat.trg inf_to_right) in
             let ext_base = add i inf root_to_inf ext_base in
             let ext_base = if mem l ext_base then ext_base else add l left (inf_to_left @@ root_to_inf) ext_base in
             let ext_base = if mem r ext_base then ext_base else add r right (inf_to_right @@ root_to_inf) ext_base in
             let ext_base = if conflict then add_conflict l r ext_base else ext_base in
             let ext_base = add_step z i root_to_inf
                              (add_step i l inf_to_left
                                 (add_step i r inf_to_right ext_base))
             in
             match Cat.upper_bound tile with
               None -> ext_base
             | Some (left_to_sup,right_to_sup) ->
                let s = get_fresh ext_base in
                let sup = point (Cat.trg left_to_sup) in
                let ext_base = add s sup ((Cat.arrows_of_tile tile) @@ root_to_inf) ext_base in
                add_step l s left_to_sup (add_step r s right_to_sup ext_base)
           in
           iter_convert z l r tiles' ext_base
      in
      match tiles_l with
        [] -> empty (Graph.empty)
      | hd::_ ->
         match hd with
           [] -> failwith "error"
         | (f,_)::_ ->
            let inf = Cat.src f in
            let eb,_,_,_ =
              let eb = empty inf in
              let l = get_fresh eb in
              let r = get_fresh eb in
              List.fold_left
                (fun (ext_base,z,l,r) tiles ->
                  iter_convert z l r tiles ext_base
                ) (eb,0,l,r) tiles_l
            in
            eb

    let to_dot_corresp ext_base =
      let str_list,_ =
        Lib.IntMap.fold
          (fun i p (str_list,fresh) ->
            let f = find_extension i ext_base in
            let _G = List.hd ((Cat.src f) --> f) in
            match p.obs with
              [] -> let str,name,fresh = Graph.to_dot_cluster ~sub:_G p.value i fresh in
                    (str::str_list,fresh)
            | _ -> (str_list,fresh)
          ) ext_base.points ([],0)
      in
      "digraph G{\n"^(String.concat "\n" str_list)^"\n}"

    let to_dot_content ext_base =
      let str_list =
        Lib.IntMap.fold
          (fun i p str_list ->
            let f = find_extension i ext_base in
            let pairs = List.map (fun (u,v) -> (v,u)) (Cat.fold_arrow f) in
            (Graph.to_dot p.value ~highlights:pairs (string_of_int i))::str_list
          ) ext_base.points []
      in
      (String.concat "\n" str_list)

  end
