module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)

    let (-->) = Cat.(-->)
    let (@@) = Cat.(@@)
    let (|/) = Cat.(|/)
    let (=~=) = Cat.(=~=)
    let (++) = Lib.IntSet.union

    type arrows = Cat.arrows
    type obj = Cat.obj
    open Lib.Util

    type point = {value : Graph.t ;
                  next : Cat.arrows Lib.IntMap.t ;
                  obs : (Cat.arrows * int) list ;
                  conflict : Lib.IntSet.t ;
                  down : Lib.IntSet.t
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
       obs = [] ;
       conflict = Lib.IntSet.empty ;
       down = Lib.IntSet.empty
      }

    let empty h_eps =
      {points = Lib.IntMap.add 0 (point h_eps) Lib.IntMap.empty ;
       witnesses = Lib.IntSet.empty;
       extensions = Lib.IntMap.add 0 (Cat.identity h_eps h_eps) Lib.IntMap.empty ;
       max_elements = Lib.IntSet.singleton 0 ;
       fresh = 1
      }

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
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let is_empty ext_base = (Lib.IntMap.cardinal ext_base.points = 1)

    let find i ext_base = Lib.IntMap.find i ext_base.points

    let find_extension i ext_base =
      if not (mem i ext_base) then
        failwith ("Unkown point "^(string_of_int i)^" in extension base")
      else
        Lib.IntMap.find i ext_base.extensions

    exception Found of Cat.arrows list


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
      let _ = if db() then
                if Lib.IntMap.mem j pi.next then
                  print_string
                    (red (Printf.sprintf "\t Removing step %d |-x-> %d\n" i j))
      in
      replace i {pi with next = Lib.IntMap.remove j pi.next} ext_base

    let add_step i j emb_ij ext_base =
      let () =
        if db() then Printf.printf "Verifying if %d|->%d should be added...\n" i j
      in
      let pi =
        try find i ext_base
        with Not_found -> raise (Invariant_failure (Printf.sprintf "Point %d is not in the base" i,ext_base))
      in
      let pj =
        try find j ext_base
        with Not_found -> raise (Invariant_failure (Printf.sprintf "Point %d is not in the base" j,ext_base))
      in
      if Lib.IntSet.mem i pj.down then (if db() then print_endline "No!" ; ext_base)
      else
        let () = if db() then Printf.printf
                                "\t Add Step %d |-> %d = %s-%s->%s\n" i j
                                (Graph.to_string (Cat.src emb_ij))
                                (Cat.string_of_arrows emb_ij)
                                (Graph.to_string (Cat.trg emb_ij))
        in
        let ext_base =
          replace i
            {pi with next = Lib.IntMap.add j emb_ij pi.next}
            {ext_base with max_elements = Lib.IntSet.remove i ext_base.max_elements}
        in
        replace j
          {pj with down = pj.down ++ pi.down ++ (Lib.IntSet.singleton i)}
          ext_base

    type sharing_info = {to_w : Cat.arrows ;
                         to_base : Cat.arrows ;
                         to_midpoint : Cat.arrows ;
                         has_sup : bool}
    type comparison =
      Iso of Cat.arrows
    | Below of Cat.arrows
    | Above of Cat.arrows
    | Incomp of sharing_info
    | Conflicting

    let string_of_comparison = function
        Iso _ -> "Iso"
      | Below _ -> "Below"
      | Above _ -> "Above"
      | Incomp _ -> "Incomp"
      | Conflicting -> "Conflict"

    let compare inf_to_i inf_to_w =
      if db() then
        Printf.printf "\t Sharing %s\n"  (Cat.string_of_span (inf_to_i,inf_to_w)) ; flush stdout ;
      match Cat.share inf_to_i inf_to_w with
        [] -> [Conflicting]
      | lcomp ->
         let lcomp =
           List.fold_left
             (fun cont (inf_to_sh,sharing_tile) ->
               let sh_to_base,sh_to_w = Cat.lower_bound sharing_tile in
               let _ =
                 if db() then
                   let sup_info = match Cat.upper_bound sharing_tile with
                       Some (ext,_) -> Graph.to_string (Cat.trg ext)
                     | None -> "No sup"
                   in
                   Printf.printf
                     "Sharing (%s) is %s\n"
                     sup_info (Cat.string_of_span (sh_to_base,sh_to_w))
               in
               let iso_to_w = Cat.is_iso sh_to_w in
               let iso_to_base = Cat.is_iso sh_to_base in
               if iso_to_w then
                 if iso_to_base then
                   let () = if db() then
                              assert (
                                  inf_to_i =~= inf_to_w
                                )
                   in
                   (Iso (sh_to_base @@ (Cat.invert sh_to_w) ))::cont (*Iso: w (<)--> i *)
                 else
                   (Below (sh_to_base @@ (Cat.invert sh_to_w) ))::cont (*Below wit -> i*)
               else
                 if iso_to_base then
                   (Above (sh_to_w @@ (Cat.invert sh_to_base) ))::cont (*Above i -> wit *)
                 else
                   match Cat.upper_bound sharing_tile
                   with
                     None -> (Incomp {to_w = sh_to_w ;
                                      to_base = sh_to_base ;
                                      to_midpoint = inf_to_sh ;
                                      has_sup = false})::cont
                   | Some _ -> (Incomp {to_w = sh_to_w ;
                                        to_base = sh_to_base ;
                                        to_midpoint = inf_to_sh ;
                                        has_sup = true})::cont
             ) [] lcomp
         in
         print_endline "end of compare" ; flush stdout ;
         lcomp

    exception Found_iso of Cat.arrows * int

    type inf_path = {beta : (int*arrows*arrows*arrows) list Lib.IntMap.t ; alpha: (int*arrows) Lib.IntMap.t}

    let print_inf_path ip =
      Lib.IntMap.iter
        (fun i l ->
          Printf.printf "Beta(%d):=[%s]\n" i
            (String.concat ","
               (List.map (fun (j,f,g,h) -> (string_of_int j) ^":"^ (Cat.string_of_arrows ~full:true h)) l))
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
      add_step i' j' (to_j' @@ (a_ij @@ (Cat.invert to_i'))) ext_base

    let rm_step_alpha i j ext_base inf_path =
      remove_step (alias i inf_path) (alias j inf_path) ext_base

    let find_extension_alpha i ext_base inf_path =
      find_extension (alias i inf_path) ext_base

    let add_conflict_alpha i j ext_base inf_path =
      add_conflict (alias i inf_path) (alias j inf_path) ext_base

(*    let is_below_alpha i j ext_base inf_path =
      let rec search ext_base = function
          [] -> false
        | i::cont ->
           let pi = try find (alias i inf_path) ext_base
                    with Not_found ->
                      raise (Invariant_failure (Printf.sprintf "Point %d is not in the base" i,ext_base))
           in
           if Lib.IntMap.mem (alias j inf_path) pi.next then raise Exit
           else
             let cont' =
               Lib.IntMap.fold (fun k _ cont -> k::cont) pi.next cont
             in
             search ext_base cont'
      in
      try
        let pi = find (alias i inf_path) ext_base
        in
        let next =
          Lib.IntMap.fold
            (fun k _ cont -> if (alias k inf_path) = (alias j inf_path) then raise Exit else k::cont
            ) pi.next []
        in
        search ext_base next
      with
        Exit -> true
 *)

    let rec progress ext_base dry_run visited inf_path queue max_step =
      (************* DEBUGING INFO ***************)
      let _ = if db() then
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
                    "Visited {%s}\n"
		    (String.concat ","
		       (List.map string_of_int (Lib.IntSet.elements visited))
		    ) ;
                  flush stdout
                end
      in
      (************* DEBUGING INFO ***************)
      let dec_step ext_base = function
          None -> None
        | Some i ->
           if i=1 then raise (Invariant_failure (red "Max iteration reached", ext_base))
           else
             Some (i-1)
      in
      let add_alias i i' to_i' alpha =
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
      let update_inf i (newp,root_to_newp,newp_to_i,newp_to_w as new_inf) inf_path ext_base =
        let alpha',infs_i =
          List.fold_left
            (fun (alpha,infs_i) (oldp,root_to_oldp,oldp_to_i,oldp_to_w as old_inf) ->
              let (to_oldp,to_newp) = try List.hd (oldp_to_i |/ newp_to_i) with _ -> failwith "could not compute pullback"
              in
              if Cat.is_iso to_oldp && Cat.is_iso to_newp then
                if oldp = newp then (alpha, old_inf::infs_i)
                else
                  if oldp < newp then (*aliasing newp ~> oldp and not modifying beta*)
                    (add_alias newp oldp (to_oldp @@ (Cat.invert to_newp)) alpha, old_inf::infs_i)
                  else (*aliasing oldp ~> newp and replacing old_inf by new_inf in beta*)
                    (add_alias oldp newp (to_newp @@ (Cat.invert to_oldp)) alpha, new_inf::infs_i)
              else
                (alpha,old_inf::infs_i)
            ) (inf_path.alpha,[]) (try Lib.IntMap.find i inf_path.beta with Not_found -> [])
        in
        let infs_i = if infs_i = [] then [new_inf] else infs_i in
        let inf_path' = {beta = Lib.IntMap.add i infs_i inf_path.beta ; alpha = alpha'} in
        if db() then print_inf_path inf_path' ;
        inf_path'
      in

      let get_best_inf i ip = Lib.IntMap.find i ip.beta
      in
      if QueueList.is_empty queue then (inf_path,dry_run)
      else
        let k,step_ki,i = QueueList.pop queue in
        let inf_list =
          try get_best_inf k inf_path
          with Not_found -> raise (Invariant_failure (Printf.sprintf "Point %d has no defined best_inf" k, ext_base))
        in
        let dry_run',visited',inf_path',queue',max_step'=
          List.fold_left (*folding inf_list*)
            (fun (dry_run,visited,inf_path,queue,max_step) (inf,root_to_inf,inf_to_k,inf_to_w) ->
              let inf_to_i = try step_ki @@ inf_to_k
                             with
                               Cat.Undefined ->
                               print_endline ("cannot compose "
                                              ^(Cat.string_of_arrows ~full:true inf_to_k)
                                              ^" and "
                                              ^(Cat.string_of_arrows ~full:true step_ki)) ;
                               raise Cat.Undefined
              in
              let _ = if db() then Printf.printf "Visiting (%d -*-> %d |-> %d )\n" inf k i in
              flush stdout ;
              let lcomp = compare inf_to_i inf_to_w in
              let () =
                if db() then
                  Printf.printf "Comparisons found : {%s}\n" (String.concat "," (List.map string_of_comparison lcomp))
              in
              List.fold_left (*folding compare inf_to_i inf_to_w*)
                (fun (dry_run,visited,inf_path,queue,max_step) -> function

                    (************************** Case Conflicting span ********************************)
                    (*1. best_inf,aliases = (root_to_inf,inf_to_i,inf,inf_to w) +!> best_inf (i) *)
                    (*2. add i...#...w to dry_run *)
                    (*3. if i is not visited yet, add i |-> k (for all succ(i)) to next_layer*)
                    (*4. add i to visited *)

                    Conflicting ->
                     if db() then print_string (red "Conflicting points\n");
                     let inf_path'=
                       update_inf
                         i
                         (inf,root_to_inf,inf_to_i,inf_to_w)
                         inf_path
                         ext_base
                     in
                     let dry_run' =
                       (fun w ext_base inf_path -> add_conflict_alpha i w ext_base inf_path)::dry_run
                     in

                     let queue' =
                       if Lib.IntSet.mem i visited then
                         queue
                       else
                         Lib.IntMap.fold
                           (fun j step_ij cont ->
                             QueueList.add_fifo (i,step_ij,j) cont ; cont
                           ) (find i ext_base).next queue
                     in
                     let visited' = Lib.IntSet.add i visited in
                     (dry_run',visited',inf_path',queue',dec_step ext_base max_step)

                    (************************** Case inf_to_w factors inf_to_i ********************************)
                    (*1. best_inf,aliases = (root_to_inf,inf_to_i,inf,inf_to w) +!> best_inf (i) *)
                    (*2. add inf |-x-> i and w |-> i to dry_run NB: inf |-> w will eventually be added*)
                    (*3. add i to visited *)
                    (*NB no todo list to update here*)
                    | Below w_to_i -> (* w --w_to_i--> i *)
                       if db() then print_string (blue ("below "^(string_of_int i)^"\n"));
                       let inf_path' =
                         update_inf
                           i
                           (inf,root_to_inf,inf_to_i,inf_to_w)
                           inf_path
                           ext_base
                       in
                       let dry_run' =
		         ((fun w ext_base inf_path ->
                           (*no check and no aliasing necessary here*)
                           rm_step_alpha inf i (add_step_alpha w i w_to_i ext_base inf_path) inf_path
                         )::dry_run)
                       in
                       let visited' = Lib.IntSet.add i visited in
                       (dry_run',visited',inf_path',queue,dec_step ext_base max_step)

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
                       assert (alias i inf_path = i) ;
                       let g_i = Cat.src i_to_w in
                       let inf_path' =
                         update_inf i
                           (i, inf_to_i @@ root_to_inf, Cat.identity g_i g_i, i_to_w)
                           inf_path
                           ext_base
                       in
                       let queue' =
                         if Lib.IntSet.mem i visited then
                           queue
                         else
                           Lib.IntMap.fold
                             (fun j step_ij cont ->
                               QueueList.add_lifo (i,step_ij,j) cont ; cont
                             ) (find i ext_base).next queue
                       in
                       (dry_run,(Lib.IntSet.add i visited), inf_path' ,queue', dec_step ext_base max_step)

                    (************************** Case inf_to_w =~= inf_to_i *************************)
                    (*NB drop dry_run*)
                    | Iso iso_w_i ->
                       if db() then print_string (red "iso\n") ;
                       raise (Found_iso (iso_w_i,i))

                    (************** Case both inf_to_w and inf_to_i have a common factor ***********)
                    | Incomp sh_info ->
                       if db() then print_string
			              (green (Printf.sprintf
                                                "I found a midpoint %s (%d)!\n"
					        (Graph.to_string
                                                   (Cat.trg sh_info.to_midpoint)
                                                )
					        ext_base.fresh
                                         )
			              );
		       (*No better comparison with w exists*)
                       (*1. best_inf,_ = (root_to_inf,inf_to_i,inf,inf_to_w) +!> best_inf (i)*)
                       (*2. add i |-> succ i to next_layer if i not visited*)
                       (*3. if sharing span has no sup add i ..#.. w to dry_run*)
                       (*4. mark i as visited *)
                       if Cat.is_iso sh_info.to_midpoint then
                         let () = if db() then print_string (green "...that is not worth adding\n") in
                         let inf_path' =
                           update_inf i (inf,root_to_inf,inf_to_i,inf_to_w) inf_path ext_base
                         in
		         let queue' =
                           if Lib.IntSet.mem i visited then
                             queue
                           else
                             Lib.IntMap.fold
                               (fun j step_ij cont ->
                                 QueueList.add_fifo (i,step_ij,j) cont ; cont
                               ) (find i ext_base).next queue
                         in
                         let dry_run' =
                           if not sh_info.has_sup then
                             (fun w ext_base inf_path -> add_conflict_alpha i w ext_base inf_path)::dry_run
                           else
                             dry_run
		         in
                         (dry_run',(Lib.IntSet.add i visited),inf_path',queue',dec_step ext_base max_step)
                       else
                         (*Not a trivial midpoint*)
                         let queue' =
                           if Lib.IntSet.mem i visited then
                             queue
                           else
                             Lib.IntMap.fold
                               (fun j step_ij cont ->
                                 QueueList.add_fifo (i, step_ij, j) cont ; cont
                               ) (find i ext_base).next queue
                         in
                         let fresh_id = get_fresh ext_base in
                         let inf_path' =
                           update_inf i
                             (fresh_id,sh_info.to_midpoint @@ root_to_inf,sh_info.to_base,sh_info.to_w)
                             inf_path
                             ext_base
                         in
                         let dry_run' =
                           (fun w ext_base inf_path ->
                             let skip_midpoint = (alias fresh_id inf_path) <> fresh_id in
                             let ext_base =
                               if skip_midpoint then ext_base
                               else
                                 let mp = point (Cat.trg sh_info.to_midpoint) in
                                 let ext_base =
                                   add fresh_id
                                     mp
                                     (sh_info.to_midpoint @@ (find_extension_alpha inf ext_base inf_path))
                                     ext_base
                                 in
                                 add_step_alpha fresh_id i sh_info.to_base ext_base inf_path
                             in
                             (*adding step from inf to midpoint or its alias
                               (in this case verify that inf is not already below the alias*)
                             let ext_base =
                               (*if skip_midpoint && (is_below_alpha inf fresh_id ext_base inf_path)
                               then ext_base
                               else*)
                                 add_step_alpha
                                   inf
                                   fresh_id
                                   sh_info.to_midpoint
                                   ext_base
                                   inf_path
                             in
		             let ext_base = if sh_info.has_sup then ext_base else add_conflict i w ext_base in
                             rm_step_alpha inf i ext_base inf_path (*will remove steps only if they exists and they are direct*)
                           )::dry_run
                         in
		         (dry_run',(Lib.IntSet.add i visited),inf_path',queue',dec_step ext_base max_step)
                ) (dry_run,visited,inf_path,queue,max_step) lcomp
            ) (dry_run,visited,inf_path,queue,max_step) inf_list
        in
        progress ext_base dry_run' visited' inf_path' queue' max_step'

    let insert ~max_step ext_w obs_emb obs_id ext_base =
      let p0 = find 0 ext_base in
      let id_0 = Cat.identity p0.value p0.value in
      try
        let beta_0 = Lib.IntMap.add 0 [(0,id_0,id_0,ext_w)] Lib.IntMap.empty in
        let alpha_0 = Lib.IntMap.empty in
        let inf_path_0 = {beta = beta_0 ; alpha = alpha_0} in
        let queue_0 = QueueList.create () in
        QueueList.add_fifo (0,id_0,0) queue_0 ;
        let visited_0 = Lib.IntSet.empty in
        let dry_run_0 = [] in
        let inf_path,dry_run = progress ext_base dry_run_0 visited_0 inf_path_0 queue_0 max_step
        in
        let () = if db() then print_inf_path inf_path in
        (* 1. Adding witness point *)
        let w = get_fresh ext_base in
        let _ = if db() then print_string (blue (Printf.sprintf "Inserting witness with id %d\n" w)) ; flush stdout in
        let ext_base = add w (point (Cat.trg ext_w)) ext_w ext_base in
        let ext_base = add_obs w obs_emb obs_id ext_base in
        (* 2. Executing dry run, i.e inserting midpoints *)
        let ext_base =
          List.fold_left (fun ext_base act -> act w ext_base inf_path) ext_base (List.rev dry_run)
        in
        (* 3. Connecting witness w to its best predecessors in the base*)
        let inf_list =
          Lib.IntSet.fold
          (fun i inf_list ->
            let infs_i = try Lib.IntMap.find i inf_path.beta with Not_found -> []
            in
            infs_i @ inf_list
          ) ext_base.max_elements []
        in
        let compare_infs (i,_,_,_) (j,_,_,_) =
          let i = alias i inf_path in
          let j = alias j inf_path in
          if Lib.IntSet.mem i (find j ext_base).down then -1
          else
            if Lib.IntSet.mem j (find i ext_base).down then 1
            else 0
        in
        let inf_list = List.fast_sort compare_infs inf_list in
        let () =
          if db() then
            Printf.printf "best infs for witness %d are {%s}\n"
              w
              (String.concat "," (List.map (fun (i,_,_,_) -> string_of_int i) inf_list))
        in
        let ext_base =
          List.fold_left
            (fun ext_base (inf,_,_,inf_to_w) ->
              if inf=w then ext_base
              else
                add_step_alpha inf w inf_to_w ext_base inf_path
            ) ext_base inf_list
        in
        add_step 0 w ext_w ext_base
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
              List.fold_left (fun (ext_base,z,l,r) tiles -> iter_convert z l r tiles ext_base) (eb,0,l,r) tiles_l
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
