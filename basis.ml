module type ExtensionBasisType =
  sig
    type t
    type arrows
    type obj
    val to_dot : ?show_conflict:bool -> Lib.Dict.t -> t -> string
    val to_dot_corresp : t -> string
    val to_dot_content : t -> string
    val insert : arrows -> arrows -> int -> t -> t
    val empty : obj -> t
  end

module Make (Node:Node.NodeType) =
  (struct
      module Graph = Graph.Make (Node)
      module Cat = Cat.Make (Node)

      let (-->) = Cat.(-->)
      let (|/) = Cat.(|/)
      let (=~=) = Cat.(=~=)

      type arrows = Cat.arrows
      type obj = Cat.obj
      open Lib.Util

      type point = {value : Graph.t ;
                    next : Cat.arrows Lib.IntMap.t ;
                    obs : (Cat.arrows * int) list ;
                    conflict : Lib.IntSet.t ;
                   }

      type t = {points : point Lib.IntMap.t ; (*corresp int -> point *)
                (*set of points that are witnesses (not midpoints) *)
                witnesses : Lib.IntSet.t ;
                (* i |-->  (0 -->i) --extension from root to i*)
                extensions : Cat.arrows Lib.IntMap.t ;
                max_elements : Lib.IntSet.t ;
                mutable fresh : int
               }


      let point g =
        {value = g ;
         next = Lib.IntMap.empty ;
         obs = [] ;
         conflict = Lib.IntSet.empty ;
        }


      let to_dot ?(show_conflict=true) dict ext_base =
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
                          "%d -> %d [style = \"dotted\", dir = \"none\", constraint = false];" i j)::dot_string
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

      let empty h_eps =
        {points = Lib.IntMap.add 0 (point h_eps) Lib.IntMap.empty ;
         witnesses = Lib.IntSet.empty;
         extensions = Lib.IntMap.add 0 (Cat.identity h_eps h_eps) Lib.IntMap.empty ;
         max_elements = Lib.IntSet.singleton 0 ;
         fresh = 1
        }

      let is_empty ext_base = (Lib.IntMap.cardinal ext_base.points = 1)

      let find i ext_base = Lib.IntMap.find i ext_base.points

      let (@@) = Cat.(@@)

      let find_extension i ext_base =
        if not (mem i ext_base) then
          failwith ("Unkown point "^(string_of_int i)^" in extension base")
        else
          Lib.IntMap.find i ext_base.extensions

      exception Found of Cat.arrows list

      let delta i j ext_base =
        let rec compose emb_list acc =
          match emb_list with
            [] -> acc
          | emb::tl -> compose tl (acc @@ emb)
        in
        let rec dfs i ext visited =
          if db() then Printf.printf "Exploring %d...\n" i ;
          if i = j then (ext,visited)
          else
            if Lib.IntSet.mem i ext_base.max_elements then ([],visited)
            else
              let pi = find i ext_base in
              let ext,visited =
                Lib.IntMap.fold
                  (fun k hom_ik (ext,visited) ->
                   match ext with
                     [] -> if Lib.IntSet.mem k visited then (ext,visited)
                           else dfs k (hom_ik::ext) (Lib.IntSet.add k visited)
                   | _ -> raise (Found ext)
                  ) pi.next (ext,visited)
              in
              if ext <> [] then raise (Found ext)
              else
                (ext,visited)
        in
        if i = 0 then Some (find_extension j ext_base) (*optim!*)
        else
          try
            let _ = dfs i [] Lib.IntSet.empty
            in
            None
          with
            Found ext ->
            let pi = find i ext_base in
            Some (compose ext (Cat.identity pi.value pi.value))


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
        let pi = find i ext_base in
        let _ = if db() then
                  if Lib.IntMap.mem j pi.next then
                    print_string
                      (red (Printf.sprintf "\t Removing step %d |-x-> %d\n" i j))
        in
        replace i {pi with next = Lib.IntMap.remove j pi.next} ext_base

      let is_below i j ext_base =
        let rec search ext_base = function
            [] -> false
          | i::cont ->
             let pi = try find i ext_base
                      with Not_found ->
                        failwith (Printf.sprintf "%d is not in the base..." i)
             in
             if Lib.IntMap.mem j pi.next then raise Exit
             else
               let cont' =
                 Lib.IntMap.fold (fun k _ cont -> k::cont) pi.next cont
               in
               search ext_base cont'
        in
        try
          let pi = find i ext_base
          in
          let next =
            Lib.IntMap.fold
              (fun k _ cont -> if k=j then raise Exit else k::cont
              ) pi.next []
          in
          search ext_base next
        with
          Exit -> true

      let add_step ?(check=false) ?(aliases=Lib.IntMap.empty) i j emb_ij ext_base =
        if db() then Printf.printf "Checking whether step %d |-> %d should be added\n" i j ;
        let j,emb_ij =
          try
            let j_to_k,k = Lib.IntMap.find j aliases in
            let () = if db() then Printf.printf "Aliasing %d |-> %d to %d |-> %d\n " i j i k
            in
            (k,j_to_k @@ emb_ij)
          with
            Not_found -> (j,emb_ij)
        in
        let ext_base = if i <> 0 then remove_step 0 j ext_base else ext_base (*This is weird, not the general case...*)
        in
        if (check && is_below i j ext_base) then ext_base
        else
          let pi = try find i ext_base with Not_found -> failwith "Invariant violation"
          in
          if db() then Printf.printf
                         "\t Add Step %d |-> %d = %s-%s->%s\n" i j
                         (Graph.to_string (Cat.src emb_ij))
                         (Cat.string_of_arrows emb_ij)
                         (Graph.to_string (Cat.trg emb_ij)) ;
          replace i
                  {pi with next = Lib.IntMap.add j emb_ij pi.next}
                  {ext_base with max_elements = Lib.IntSet.remove i ext_base.max_elements}

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


      let compare inf_to_i inf_to_w ext_base =
        if db() then
          Printf.printf "\t Sharing %s\n"  (Cat.string_of_span (inf_to_i,inf_to_w)) ;
        match Cat.share inf_to_i inf_to_w with
          [] -> [Conflicting]
        | lcomp ->
           let () = if db() then
                      (
                        if List.length lcomp > 1 then
                          print_string "Multiple sharings detected!\n" ;
                        (List.iter (fun (_,sharing_tile) ->
                             Printf.printf "%s\n" (Cat.string_of_tile sharing_tile)) lcomp ;
                         print_newline()
                        )
                      )
           in
           (*let lcomp = [List.hd lcomp] in*)

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
                  (if db() then
                     Printf.printf
                       "Trying to compose obs_emb : %s o %s \n"
                       (Cat.string_of_arrows ~full:true sh_to_base)
                       (Cat.string_of_arrows ~full:true (Cat.invert sh_to_w)) ;
                   (Iso (sh_to_base @@ (Cat.invert sh_to_w) ))::cont (*Iso: w (<)--> i *)
                  )
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


      exception Found_iso of Cat.arrows * int

      let rec progress ext_base dry_run visited best_inf aliases next_layer todo =
        (************* DEBUGING INFO ***************)
        let _ = if db() then
                  begin
                    Printf.printf
                      "stack: {%s}\n"
                      (String.concat
                         ","
                         (List.map
                            (fun (i,_,j) ->
                             "("^(string_of_int i)^"|->"^(string_of_int j)^")"
                            ) todo
                         )
                      ) ;
                    Printf.printf
                      "next calls: {%s}\n"
                      (String.concat
                         ","
                         (List.map
                            (fun (i,_,j) ->
                             "("^(string_of_int i)^"|->"^(string_of_int j)^")") next_layer)
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
        let update_best_inf ?(replace_if_found=true) i (root_to_inf,inf_to_i,inf,inf_to_w as new_inf) m a =
          try
            let _ = if db() then Printf.printf "Adding %d as best inf for %d...\n" inf i in
            let cut = try Lib.IntMap.find i m with Not_found -> [] in
            let cut',aliasing_opt =
              List.fold_left
                (fun (cut,aliasing_opt) (root_to_mp,_,mp,_ as old_inf) ->
                  if mp = inf then
                    let () = if db() then Printf.printf "%d already present\n" inf ; flush stdout ;
                    in
                    raise Exit (*to avoid auto aliasing*)
                  else
                      if root_to_mp =~= root_to_inf then
                        match Cat.share root_to_mp root_to_inf with
                          (_,sh_tile)::_ ->
                           let (to_mp,to_inf) = Cat.lower_bound sh_tile
                           in
                           assert (Cat.is_iso to_mp && Cat.is_iso to_inf) ;
                           if replace_if_found then
                             let () = if db() then Printf.printf "aliasing %d (replaced) -> %d \n" mp inf
                             in
                             (new_inf::cut, Some (mp, to_inf @@ (Cat.invert to_mp), inf)) (* (old_inf -~-> new_inf, old_inf) *)
                           else
                             let () = if db() then Printf.printf "aliasing %d (not inserted) -> %d \n" inf mp in
                             (old_inf::cut, Some (inf, to_mp @@ (Cat.invert to_inf), mp)) (* (new_inf -~-> old_inf, old_inf) *)
                        | _ -> failwith "invariant violation"
                      else
                        (old_inf::cut,aliasing_opt)
                ) ([],None) cut
            in
            match aliasing_opt with
              None -> (Lib.IntMap.add i (new_inf::cut) m, a)
            | Some (i,to_j,j) -> (Lib.IntMap.add i cut' m, Lib.IntMap.add i (to_j,j) a)
          with
            Exit -> (m,a)
        in
        let get_best_inf i m =
          try
            Lib.IntMap.find i m
          with
            Not_found -> failwith ("Best inf not initialized for point "^(string_of_int i))
        in
        match todo with
          [] -> if next_layer = [] then (best_inf,aliases,dry_run)
	        else
		  progress ext_base dry_run visited best_inf aliases [] next_layer
        | (k,step_ki,i)::todo ->

           let inf_list = get_best_inf k best_inf in
           let dry_run',visited',best_inf',aliases',next_layer',todo' =
             List.fold_left (*folding inf_list*)
               (fun (dry_run,visited,best_inf,aliases,next_layer,todo) (root_to_inf,inf_to_k,inf,inf_to_w) ->
                let inf_to_i = step_ki @@ inf_to_k in
                let _ = if db() then Printf.printf "Visiting (%d -*-> %d |-> %d )\n" inf k i in
                List.fold_left (*folding compare inf_to_i inf_to_w*)
                  (fun (dry_run,visited,best_inf,aliases,next_layer,todo) -> function

                      (************************** Case Conflicting span ********************************)
                      (*1. best_inf,aliases = (root_to_inf,inf_to_i,inf,inf_to w) +!> best_inf (i) *)
                      (*2. add i...#...w to dry_run *)
                      (*3. if i is not visited yet, add i |-> k (for all succ(i)) to next_layer*)
                      (*4. add i to visited *)

                      Conflicting ->
                       if db() then print_string (red "Conflicting points\n");
                       let best_inf',aliases' =
                         update_best_inf
                           i
                           (root_to_inf,inf_to_i,inf,inf_to_w)
                           best_inf
                           aliases
                       in
                       let dry_run' =
                         (fun w ext_base _ -> add_conflict i w ext_base)::dry_run
                       in

                       let next_layer' =
                         if Lib.IntSet.mem i visited then
                         next_layer
                       else
                         Lib.IntMap.fold
                           (fun j step_ij cont ->
                            (i,step_ij,j)::cont
                           ) (find i ext_base).next next_layer
                       in
                       let visited' = Lib.IntSet.add i visited in
                       (dry_run',visited',best_inf',aliases',next_layer',todo)

                      (************************** Case inf_to_w factors inf_to_i ********************************)
                      (*1. best_inf,aliases = (root_to_inf,inf_to_i,inf,inf_to w) +!> best_inf (i) *)
                      (*2. add inf |-x-> i and w |-> i to dry_run NB: inf |-> w will eventually be added*)
                      (*3. add i to visited *)
                      (*NB no todo list to update here*)
                      | Below w_to_i -> (* w --w_to_i--> i *)
                        if db() then print_string (blue ("below "^(string_of_int i)^"\n"));
                        let best_inf',aliases' =
                          update_best_inf
                            i
                            (root_to_inf,inf_to_i,inf,inf_to_w)
                            best_inf
                            aliases
                        in
                        let dry_run' =
		          ((fun w ext_base _ ->
                            remove_step inf i (add_step w i w_to_i ext_base) (*no check and no aliasing necessary here*)
                           )::dry_run)
                        in
                        let visited' = Lib.IntSet.add i visited in
                        (dry_run',visited',best_inf',aliases',next_layer,todo)

                      (************************** Case inf_to_i factors inf_to_w *******************)
                      (*1. best_inf,_ = (root_to_i,id_i,i,i_to_w) +!> best_inf (i) *)
                      (*NB: no new alias here. no dry_run to add*)
                      (*2. add step i |-> k (for all succ k) to TODO to emulate Depth first*)
                      (*3. add i to visited *)

                     | Above i_to_w -> (* i --i_to_w--> w *)
                        if db() then print_string (yellow ("above "^(string_of_int i)^"\n"));
                        let pi = find i ext_base in
                        let best_inf',_ =
                          update_best_inf i
                                          (inf_to_i @@ root_to_inf,Cat.identity pi.value pi.value,i,i_to_w)
                                          best_inf
                                          aliases
                        in
                        let todo' =
                          if Lib.IntSet.mem i visited then
                            todo
                          else
                            Lib.IntMap.fold
                              (fun j step_ij cont -> (i,step_ij,j)::cont) pi.next todo
                        in
                        (dry_run,(Lib.IntSet.add i visited), best_inf',aliases,next_layer,todo')

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
                          let best_inf',aliases' =
                            update_best_inf i (root_to_inf,inf_to_i,inf,inf_to_w) best_inf aliases
                          in
		          let next_layer' =
                            if Lib.IntSet.mem i visited then
                              next_layer
                            else
                              Lib.IntMap.fold
                                (fun j step_ij cont ->
                                 (i,step_ij,j)::cont
                                ) (find i ext_base).next next_layer
                          in
                          let dry_run' =
                            if not sh_info.has_sup then
                              (fun w ext_base  _ -> add_conflict i w ext_base)::dry_run
                            else
                              dry_run
		          in
                          (dry_run',(Lib.IntSet.add i visited),best_inf',aliases',next_layer',todo)
                        else
                          (*Not a trivial midpoint*)
                          let next_layer' =
                            if Lib.IntSet.mem i visited then
                              next_layer
                            else
                              Lib.IntMap.fold
                                (fun j step_ij cont ->
                                 (i, step_ij, j)::cont
                                ) (find i ext_base).next next_layer
                          in
                          let fresh_id = get_fresh ext_base in
                          let best_inf',aliases' =
                            update_best_inf ~replace_if_found:false
                                            i
                                            (sh_info.to_midpoint @@ root_to_inf,sh_info.to_base,fresh_id,sh_info.to_w)
                                            best_inf
                                            aliases
                          in
                          let dry_run' =
                            (fun w ext_base aliases ->
                              let skip_midpoint = Lib.IntMap.mem fresh_id aliases in
                              let ext_base =
                                if skip_midpoint then ext_base
                                else
                                  let mp = point (Cat.trg sh_info.to_midpoint) in
                                  let ext_base =
                                    add fresh_id
                                      mp
                                      (sh_info.to_midpoint @@ (find_extension inf ext_base))
                                      ext_base
                                  in
                                  add_step fresh_id i sh_info.to_base ext_base
                              in
                              (*adding step from inf to midpoint or its alias (in this case verify that inf is not already below the alias*)
                              let ext_base =
                                add_step
                                  ~check:skip_midpoint
                                  ~aliases:aliases
                                  inf fresh_id sh_info.to_midpoint ext_base
                              in
		              let ext_base = if sh_info.has_sup then ext_base else add_conflict i w ext_base in
                              remove_step inf i ext_base (*will remove steps only if they exists and they are direct*)
                            )::dry_run
                          in
		          (dry_run',(Lib.IntSet.add i visited),best_inf',aliases',next_layer',todo)
                  ) (dry_run,visited,best_inf,aliases,next_layer,todo) (compare inf_to_i inf_to_w ext_base)
               ) (dry_run,visited,best_inf,aliases,next_layer,todo) inf_list
           in
           progress ext_base dry_run' visited' best_inf' aliases' next_layer' todo'

      let insert ext_w obs_emb obs_id ext_base =
        let p0 = find 0 ext_base in
        let id_0 = Cat.identity p0.value p0.value in
        try
          let best_inf_0 = Lib.IntMap.add 0 [(id_0,id_0,0,ext_w)] Lib.IntMap.empty in
          let todo_0 = [(0,id_0,0)] in
          let best_inf,aliases,dry_run = progress ext_base [] Lib.IntSet.empty best_inf_0 Lib.IntMap.empty [] todo_0 in

          
          (* 1. Adding witness point *)
          let w = get_fresh ext_base in
          let _ = if db() then print_string (blue (Printf.sprintf "Inserting witness with id %d\n" w)) ; flush stdout in
          let ext_base = add w (point (Cat.trg ext_w)) ext_w ext_base in
          let ext_base = add_obs w obs_emb obs_id ext_base in
          (* 2. Executing dry run, i.e inserting midpoints *)
          let ext_base = List.fold_left (fun ext_base act -> act w ext_base aliases) ext_base (List.rev dry_run) in

          (* 3. Connecting witness w to its best predecessors in the base*)
          let ext_base = Lib.IntSet.fold
                           (fun i ext_base ->
                            if i=w then ext_base
                            else
                              let inf_list = try Lib.IntMap.find i best_inf with
                                               Not_found ->
                                               failwith
                                                 ("Invariant violation: best_inf not defined for point "^(string_of_int i))
                              in
                              List.fold_left
                                (fun ext_base (_,_,inf,inf_to_w) ->
                                 let () =
                                   if db() then print_string
                                                  (blue (Printf.sprintf
                                                           "\t Adding best inf %d for %d and witness %d\n" inf i w)
                                                  ) ; flush stdout
                                 in
                                 (*no need to check aliasing since best_inf should only contain inf to be kept*)
                                 try add_step ~check:true inf w inf_to_w ext_base with
                                   Not_found -> (failwith (Printf.sprintf "Point %d (best inf for %d) is no longer in the base\n" inf i))
                                ) ext_base inf_list
                           ) ext_base.max_elements ext_base
          in
          ext_base
        with
          Found_iso (iso_w_i,i) -> add_obs i (iso_w_i @@ obs_emb) obs_id ext_base

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

end:ExtensionBasisType with type arrows = Cat.Make(Node).arrows and type obj = Cat.Make(Node).obj)
