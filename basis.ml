module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    open Lib.Util

    type point = {value : Graph.t ;
                  next : Cat.arrows Lib.IntMap.t ;
                  obs : (Cat.arrows * int) list ;
                  conflict : Lib.IntSet.t ;
                  future : Lib.IntSet.t ;
                 }

    type param = {min : int ; deep : bool ; unique: bool}

    type t = {points : point Lib.IntMap.t ; (*corresp int -> point *)
              sharing : param ; (*various tuning params*)
              witnesses : Lib.IntSet.t ; (*set of points that are witnesses (not midpoints) *)
              extensions : Cat.arrows Lib.IntMap.t (* i |-->  (0 -->i) --extension from root to i*)
             }


    let point g =
      {value = g ;
       next = Lib.IntMap.empty ;
       obs = [] ;
       conflict = Lib.IntSet.empty ;
       future = Lib.IntSet.empty
      }


    let to_dot dict ext_base =
      let l =
        Lib.IntMap.fold
          (fun i p dot_string ->
           let str = Printf.sprintf "%d [label=\"%d [obs: %s] {sees:%s}\" , shape = \"%s\"];" i
                                    i
                                    (match p.obs with
                                       [] -> ""
                                     | ol -> String.concat ","
                                                           (List.map (fun (emb,x) ->
                                                                      (Cat.string_of_arrows ~nocolor:true emb)
                                                                      ^","^(Lib.Dict.to_name x dict)
                                                                     ) ol))
                                    (String.concat "," (List.map string_of_int (to_list Lib.IntSet.fold p.future)))
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
             String.concat "\n"
                           (Lib.IntSet.fold
                              (fun j dot_string ->
                               if i < j then
                                 (Printf.sprintf "%d -> %d [style = \"dotted\", dir = \"none\", constraint = false];" i j)::dot_string
                               else
                                 dot_string
                              ) p.conflict [])
           in
           (str^"\n"^str2^"\n"^str3)::dot_string
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
       sharing = ext_base.sharing ;
      }

    let replace i p ext_base =
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let empty ?(deep=true) ?(unique=true) ?(min=1) h_eps =
      assert (min>0) ;
      {points = Lib.IntMap.add 0 (point h_eps) Lib.IntMap.empty ;
       sharing = {min = min ; deep = deep ; unique = unique} ;
       witnesses = Lib.IntSet.empty;
       extensions = Lib.IntMap.add 0 (Cat.identity h_eps h_eps) Lib.IntMap.empty
      }

    let is_empty ext_base = (Lib.IntMap.cardinal ext_base.points = 1)

    let find i ext_base = Lib.IntMap.find i ext_base.points

    let (@@) = Cat.(@@)

    let leaf i ext_base =
      Lib.IntMap.is_empty (find i ext_base).next

    let find_extension i ext_base =
      if db() then
        begin
          print_string ("find_extension "^(string_of_int i)^": ") ;
        end ;

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
          if leaf i ext_base then ([],visited)
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


    let add_step i j emb_ij ext_base =
      let pi = find i ext_base in
      if Lib.IntSet.mem j pi.future then
        let _ = if db() then print_string (red (Printf.sprintf "Not adding step: %d is in the future of %d\n" j i))
        in
        ext_base
      else
        let pj = find j ext_base in
        if db() then Printf.printf "Add Step %d |-> %d = %s-%s->%s\n" i j
                                   (Graph.to_string (Cat.src emb_ij))
                                   (Cat.string_of_arrows emb_ij)
                                   (Graph.to_string (Cat.trg emb_ij)) ;
        replace i {pi with next = Lib.IntMap.add j emb_ij pi.next;
                           future = Lib.IntSet.add j (Lib.IntSet.union pi.future pj.future)
                  } ext_base

    let add_conflict i j ext_base =
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


    type sharing_info = {to_w : Cat.arrows ; to_base : Cat.arrows ; to_midpoint : Cat.arrows ; has_sup : bool}
    type comparison = Iso of Cat.arrows | Below of Cat.arrows | Above of Cat.arrows | Incomp of sharing_info | Conflicting

    let compare inf_to_i inf_to_w ext_base =
      if db() then
        Printf.printf "\t Sharing %s\n"  (Cat.string_of_span (inf_to_i,inf_to_w)) ;
      match Cat.share inf_to_i inf_to_w with
        None -> Conflicting
      | Some (inf_to_sh,sharing_tile) ->
         let sh_to_base,sh_to_w = Cat.lower_bound sharing_tile in
         let _ = if db() then Printf.printf "Sharing is %s\n" (Cat.string_of_span (sh_to_base,sh_to_w)) in
         let iso_to_w = Cat.is_iso sh_to_w in
         let iso_to_base = Cat.is_iso sh_to_base in
         if iso_to_w then
           if iso_to_base then
             Iso (sh_to_base @@ (Cat.invert sh_to_w) ) (*Iso: w (<)--> i *)
           else
             Below (sh_to_base @@ (Cat.invert sh_to_w) ) (*Below wit -> i*)
         else
           if iso_to_base then
             Above (sh_to_w @@ (Cat.invert sh_to_base) ) (*Above i -> wit *)
           else
             match Cat.upper_bound sharing_tile with
               None -> Incomp {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = inf_to_sh ; has_sup = false}
             | Some _ -> Incomp {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = inf_to_sh ; has_sup = true}


    exception Found_iso of (Cat.arrows * int)

    let remove_step i j ext_base =
      let pi = find i ext_base in
      let _ = if db() then
                if Lib.IntMap.mem j pi.next then print_string (red (Printf.sprintf "Removing step %d |-x-> %d\n" i j))
      in
      replace i {pi with next = Lib.IntMap.remove j pi.next} ext_base

    let rec progress fresh_id ext_base actions visited best_inf next_layer todo =
      (************* DEBUGING INFO ***************)
      let _ = if db() then
                begin
                  Printf.printf "stack: {%s}\n"
                                (String.concat
                                   ","
                                   (List.map (fun (inf,_,i,_) -> "("^(string_of_int inf)^","^(string_of_int i)^")") todo)) ;
                  Printf.printf "next calls: {%s}\n"
                                (String.concat
                                   ","
                                   (List.map (fun (inf,_,i,_) -> "("^(string_of_int inf)^","^(string_of_int i)^")") next_layer)) ;
                  Printf.printf "0 |--> {%s}\n"
				(String.concat ","
					       (List.map string_of_int
							 (Lib.IntMap.fold (fun i _ cont -> i::cont) (find 0 ext_base).next []))
				)
                end
      in
      (************* DEBUGING INFO ***************)
      let update_best_inf i j m =
        try
          let p = Lib.IntMap.find i m in
          if p = j then m
          else
            if (mem p ext_base) || (mem j ext_base) then (* j ~ p detected*)
              failwith (Printf.sprintf "Malformed extension based, points %d and %d should be incomparable" p j)
            else
              let () = if db() then Printf.printf "Found two isomorphic midpoints %d and %d\n" j p
              in
              Lib.IntMap.add i j m
        with
          Not_found -> Lib.IntMap.add i j m
      in

      match todo with
        [] -> if next_layer = [] then (best_inf,actions)
	      else
		progress fresh_id ext_base actions visited best_inf [] next_layer
      | (inf,ext_inf_i,i,ext_inf_w)::todo ->

	 (*When there are cycles in the extension base, a point may already have been compared with w*)
         if Lib.IntSet.mem i visited then
           progress fresh_id ext_base actions visited best_inf next_layer todo
         else

           let _ = if db() then Printf.printf "Visiting (%d,%d)\n" inf i in
           begin
             assert (mem i ext_base) ;
             match compare ext_inf_i ext_inf_w ext_base with

               Conflicting ->
               if db() then print_string (red "Conflicting points\n");
               let next_layer',stop =
                 Lib.IntMap.fold
                   (fun j ext_ij (cont,b) ->
                    print_int i ; print_string "|-->" ; print_int j ; print_newline ();
                    ((inf,ext_ij @@ ext_inf_i,j,ext_inf_w)::cont,false)
                   ) (find i ext_base).next (next_layer,true)
               in
               let actions' =
                 if stop then
                   (fun w ext_base best_inf -> add_step inf w ext_inf_w (add_conflict i w ext_base))::actions
                 else
                   (fun w ext_base best_inf -> add_conflict i w ext_base)::actions
               in
               let best_inf' = update_best_inf i (Lib.IntMap.find inf best_inf) best_inf in
               progress fresh_id ext_base actions' (Lib.IntSet.add i visited) best_inf' next_layer' todo

               | Below ext_w_i -> (* w --ext_w_i--> i *)
                  if db() then print_string (blue ("below "^(string_of_int i)^"\n"));
                  progress
		    fresh_id
		    ext_base
		    ((fun w ext_base best_inf -> remove_step inf i (add_step w i ext_w_i ext_base))::actions)
		    (Lib.IntSet.add i visited)
                    best_inf
		    next_layer
		    todo

               | Above ext_i_w -> (* i --ext_i_w--> w *)
                  if db() then print_string (yellow ("above "^(string_of_int i)^"\n"));
                  let todo',stop =
                    Lib.IntMap.fold
                      (fun j ext_ij (cont,b) ->
                       ((i,ext_ij,j,ext_i_w)::cont,false)
                      ) (find i ext_base).next (todo,true)
                  in
                  let actions' =
                    if stop then
                      (fun w ext_base best_inf -> add_step i w ext_i_w (remove_step inf w ext_base))::actions
                    else
                      actions
                  in
                  let best_inf' = update_best_inf i i best_inf in
                  progress fresh_id
                           ext_base
                           actions'
                           (Lib.IntSet.add i visited)
                           best_inf'
                           next_layer
                           todo'

               | Iso iso_w_i ->
                  if db() then print_string (red "iso\n");
                  raise (Found_iso (iso_w_i,i))

               | Incomp sh_info ->
                  if db() then print_string
				 (green (Printf.sprintf "I found a midpoint %s (%d)!\n"
							(Graph.to_string (Cat.trg sh_info.to_midpoint))
							fresh_id)
				 );
		  (*No better comparison with w exists*)
                  if Cat.is_iso sh_info.to_midpoint then
                    let next_layer',stop =
                      if db() then print_string (green (Printf.sprintf "...that is not worth adding\n")) ;
                      Lib.IntMap.fold
                        (fun j ext_ij (cont,b) ->
                         ((inf,ext_ij @@ ext_inf_i,j,ext_inf_w)::cont,false)
                        ) (find i ext_base).next (next_layer,true)
                    in
                    let actions' =
                      if stop then
                        (fun w ext_base best_inf ->
			 if sh_info.has_sup then add_step inf w ext_inf_w ext_base
			 else
			    add_conflict i w (add_step inf w ext_inf_w ext_base)
			)::actions
                      else
                        if sh_info.has_sup then actions
			else
			  (fun w ext_base best_inf -> add_conflict i w ext_base)::actions
                    in
                    let best_inf' = update_best_inf i (Lib.IntMap.find inf best_inf) best_inf in
                    progress
		      fresh_id
		      ext_base actions'
		      (Lib.IntSet.add i visited)
                      best_inf'
		      next_layer'
		      todo
                  else
                    (*Not a trivial midpoint*)
                    let next_layer',stop =
                      Lib.IntMap.fold
                        (fun j ext_ij (cont,b) ->
                         ((fresh_id,ext_ij @@ sh_info.to_base,j,sh_info.to_w)::cont,false)
                        ) (find i ext_base).next (next_layer,true)
                    in
                    let actions' =
                      (fun w ext_base best_inf ->
                       let id = try Lib.IntMap.find i best_inf with Not_found -> failwith "Invariant violation"
                       in

                       (*if best predecessor has been already added to the ext_base*)
                       if mem id ext_base then
                         match Cat.share (find_extension id ext_base) (sh_info.to_midpoint @@ (find_extension inf ext_base)) with
                           None -> failwith "Both best predecessors should be isomorphic"
                         | Some (_,tile) ->
                            let left,right = Cat.lower_bound tile in
                            let ext_base = add_step inf id ((left @@ (Cat.invert right)) @@ sh_info.to_midpoint) ext_base in
                            remove_step inf i (remove_step inf w ext_base)

                       else
                         (*this new midpoint is the current best predecessor*)
                         let _ = if db() then Printf.printf "new midpoint %d is the best predecessor of witness %d\n" id w in
                         let mp = point (Cat.trg sh_info.to_midpoint) in
                         let ext_base = add id mp (sh_info.to_midpoint @@ (find_extension inf ext_base)) ext_base in
                         let ext_base =
                           if stop then (add_step id w sh_info.to_w ext_base)
                           else ext_base
                         in
                         let ext_base = add_step inf id sh_info.to_midpoint ext_base in
                         let ext_base = add_step id i sh_info.to_base ext_base in
		         let ext_base = if sh_info.has_sup then ext_base else add_conflict i w ext_base in
                         remove_step inf i (remove_step inf w ext_base) (*will remove steps only if they exists and they are direct*)
                      )::actions
                    in
                    let best_inf' = update_best_inf i fresh_id best_inf in
                    progress
		      (fresh_id+1)
		      ext_base
		      actions'
		      (Lib.IntSet.add i visited)
                      best_inf'
		      next_layer'
		      todo
           end

    let insert ext_w obs_emb obs_id ext_base =
      let p0 = find 0 ext_base in
      let id_0 = Cat.identity p0.value p0.value in
      try
        let w = Lib.IntMap.cardinal ext_base.points in
	let next_midpoint = w+1 in
        let best_inf,actions = progress next_midpoint ext_base [] Lib.IntSet.empty Lib.IntMap.empty [] [(0,id_0,0,ext_w)] in
        let _ = if db() then print_string (blue (Printf.sprintf "Adding witness with id %d\n" w)) in
        let ext_base = add w (point (Cat.trg ext_w)) ext_w ext_base in
        let ext_base = add_obs w obs_emb obs_id ext_base in
        List.fold_left (fun ext_base act -> act w ext_base best_inf) ext_base (List.rev actions)
      with
        Found_iso (iso_w_i,i) -> add_obs i (iso_w_i @@ obs_emb) obs_id ext_base


  end
