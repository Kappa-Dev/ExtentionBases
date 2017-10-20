module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    open Lib.Util

    type point = {value : Graph.t ;
                  next : Cat.embeddings Lib.IntMap.t ;
                  obs : (Cat.embeddings * int) list ;
                  conflict : Lib.IntSet.t
                 }

    type param = {min : int ; deep : bool ; unique: bool}

    type t = {points : point Lib.IntMap.t ; (*corresp int -> point *)
              fresh : int ; (*next fresh point id*)
              sharing : param ; (*various tuning params*)
              witnesses : Lib.IntSet.t ; (*set of points that are witnesses (not midpoints) *)
              extensions : Cat.embeddings Lib.IntMap.t (* i |-->  (0 -->i) --extension from root to i*)
             }


    let to_dot dict ext_base =
      let l =
        Lib.IntMap.fold
          (fun i p dot_string ->
           let str = Printf.sprintf "%d [label=\"%d [obs: %s]\" , shape = \"%s\"];" i
                                    i
                                    (match p.obs with
                                       [] -> ""
                                     | ol -> String.concat ","
                                                           (List.map (fun (emb,x) ->
                                                                      (Cat.string_of_embeddings ~nocolor:true emb)
                                                                      ^","^(Lib.Dict.to_name x dict)
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

    let add p ext_p ext_base =
      ({points = Lib.IntMap.add ext_base.fresh p ext_base.points ;
        witnesses =
          begin
            match p.obs with
              [] -> ext_base.witnesses
            | _ -> Lib.IntSet.add ext_base.fresh ext_base.witnesses
          end ;
        fresh = ext_base.fresh+1 ;
        extensions = Lib.IntMap.add ext_base.fresh ext_p ext_base.extensions ;
        sharing = ext_base.sharing ;
       },ext_base.fresh)

    let replace i p ext_base =
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let empty ?(deep=true) ?(unique=true) ?(min=1) h_eps =
      assert (min>0) ;
      {points = Lib.IntMap.add 0 {value = h_eps ;
                                  next = Lib.IntMap.empty ;
                                  obs = [] ;
                                  conflict = Lib.IntSet.empty ;
                                 } Lib.IntMap.empty ;
       fresh = 1 ;
       sharing = {min = min ; deep = deep ; unique = unique} ;
       witnesses = Lib.IntSet.empty;
       extensions = Lib.IntMap.add 0 (Cat.identity h_eps h_eps) Lib.IntMap.empty
      }

    let is_empty ext_base = ext_base.fresh = 1

    let find i ext_base = Lib.IntMap.find i ext_base.points

    let (@@) = Cat.vertical_compose

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

    exception Found of Cat.embeddings list

    let search i j ext_base =
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
      if db() then Printf.printf "Add Step %d |-> %d = %s-%s->%s\n" i j
                                 (Graph.to_string emb_ij.Cat.src)
                                 (Cat.string_of_embeddings emb_ij)
                                 (Graph.to_string emb_ij.Cat.trg) ;

      let pi = find i ext_base in
      replace i {pi with next = Lib.IntMap.add j emb_ij pi.next} ext_base

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


    type sharing_info = {to_w : Cat.embeddings ; to_base : Cat.embeddings ; to_midpoint : Cat.embeddings ; has_sup : bool}
    type comparison = Iso of Cat.embeddings | Below of Cat.embeddings | Above of Cat.embeddings | Incomp of sharing_info | Conflicting

    let compare inf_to_i inf_to_w ext_base =
      if db() then
        begin
          try Printf.printf "\t Sharing %s\n"  (Cat.string_of_span (inf_to_i,inf_to_w))
          with _ ->
            Printf.printf "\t Sharing (Not a span!!!) %s<-%s-%s, %s-%s->%s\n"
                          (Graph.to_string inf_to_i.Cat.trg)
                          (Cat.string_of_embeddings inf_to_i)
                          (Graph.to_string inf_to_i.Cat.src)
                          (Graph.to_string inf_to_w.Cat.src)
                          (Cat.string_of_embeddings inf_to_w)
                          (Graph.to_string inf_to_w.Cat.trg)
        end;
      match Cat.share ext_base.sharing.unique (inf_to_i,inf_to_w) with
        None -> Conflicting
      | Some (inf_to_sh,sharing_tile) ->
         let sh_to_base,sh_to_w = sharing_tile.Cat.span in
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
             match sharing_tile.Cat.cospan with
               None -> Incomp {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = inf_to_sh ; has_sup = false}
             | Some _ -> Incomp {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = inf_to_sh ; has_sup = true}


    exception Found_iso of (Cat.embeddings * int)

    let remove_step i j ext_base =
      let pi = find i ext_base in
      replace i {pi with next = Lib.IntMap.remove j pi.next} ext_base

    let rec progress inf ext_w ext_base =
      Lib.IntMap.fold
        (fun i ext_inf_i actions ->
         match compare ext_inf_i ext_w ext_base with
           Conflicting -> (fun w ext_base -> add_conflict i w ext_base)::actions
         | Below ext_w_i -> (fun w ext_base -> add_step w i ext_w_i ext_base)::actions
         | Above ext_i_w -> (progress i ext_i_w ext_base)@actions (*may still find a point that is isomorphic to witness*)
         | Iso iso_w_i -> raise (Found_iso (iso_w_i,i))
         | Incomp sh_info ->
            let actions =
              if sh_info.has_sup then
                actions
              else
                (fun w ext_base -> add_conflict i w ext_base)::actions
            in
            if Cat.is_iso sh_info.to_midpoint then
              actions
            else
              (*Not a trivial midpoint*)
              (fun w ext_base ->
               let mp = {value = sh_info.to_midpoint.Cat.trg ;
                         next = Lib.IntMap.empty ;
                         obs = [] ;
                         conflict = Lib.IntSet.empty ;
                        }
               in
               let ext_base,inf' = add mp (sh_info.to_midpoint @@ (find_extension inf ext_base)) ext_base in
               let ext_base = add_step inf inf' sh_info.to_midpoint ext_base in
               let ext_base = add_step inf' i sh_info.to_base ext_base in
               remove_step inf i ext_base
              )::actions
        ) (find inf ext_base).next []


    (*Bug should test whether to_mipoint is not an iso*)
 (*   let insert ext_wit obs_emb obs_id ext_base =
      let rec push inf inf_to_w ext_base w_opt = function
          [] -> if db() then Printf.printf "Push stack: {}\n" ; ext_base
          | (j,emb_i,i)::tl as call_st ->
             assert (mem i ext_base) ;
             let _ =  if db() then Printf.printf "Push stack: {%s}\n"
                                                 (String.concat ","
                                                                (List.map (fun (i,_,j) ->
                                                                     (string_of_int i)^"|->"^(string_of_int j)
                                                                   ) call_st))
             in
             let comparisons =
               if inf <> j then
                 let _ = if db() then print_string "Inf is above comparison point, computing difference...\n" in
                 let emb_j_inf =
                   match search j inf ext_base with
                     None -> failwith "Could not compute steps composition"
                   | Some emb -> emb
                 in
                 compare j emb_i i (inf_to_w @@ emb_j_inf) ext_base
               else
                 compare j emb_i i inf_to_w ext_base
             in
             let ext_base,cont,inf,inf_to_w, w_opt =
               List.fold_left
                 (fun (ext_base,cont,inf,inf_to_w,w_opt) cmp ->
                  if db() then Printf.printf "Continuation {%s}\n"
                                             (String.concat ","
                                                            (List.map
                                                               (fun (i,_,j) -> (string_of_int i)^"|->"^(string_of_int j)
                                                               ) cont)
                                             ) ;
                  match cmp with
                    (*i ...#... w *)
                    Conflicting ->
                    if db() then print_string (red "Conflicting points\n");
                    let ext_base,w =
                      add_extension w_opt
                                    ext_wit
                                    [obs_emb,obs_id]
                                    ext_base
                    in
                    let ext_base = add_conflict i w ext_base in
                    (add_step inf w inf_to_w ext_base, cont, inf, inf_to_w, Some w)
                  (*i <---(> w): emb*)
                  |  Iso emb ->
                      if db() then print_string (red "iso\n");
                      (add_obs i (emb@@obs_emb) obs_id ext_base,[],inf,inf_to_w,w_opt)

                  (* emb: w --> mp*)
                  | Below sh_info ->
                     if db() then print_string (blue ("below "^(string_of_int i)^"\n"));
                     let ext_base,w =
                       add_extension w_opt
                                     ext_wit
                                     [obs_emb,obs_id]
                                     ext_base
                     in
                     let inf_to_w = sh_info.to_w @@ sh_info.to_midpoint in
                     let ext_base = add_step inf w inf_to_w ext_base in
                     let ext_base = remove_step inf i ext_base in
                     (add_step w i (sh_info.to_base @@ (Cat.invert sh_info.to_w)) ext_base,cont,inf,inf_to_w, Some w)

                  (* emb: i --> w *)
                  | Above sh_info ->
                     if db() then print_string (yellow ("above "^(string_of_int i)^"\n"));
                     let emb_i_w = sh_info.to_w@@(Cat.invert sh_info.to_base) in
                     let pi = find i ext_base in
                     if Lib.IntMap.is_empty pi.next then
                       let ext_base,w =
                         add_extension w_opt
                                       ext_wit
                                       [obs_emb,obs_id]
                                       ext_base
                       in
                       (add_step i w emb_i_w ext_base, cont, i, emb_i_w, Some w)
                     else
                       let _ = if db() then print_string "Defering insertion\n" in
                       (ext_base,Lib.IntMap.fold
                                   (fun j emb cont ->
                                    (i,emb,j)::cont
                                   ) pi.next cont,i,emb_i_w, w_opt)

                  (*i <-- mp --> w *)
                  | Incomp sh_info ->
                     if db() then print_string (green (Printf.sprintf "I found a midpoint %s!\n" (Graph.to_string sh_info.to_midpoint.Cat.trg)));

                     let ext_base,w =
                       add_extension w_opt
                                     ext_wit
                                     [obs_emb,obs_id]
                                     ext_base
                     in
                     let ext_base = if not sh_info.has_sup then add_conflict i w ext_base else ext_base in

                     if Cat.is_iso sh_info.to_midpoint then
                       let _ = if db() then print_string "Sharing is not worth adding\n"
                       in
                       (*BUG Here should check that iso i <--> w is not from above when sh_info.has_sup*)
                       (add_step inf w inf_to_w ext_base,tl,inf,inf_to_w,Some w)
                     else
                       let ext_base,mp =
                         add_extension None
                                       (sh_info.to_midpoint@@(find_extension inf ext_base))
                                       [] (*no observable*)
                                       ext_base
                       in
                       if db() then print_string (green ("new point "^(string_of_int mp)^"\n"));
                       let ext_base = remove_step inf i ext_base in
                       let ext_base = remove_step inf w ext_base in
                       let ext_base = add_step inf mp sh_info.to_midpoint ext_base in
                       let ext_base = add_step mp i sh_info.to_base ext_base in
                       let ext_base = add_step mp w sh_info.to_w ext_base in
                       (ext_base,cont,mp,sh_info.to_w, Some w)
                 ) (ext_base,tl,inf,inf_to_w, w_opt) comparisons
             in
             push inf inf_to_w ext_base w_opt cont
      in
      let p0 = find 0 ext_base in
      let id_0 = Cat.identity p0.value p0.value in
      push 0 ext_wit ext_base None [(0,id_0,0)]
  *)

  end
