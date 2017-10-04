module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    open Lib.Util

    type point = {value : Graph.t ;
                  next : Hom.t Lib.IntMap.t ;
                  prev : int list ;
                  obs : (Cat.embeddings * (int list)) option ;
                  conflict : Lib.IntSet.t ;
                  witnesses : Lib.IntSet.t}

    type param = {min : int ; deep : bool ; unique: bool}

    type t = {points : point Lib.IntMap.t ; fresh : int ; sharing : param ; leaves : Lib.IntSet.t ; extensions : Cat.embeddings Lib.IntMap.t}


    let to_dot dict ext_base =
      let l =
        Lib.IntMap.fold
          (fun i p dot_string ->
           let str = Printf.sprintf "%d [label=\"%d{sees: %s}[obs: %s]\"];" i
                                    i
                                    (String.concat "," (Lib.IntSet.fold (fun i cont -> string_of_int i::cont) p.witnesses []))
                                    (match p.obs with None -> "" | Some (_,ol) -> String.concat "," (List.map (fun x -> Lib.Dict.to_name x dict) ol))
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
                               (Printf.sprintf "%d -> %d [style = dotted];" i j)::dot_string
                              ) p.conflict [])
           in
           (str^str2^str3)::dot_string
          ) ext_base.points []
      in
      "digraph G{\n"^(String.concat "\n" l)^"\n}"

    let add p ext_base =
      ({ext_base with points = Lib.IntMap.add ext_base.fresh p ext_base.points ;
                      leaves = Lib.IntSet.add ext_base.fresh ext_base.leaves ;
                      fresh = ext_base.fresh+1
       },ext_base.fresh)

    let replace i p ext_base =
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let empty ?(deep=true) ?(unique=true) ?(min=1) h_eps =
      assert (min>0) ;
      {points = Lib.IntMap.add 0 {value = h_eps ;
                                  next = Lib.IntMap.empty ;
                                  prev = [] ;
                                  obs = None ;
                                  conflict = Lib.IntSet.empty ;
                                  witnesses = Lib.IntSet.empty
                                 } Lib.IntMap.empty ;
       fresh = 1 ;
       sharing = {min = min ; deep = deep ; unique = unique} ;
       leaves = Lib.IntSet.singleton 0;
       extensions = Lib.IntMap.add 0 (Cat.identity h_eps h_eps) Lib.IntMap.empty
      }

    let is_empty ext_base = ext_base.fresh = 1

    let find i ext_base = try Lib.IntMap.find i ext_base.points with Not_found -> failwith ("Point "^(string_of_int i)^" is not in the base")

    let cut_leaf i ext_base =
      let pi = find i ext_base in

      let ext_base = (*removing i from prev of successors of i*)
        Lib.IntMap.fold
          (fun j hom ext_base ->
           let pj = find j ext_base in
           replace j {pj with prev = List.filter (fun x -> x<>i) pj.prev} ext_base
          ) pi.next ext_base
      in
      let ext_base = (*removing i from next and witnesses of predecessors of i*)
        List.fold_left
          (fun ext_base j ->
           let pj = find j ext_base in
           replace j {pj with next = Lib.IntMap.remove i pj.next ;
                              witnesses = Lib.IntSet.remove i pj.witnesses
                     } ext_base
          ) ext_base pi.prev
      in
      {ext_base with points = Lib.IntMap.remove i ext_base.points}

    let to_emb i f j ext_base =
      try
        let iG = (find i ext_base).value in
        let jG = (find j ext_base).value in
        {Cat.src = iG ; Cat.trg = jG ; Cat.maps = [f]}
      with Not_found -> failwith "Unkown point identifier"

    let (@@) = Cat.vertical_compose
    let get_hom emb =
      match emb.Cat.maps with
        [h] -> h
      | _ -> failwith "Cannot extract map from embeddings"


    let update_witnesses i ext_base =
      let rec propagate prevs updated ext_base =
        match prevs with
          [] -> ext_base
        | j::tl ->
           if Lib.IntSet.mem j updated then propagate tl updated ext_base
           else
             let p = find j ext_base in
             propagate (p.prev@tl) (Lib.IntSet.add j updated) (replace j {p with witnesses = Lib.IntSet.add i p.witnesses} ext_base)
      in
      propagate (find i ext_base).prev Lib.IntSet.empty ext_base

    let find_extension i ext_base =
      if db() then print_string ("find_extension "^(string_of_int i)^"\n") ;

      if not (mem i ext_base) then
        failwith ("Unkown point "^(string_of_int i)^" in extension base")
      else
        Lib.IntMap.find i ext_base.extensions

    let add_step i j hom_ij ext_base =
      if db() then Printf.printf "add_extension %d->%d = %s\n" i j (Hom.to_string hom_ij) ;

      let pi = find i ext_base in
      let pj = find j ext_base in
      let new_wit = match pj.obs with
          None -> pj.witnesses
        | Some _ -> Lib.IntSet.add j pj.witnesses
      in
      replace j {pj with prev = i::pj.prev}
              (replace i {pi with next = Lib.IntMap.add j hom_ij pi.next ;
                                  witnesses = Lib.IntSet.union pi.witnesses new_wit
                         } {ext_base with leaves = Lib.IntSet.remove i ext_base.leaves})


    let add_extension ?(add_next=false) emb_w obs_opt conflict witnesses ext_base =
      let pw = {value = emb_w.Cat.trg ;
                next = Lib.IntMap.empty ;
                prev = [0] ;
                obs = obs_opt ;
                conflict = conflict ;
                witnesses = witnesses
               }
      in
      let ext_base,k = add pw ext_base in
      let hom_0k = get_hom emb_w in
      let ext_base = if add_next then add_step 0 k hom_0k ext_base else ext_base
      in
      if db() then Printf.printf "Add witness %d\n" k ;
      ({ext_base with leaves = Lib.IntSet.add k ext_base.leaves ; extensions = Lib.IntMap.add k emb_w ext_base.extensions},k)

    let add_conflict i j ext_base =
      let pi = find i ext_base in
      let pj = find j ext_base in
      replace i {pi with conflict = Lib.IntSet.add j pi.conflict}
              (replace j {pj with conflict = Lib.IntSet.add i pj.conflict} ext_base)

    type sharing_info = {to_w : Cat.embeddings ; to_base : Cat.embeddings ; to_midpoint : Cat.embeddings ; has_sup : bool}
    type comparison = Iso of Cat.embeddings | Below of Cat.embeddings | Above of Cat.embeddings | Incomp of sharing_info

    let compare i ext_wit obs_emb obs_id ext_base =
      assert (mem i ext_base) ;
      if db() then Printf.printf "\t Comparing %s with point %d\n" (Cat.string_of_embeddings ext_wit) i ;
      let ext_i = find_extension i ext_base in
      if db() then Printf.printf "\t Sharing %s\n"  (Cat.string_of_span (ext_wit,ext_i)) ;
      match Cat.share ext_base.sharing.unique (ext_i,ext_wit) with
        [] -> failwith "\t Extension should at least share their sources"
      | sharings ->
         List.fold_left
           (fun comparisons (ext_mp,sharing_tile) ->
             let sh_to_w,sh_to_base = sharing_tile.Cat.span in
             let iso_to_w = Cat.is_iso sh_to_w in
             let iso_to_base = Cat.is_iso sh_to_base in
             if iso_to_w then
               if iso_to_base then
                 begin
                   assert (Cat.is_co_span (sh_to_w,obs_emb)) ;
                   let cmp = Iso (sh_to_base @@ (Cat.invert sh_to_w) @@ obs_emb) (*Iso obs -> i *)
                   in
                   cmp::comparisons
                 end
               else
                 let cmp = Below (sh_to_w @@ (Cat.invert sh_to_base)) (*Below wit -> i*)
                 in
                 cmp::comparisons
             else
               if iso_to_base then
                 let cmp = Above (sh_to_base @@ (Cat.invert sh_to_w)) (*Above i -> wit *)
                 in
                 cmp::comparisons
               else
                 let is_compatible =
                   match sharing_tile.Cat.cospan with
                     None -> false
                   | Some _ -> true
                 in
                 (Incomp {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = ext_mp ; has_sup = is_compatible})::comparisons
           ) [] sharings

    let add_obs i ext obs_id ext_base =
      let pi = find i ext_base in
      let pi =
        match pi.obs with
          None -> {pi with obs = Some (ext,[obs_id])}
        | Some (_,obs_ids) -> {pi with obs = Some (ext,obs_id::obs_ids)}
      in
      replace i pi ext_base

    let simplify i j ext_base =
      let remove_prev k i ext_base =
        let pi = find i ext_base in
        replace i {pi with prev = List.filter (fun i ->  k <> 0) pi.prev} ext_base
      in
      let remove_next k i ext_base =
        let pi = find i ext_base in
        replace i {pi with next = Lib.IntMap.remove k pi.next} ext_base
      in
      let ext_base = remove_prev 0 i ext_base in
      let ext_base = remove_prev 0 j ext_base in
      remove_next i 0 (remove_next j 0 ext_base)


    let insert ext_wit obs_emb obs_id ext_base =
      let rec push ext_base = function
          [] -> if db() then Printf.printf "Push stack: {}\n" ; ext_base
        | i::tl as call_st ->
           if db() then Printf.printf "Push stack: {%s}\n" (String.concat "," (List.map string_of_int call_st)) ;
           let comparisons = compare i ext_wit obs_emb obs_id ext_base
           in
           assert (comparisons<>[]) ;
           let ext_base, cont =
             List.fold_left
               (fun (ext_base,cont) cmp ->
                match cmp with

                  (*i <---(> w) <--- obs: emb*)
                  Iso emb ->
                  if db() then print_string (red "iso\n");
                  (add_obs i emb obs_id ext_base,cont)

                (* emb: w(j) --> i*)
                | Below emb ->
                   if db() then print_string (blue ("below "^(string_of_int i)^"\n"));
                   let ext_base,j = add_extension ~add_next:true ext_wit (Some (obs_emb,[obs_id])) Lib.IntSet.empty Lib.IntSet.empty ext_base in
                   (add_step j i (get_hom emb) ext_base,cont)

                (* emb: i --> w(j) *)
                | Above emb ->
                   if db() then print_string (yellow ("above "^(string_of_int i)^"\n"));
                   if Lib.IntSet.mem i ext_base.leaves then
                     let ext_base,j = add_extension ~add_next:(i=0) ext_wit (Some (obs_emb,[obs_id])) Lib.IntSet.empty Lib.IntSet.empty ext_base in
                     if i=0 then (ext_base,cont)
                     else
                       (add_step i j (get_hom emb) ext_base,cont)
                   else
                     (if db() then Printf.printf "Point %d is not maximal, defering insertion\n" i ;
                      let pi = find i ext_base in
                      assert (not (Lib.IntMap.is_empty pi.next)) ;
                      (ext_base,Lib.IntMap.fold
                                  (fun j _ cont ->
                                   j::cont
                                  ) pi.next cont)
                     )

                (*i <-- mp --> w(j) *)
                | Incomp sh_info ->
                   if db() then print_string (green (Printf.sprintf "I found a midpoint %s!\n" (Graph.to_string sh_info.to_midpoint.Cat.trg)));
                   let conflict_w =
                     if sh_info.has_sup then Lib.IntSet.empty
                     else Lib.IntSet.singleton i
                   in
                   let ext_base,j = add_extension ext_wit (Some (obs_emb,[obs_id])) conflict_w Lib.IntSet.empty ext_base in
                   let pi = find i ext_base in
                   let conflict_i = if sh_info.has_sup then Lib.IntSet.add j pi.conflict else pi.conflict in
                   let ext_base = replace i {pi with conflict = conflict_i} ext_base in
                   let witnesses_mp = Lib.IntSet.add j pi.witnesses in
                   let ext_base,mp = add_extension ~add_next:true sh_info.to_midpoint None Lib.IntSet.empty witnesses_mp ext_base in
                   if db() then print_string (green ("new point "^(string_of_int mp)^"\n"));
                   let ext_base = add_step mp i (get_hom sh_info.to_base) ext_base in
                   let ext_base = simplify i j (add_step mp j (get_hom sh_info.to_w) ext_base) in
                   (ext_base,cont)
               ) (ext_base,[]) comparisons
           in

           push ext_base (cont@tl)
      in
      push ext_base [0]


  end
