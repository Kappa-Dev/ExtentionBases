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

    type t = {points : point Lib.IntMap.t ; fresh : int ; sharing : param ; leaves : Lib.IntSet.t}


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
           (str^str2)::dot_string
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
       leaves = Lib.IntSet.singleton 0}

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
        let p0 = find 0 ext_base in
        let p = find i ext_base in
        try {Cat.src = p0.value ; Cat.trg = p.value ; Cat.maps = [Lib.IntMap.find i p0.next]}
        with Not_found ->
          if i=0 then Cat.identity p0.value p0.value
          else
            failwith ("Trying unkown point "^(string_of_int i))

    let add_extension i j hom_ij ext_base =
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


    let add_witness emb_w emb_obs obs_id ext_base =
      if Cat.is_iso emb_w then
        let p0 = find 0 ext_base in
        let obs =
          match p0.obs with
            None -> Some (emb_obs,[obs_id])
          | Some (emb,obs_ids) -> Some (emb,obs_id::obs_ids)
        in
        (replace 0 {p0 with obs = obs} ext_base,0)
      else
        let pw = {value = emb_w.Cat.trg ;
                next = Lib.IntMap.empty ;
                prev = [0] ;
                obs = Some (emb_obs,[obs_id]) ;
                conflict = Lib.IntSet.empty ;
                witnesses = Lib.IntSet.empty
               }
        in
        let ext_base,k = add pw ext_base in
        let hom_0k = get_hom emb_w in
        let ext_base = add_extension 0 k hom_0k ext_base in
        if db() then Printf.printf "Add witness %d\n" k ;
        ({ext_base with leaves = Lib.IntSet.add k ext_base.leaves},k)

    let add_conflict i j ext_base =
      let pi = find i ext_base in
      let pj = find j ext_base in
      replace i {pi with conflict = Lib.IntSet.add j pi.conflict}
              (replace j {pj with conflict = Lib.IntSet.add i pj.conflict} ext_base)

    type sharing_info = {to_left : Cat.embeddings ; to_right : Cat.embeddings ; to_midpoint : Cat.embeddings ; has_sup : bool}
    type comparison = Iso of Cat.embeddings | Below of Cat.embeddings | Above of Cat.embeddings | Incomp of sharing_info

    let compare i ext obs_emb obs_id ext_base =
      assert (mem i ext_base) ;
      let ext_i = find_extension i ext_base in
      match Cat.share ext_base.sharing.unique (ext_i,ext) with
        [] -> failwith "Extension should at least share their sources"
      | sharings ->
         List.fold_left
           (fun comparisons (ext_mp,sharing_tile) ->
             let sh_left,sh_right = sharing_tile.Cat.span in
             let iso_left = Cat.is_iso sh_left in
             let iso_right = Cat.is_iso sh_right in
             if iso_left then
                    (*Both left and right embeddings of the span are actually isos*)
                    if iso_right then (*passing observable of pi to pj*)
           ) [] sharings

    (*Invariant j is the new witness in the base*)
    let compare i (*new*) j (*old*) ext_base dict =
      if db() then
        begin
          (*print_string (to_dot dict ext_base) ;*)
          Printf.printf "Comparing new %d with old %d \n" i j ;
        end ;
      if i=j then ext_base
      else
        let emb_to_i = find_extension i ext_base in
        let emb_to_j = find_extension j ext_base in
        if db() then
          Printf.printf "Sharing: \n %d: %s %s %s \n %d:%s %s %s \n"
                        i
                        (Graph.to_string emb_to_i.Cat.src)
                        (Cat.string_of_embeddings emb_to_i)
                        (Graph.to_string emb_to_i.Cat.trg)
                        j
                        (Graph.to_string emb_to_j.Cat.src)
                        (Cat.string_of_embeddings emb_to_j)
                        (Graph.to_string emb_to_j.Cat.trg) ;
        match Cat.share ext_base.sharing.unique (emb_to_i,emb_to_j) with
          [] -> ext_base
        | (emb_sharing,_)::_ as sharings ->
           let n_trg = Graph.size_edge emb_sharing.Cat.trg in
           let n_src = Graph.size_edge emb_sharing.Cat.src in
           (*if computed sharing is interesting enough --it has to be if comparing with the root of the EB*)
           if i=0 || n_trg - n_src >= ext_base.sharing.min then
             List.fold_left
               (fun ext_base (emb_s,tile_s) ->
                if not (mem i ext_base) then ext_base (*when i was found isomorphic to another point of the base*)
                else
                  let sh_left,sh_right = tile_s.Cat.span in
                  let iso_left = Cat.is_iso sh_left in
                  let iso_right = Cat.is_iso sh_right in
                  let pj = find j ext_base in
                  (*Special cases, when sharing reveals a sub-graph relationship*)
                  if iso_left then
                    (*Both left and right embeddings of the span are actually isos*)
                    if iso_right then (*passing observable of pi to pj*)
                      let pi = find i ext_base in
                      let new_obs_emb,new_obs_ids =
                        match pi.obs with
                          None -> failwith "not a witness"
                        | Some v -> v
                      in
                      (if db() then print_string (yellow "iso left and right\n")) ;
                      let obs_emb,obs_ids,add_obs =
                        match pj.obs with
                          None -> ((sh_left @@ (Cat.invert sh_right)) @@ new_obs_emb, new_obs_ids, true)
                        | Some (obs_emb,obs_ids') -> (obs_emb,obs_ids'@new_obs_ids, false) (*first obs_id in the list points to the reference graph*)
                      in
                      let ext_base = replace j {pj with obs = Some (obs_emb,obs_ids)} ext_base in
                      let ext_base = cut_leaf i ext_base in (*removing the new leaf*)
                      begin
                        if db() then
                          print_string (red "Removing "^(string_of_int i)^" from basis\n") ;
                      end;
                      if add_obs then
                        (*sons of j should know that j is a now the id of a witness*)
                        update_witnesses j ext_base
                      else
                        ext_base
                    else (*Iso left but not iso right*)
                      let hom_pj_pi = get_hom (sh_right @@ (Cat.invert sh_left)) in
                      (if db() then print_string (green "iso left\n") );
                      add_extension j i hom_pj_pi ext_base
                  else (*not iso left*)
                    if iso_right then (*but iso right*)
                      let hom_pi_pj = get_hom (sh_left @@ (Cat.invert sh_right)) in
                      (if db() then print_string (green "iso right\n") );
                      add_extension i j hom_pi_pj ext_base
                    else (*neither iso right nor left*)
                      let ext_base =
                        match tile_s.Cat.cospan with
                          None -> add_conflict i j ext_base
                        | Some _ -> ext_base
                      in
                      (if db() then print_string (green "Found a sharing point\n")) ;
                      let hom_mp_pj = get_hom sh_left in
                      let hom_mp_pi = get_hom sh_right in
                      let mp = {value = emb_s.Cat.src ;
                                next = Lib.IntMap.add i hom_mp_pi (Lib.IntMap.add j hom_mp_pj Lib.IntMap.empty) ;
                                prev = [0];
                                witnesses = Lib.IntSet.add i pj.witnesses ;
                                conflict = Lib.IntSet.empty ;
                                obs = None
                               }
                      in
                      let ext_base,k = add mp ext_base in
                      let hom_p0_mp = get_hom emb_s in
                      let ext_base = add_extension 0 k hom_p0_mp ext_base in
                      let ext_base = add_extension k j hom_mp_pj ext_base in
                      add_extension k i hom_mp_pi ext_base
               ) ext_base sharings
           else (*sharing is not worth adding to the extension base*)
             begin
               (if db() then print_string (red "not worth adding\n") );
               ext_base
             end


    let insert id_obs tile ext_base dict =
      let rec deep_insert i ext_base acc todo =
        if not (mem i ext_base) then ext_base (*i might have been removed if isomorphic to an already existing point*)
        else
          match todo with
            [] -> if acc = [] then ext_base else deep_insert i ext_base [] acc
          | j::tl ->
             if not (mem j ext_base) then deep_insert i ext_base acc tl
             else
               let acc =
                 if ext_base.sharing.deep then
                   let pj = find j ext_base in
                   List.fold_left
                     (fun acc k ->
                      let pk = find k ext_base in
                      if Lib.IntSet.mem i pk.witnesses then acc
                      else
                        begin
                          assert (mem k ext_base) ;
                          k::acc
                        end
                     ) acc pj.prev
                 else acc
               in
               let ext_base = compare i j ext_base dict in
               deep_insert i ext_base acc tl
      in

      let emb_obs,emb_w =
        match tile.Cat.cospan with
          Some cosp -> cosp
        | None -> failwith "Illegal witness tile"
      in
      (*Adding new points in the basis, without comparing with the others*)
      let ext_base,id_w = add_witness emb_w emb_obs id_obs ext_base in
      if id_w = 0 then ext_base
      else
        let _ =  if db() then Printf.printf "Computing sharing for witness %d ...\n" id_w in
        deep_insert id_w ext_base [] (to_list Lib.IntSet.fold ext_base.leaves)

  end
