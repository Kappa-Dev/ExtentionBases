module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)

    type point = {value : Graph.t ;
                  next : (Hom.t * int) list ;
                  prev : int list ;
                  obs : Cat.embeddings option ;
                  conflict : Lib.IntSet.t ;
                  witnesses : Lib.IntSet.t}

    type param = {min : int ; deep : bool ; unique: bool}

    type t = {points : point Lib.IntMap.t ; size : int ; sharing : param}

    let add_point p ext_base =
      ({ext_base with points = Lib.IntMap.add ext_base.size p ext_base.points ;
                     size = ext_base.size+1},ext_base.size-1)

    let replace_point i p ext_base =
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let init h_eps min deep unique =
      let p0 = {value = h_eps ;
                next = [] ;
                prev = [] ;
                obs = None ;
                conflict = Lib.IntSet.empty ;
                witnesses = Lib.IntSet.empty}
      in
      {points = Lib.IntMap.add 0 p0 Lib.IntMap.empty ; size = 1 ; sharing = {min = min ; deep = deep ; unique = unique}}

    let get_point i ext_base = Lib.IntMap.find i ext_base.points

    let to_emb i f j ext_base =
      try
        let iG = (get_point i ext_base).value in
        let jG = (get_point j ext_base).value in
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
         let p = get_point j ext_base in
         propagate (p.prev@tl) (Lib.IntSet.add j updated) (replace_point j {p with witnesses = Lib.IntSet.add i p.witnesses} ext_base)
      in
      propagate (get_point i ext_base).prev Lib.IntSet.empty ext_base

    let insert i span obs_emb ext_base =
      (*Costly assertion, to be removed*)
      assert (
          let p = get_point i ext_base in
          let emb = (fun (f,_) -> f) span in Graph.is_equal emb.Cat.trg p.value
        );
      match Cat.share ext_base.sharing.unique span with
        [] -> (ext_base,Lib.IntSet.empty)
      | (emb_sharing,_)::_ as sharings ->
         let n_trg = Graph.size_edge emb_sharing.Cat.trg in
         let n_src = Graph.size_edge emb_sharing.Cat.src in
         (*if computed sharing is interesting enough*)
         if n_trg - n_src >= ext_base.sharing.min then
           List.fold_left
             (fun (ext_base,midpoints) (emb_s,tile_s) ->
              let sh_left,sh_right = tile_s.Cat.span in
              let iso_left = Cat.is_iso sh_left in
              let iso_right = Cat.is_iso sh_right in

              (*Special cases, when sharing reveals a sub-graph relationship*)
              if iso_left then
                (*Both left and right embeddings of the span are actually isos*)
                if iso_right then
                  let obs_emb' = (sh_left @@ (Cat.invert sh_right)) @@ obs_emb
                  in
                  let p = {(get_point i ext_base) with obs = Some obs_emb'} in
                  let ext_base = replace_point i p ext_base in

                  (*sons of i should know that i is a now the id of a witness*)
                  let ext_base = update_witnesses i ext_base in
                  (ext_base,midpoints)
                else (*Iso left but not iso right*)
                  let w = {value = obs_emb.Cat.trg ; next = [] ;
                           prev = [i] ;
                           obs = Some obs_emb ;
                           conflict = Lib.IntSet.empty ;
                           witnesses = Lib.IntSet.empty}
                  in
                  let p = get_point i ext_base in
                  let hom_p_w = get_hom (sh_right @@ (Cat.invert sh_left)) in
                  let ext_base,j = add_point w ext_base in
                  (replace_point i {p with next = (hom_p_w,j)::p.next ; witnesses = Lib.IntSet.add j p.witnesses} ext_base, midpoints)
              else (*not iso left*)
                if iso_right then (*but iso right*)
                  let p = get_point i ext_base in
                  let hom_w_p = get_hom (sh_left @@ (Cat.invert sh_right)) in
                  let w = {value = obs_emb.Cat.trg ;
                           next = [(hom_w_p,i)] ;
                           prev = [0] ;
                           obs = Some obs_emb ;
                           conflict = Lib.IntSet.empty ;
                           witnesses = p.witnesses}
                  in
                  let ext_base,j = add_point w ext_base in
                  let hom_p0_w = get_hom ((fun (_,g) -> g) span) in
                  let p0 = get_point 0 ext_base in
                  (replace_point 0 {p0 with next = (hom_p0_w,j)::p0.next ; witnesses = Lib.IntSet.add j p0.witnesses} ext_base, midpoints)
                else (*neither iso right nor left*)
                  let conflict_w =
                    match tile_s.Cat.cospan with
                      None -> Lib.IntSet.singleton i
                    | Some _ -> Lib.IntSet.empty
                  in
                  let w = {value = obs_emb.Cat.trg ;
                           next = [] ;
                           prev = [] ;
                           obs = Some obs_emb ;
                           conflict = conflict_w ;
                           witnesses = Lib.IntSet.empty}
                  in
                  let ext_base,j = add_point w ext_base in
                  let p = get_point i ext_base in
                  let ext_base =
                    if Lib.IntSet.is_empty conflict_w then ext_base
                    else
                      replace_point i {p with conflict = Lib.IntSet.add j p.conflict} ext_base
                  in
                  let hom_mp_p = get_hom sh_left in
                  let hom_mp_w = get_hom sh_right in
                  let mp = {value = emb_s.Cat.src ;
                            next = [(hom_mp_p,i);(hom_mp_w,j)] ;
                            prev = [0];
                            witnesses = Lib.IntSet.add j p.witnesses ;
                            conflict = Lib.IntSet.empty ;
                            obs = None
                           }
                  in
                  let ext_base,k = add_point mp ext_base in
                  let ext_base = replace_point j {w with prev = [k]} (replace_point i {p with prev = k::p.prev} ext_base)
                  in
                  let hom_p0_mp = get_hom emb_s in
                  let p0 = get_point 0 ext_base in
                  let ext_base = replace_point 0 {p0 with next = (hom_p0_mp,k)::p0.next; witnesses = Lib.IntSet.add j p0.witnesses } ext_base in
                  (ext_base, Lib.IntSet.add k midpoints)
             ) (ext_base,Lib.IntSet.empty) sharings
         else (*sharing is not worth adding to the extension base*)
           (ext_base,Lib.IntSet.empty)

    let to_dot ext_base =
      let l =
        Lib.IntMap.fold
          (fun i p dot_string ->
           let str = Printf.sprintf "%d [label=\"{%s}\"];" i (String.concat "," (Lib.IntSet.fold (fun i cont -> string_of_int i::cont) p.witnesses [])) in
           let str2 =
             String.concat "\n"
                           (List.fold_left
                              (fun dot_string (_,j) ->
                               (Printf.sprintf "%d -> %d ;" i j)::dot_string
                              ) [] p.next)
           in
           (str^str2)::dot_string
          ) ext_base.points []
      in
      "digraph G{\n"^(String.concat "\n" l)^"\n}"
  end
