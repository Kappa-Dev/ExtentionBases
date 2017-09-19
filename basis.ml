module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    open Lib.Util

    type point = {value : Graph.t ;
                  next : Hom.t Lib.IntMap.t ;
                  prev : int list ;
                  obs : (Cat.embeddings*int) option ;
                  conflict : Lib.IntSet.t ;
                  witnesses : Lib.IntSet.t}

    type param = {min : int ; deep : bool ; unique: bool}

    type t = {points : point Lib.IntMap.t ; size : int ; sharing : param ; leafs : Lib.IntSet.t}

    let add p ext_base =
      ({ext_base with points = Lib.IntMap.add ext_base.size p ext_base.points ;
                      leafs = Lib.IntSet.add ext_base.size ext_base.leafs ;
                      size = ext_base.size+1
       },ext_base.size-1)


    let replace i p ext_base =
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let empty ?(min = 1) ?(deep=false) ?(unique=true) =
      assert (min>0) ;
      {points = Lib.IntMap.empty ;
       size = 0 ;
       sharing = {min = min ; deep = deep ; unique = unique} ;
       leafs = Lib.IntSet.empty}

    let is_empty ext_base = ext_base.size = 0

    let find i ext_base = Lib.IntMap.find i ext_base.points

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

    let share_insert i wit_emb id_obs obs_emb ext_base =
      if not (mem i ext_base) then
        failwith ("Unkown point "^(string_of_int i)^" in extension base")
      else
      let p0 = find 0 ext_base in
      let p = find i ext_base in
      let emb_to_i =
        try {Cat.src = p0.value ; Cat.trg = p.value ; Cat.maps = [Lib.IntMap.find i p0.next]}
        with Not_found ->
          if i=0 then Cat.identity p0.value p0.value
          else failwith "Trying to compare a witness with an unkown point"
      in
      let span = (emb_to_i,wit_emb) in
      match Cat.share ext_base.sharing.unique span with
        [] -> ext_base
      | (emb_sharing,_)::_ as sharings ->
         let n_trg = Graph.size_edge emb_sharing.Cat.trg in
         let n_src = Graph.size_edge emb_sharing.Cat.src in
         (*if computed sharing is interesting enough --it has to be if comparing with the root of the EB*)
         if i=0 || n_trg - n_src >= ext_base.sharing.min then
           List.fold_left
             (fun ext_base (emb_s,tile_s) ->
              let sh_left,sh_right = tile_s.Cat.span in
              let iso_left = Cat.is_iso sh_left in
              let iso_right = Cat.is_iso sh_right in

              (*Special cases, when sharing reveals a sub-graph relationship*)
              if iso_left then
                (*Both left and right embeddings of the span are actually isos*)
                if iso_right then
                  let obs_emb' = (sh_left @@ (Cat.invert sh_right)) @@ obs_emb
                  in
                  let ext_base = replace i {p with obs = Some (obs_emb',id_obs)} ext_base in

                  (*sons of i should know that i is a now the id of a witness*)
                  let ext_base = update_witnesses i ext_base in
                  ext_base
                else (*Iso left but not iso right*)
                  let w = {value = obs_emb.Cat.trg ; next = Lib.IntMap.empty ;
                           prev = [i] ;
                           obs = Some (obs_emb,id_obs) ;
                           conflict = Lib.IntSet.empty ;
                           witnesses = Lib.IntSet.empty}
                  in
                  let p = find i ext_base in
                  let hom_p_w = get_hom (sh_right @@ (Cat.invert sh_left)) in
                  let ext_base,j = add w ext_base in
                  let ext_base = replace 0 {p0 with next = Lib.IntMap.add j (get_hom wit_emb) p0.next} ext_base in
                  let ext_base = {ext_base with leafs = Lib.IntSet.add j (Lib.IntSet.remove i ext_base.leafs)}
                  in
                  replace i {p with next = Lib.IntMap.add j hom_p_w p.next ; witnesses = Lib.IntSet.add j p.witnesses} ext_base
              else (*not iso left*)
                if iso_right then (*but iso right*)
                  let p = find i ext_base in
                  let hom_w_p = get_hom (sh_left @@ (Cat.invert sh_right)) in
                  let w = {value = obs_emb.Cat.trg ;
                           next = Lib.IntMap.add i hom_w_p Lib.IntMap.empty ;
                           prev = [0] ;
                           obs = Some (obs_emb,id_obs) ;
                           conflict = Lib.IntSet.empty ;
                           witnesses = p.witnesses}
                  in
                  let ext_base,j = add w ext_base in
                  let ext_base = {ext_base with leafs = Lib.IntSet.add j (Lib.IntSet.remove i ext_base.leafs)} in
                  let hom_p0_w = get_hom ((fun (_,g) -> g) span) in
                  let p0 = find 0 ext_base in
                  replace 0 {p0 with next = Lib.IntMap.add j hom_p0_w p0.next ; witnesses = Lib.IntSet.add j p0.witnesses} ext_base
                else (*neither iso right nor left*)
                  let conflict_w =
                    match tile_s.Cat.cospan with
                      None -> Lib.IntSet.singleton i
                    | Some _ -> Lib.IntSet.empty
                  in
                  let w = {value = obs_emb.Cat.trg ;
                           next = Lib.IntMap.empty ;
                           prev = [] ;
                           obs = Some (obs_emb,id_obs) ;
                           conflict = conflict_w ;
                           witnesses = Lib.IntSet.empty}
                  in
                  let ext_base,j = add w ext_base in
                  let ext_base = replace 0 {p0 with next = Lib.IntMap.add j (get_hom wit_emb) p0.next} ext_base in
                  let ext_base = {ext_base with leafs = Lib.IntSet.add j (Lib.IntSet.remove i ext_base.leafs)} in
                  let p = find i ext_base in
                  let ext_base =
                    if Lib.IntSet.is_empty conflict_w then ext_base
                    else
                      replace i {p with conflict = Lib.IntSet.add j p.conflict} ext_base
                  in
                  let hom_mp_p = get_hom sh_left in
                  let hom_mp_w = get_hom sh_right in
                  let mp = {value = emb_s.Cat.src ;
                            next = Lib.IntMap.add  i hom_mp_p (Lib.IntMap.add j hom_mp_w Lib.IntMap.empty) ;
                            prev = [0];
                            witnesses = Lib.IntSet.add j p.witnesses ;
                            conflict = Lib.IntSet.empty ;
                            obs = None
                           }
                  in
                  let ext_base,k = add mp ext_base in
                  let ext_base = replace j {w with prev = [k]} (replace i {p with prev = k::p.prev} ext_base)
                  in
                  let hom_p0_mp = get_hom emb_s in
                  let p0 = find 0 ext_base in
                  replace 0 {p0 with next = Lib.IntMap.add k hom_p0_mp p0.next; witnesses = Lib.IntSet.add j p0.witnesses } ext_base
             ) ext_base sharings
         else (*sharing is not worth adding to the extension base*)
           ext_base

    let insert id_obs tile ext_base =
      let rec deep_insert ext_base = function
          [] -> ext_base
        | i::tl ->
           match tile.Cat.cospan with
             None -> failwith "Witness tile is incomplete"
           | Some (obs_emb,wit_emb) ->
              deep_insert (share_insert i wit_emb id_obs obs_emb ext_base) tl

      let ext_base =
        if is_empty ext_base then
          let p0 = {value = Cat.right_of_tile tile;
                    next = Lib.IntMap.empty ;
                    prev = [];
                    obs = None;
                    conflict = Lib.IntSet.empty;
                    witnesses = Lib.IntSet.empty
                   }
          in
          proj_left (add p0 ext_base)
        else
          ext_base
      in

    let to_dot ext_base =
      let l =
        Lib.IntMap.fold
          (fun i p dot_string ->
           let str = Printf.sprintf "%d [label=\"{%s}\"];" i (String.concat "," (Lib.IntSet.fold (fun i cont -> string_of_int i::cont) p.witnesses [])) in
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
  end
