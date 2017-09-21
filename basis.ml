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

    let add p ext_base =
      ({ext_base with points = Lib.IntMap.add ext_base.fresh p ext_base.points ;
                      leaves = Lib.IntSet.add ext_base.fresh ext_base.leaves ;
                      fresh = ext_base.fresh+1
       },ext_base.fresh-1)

    let replace i p ext_base =
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let empty ?(min = 1) ?(deep=false) ?(unique=true) =
      assert (min>0) ;
      {points = Lib.IntMap.empty ;
       fresh = 0 ;
       sharing = {min = min ; deep = deep ; unique = unique} ;
       leaves = Lib.IntSet.empty}

    let is_empty ext_base = ext_base.fresh = 0

    let find i ext_base = Lib.IntMap.find i ext_base.points

    let cut_leaf i ext_base =
      let pi = find i ext_base in
      if Lib.IntMap.is_empty pi.next then
        List.fold_left
          (fun ext_base j ->
           let pj = find j ext_base in
           replace j {pj with next = Lib.IntMap.remove i pj.next ;
                              witnesses = Lib.IntSet.remove j pj.witnesses
                     } ext_base
          ) ext_base pi.prev
      else
        failwith "Can only remove leaves"

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
      if not (mem i ext_base) then
        failwith ("Unkown point "^(string_of_int i)^" in extension base")
      else
        let p0 = find 0 ext_base in
        let p = find i ext_base in
        try {Cat.src = p0.value ; Cat.trg = p.value ; Cat.maps = [Lib.IntMap.find i p0.next]}
        with Not_found ->
          if i=0 then Cat.identity p0.value p0.value
          else failwith "Trying to compare a witness with an unkown point"

    let add_extension i j hom_ij ext_base =
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
      let ext_base =
        if is_empty ext_base then
          let ext_base,_ = add {value = emb_w.Cat.src;
                                next = Lib.IntMap.empty ;
                                prev = [] ;
                                obs = None ;
                                conflict = Lib.IntSet.empty ;
                                witnesses = Lib.IntSet.empty
                               } ext_base
          in
          {ext_base with leaves = Lib.IntSet.singleton 0}
        else ext_base
      in
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
      {ext_base with leaves = Lib.IntSet.add k ext_base.leaves}

    let add_conflict i j ext_base =
      let pi = find i ext_base in
      let pj = find j ext_base in
      replace i {pi with conflict = Lib.IntSet.add j pi.conflict}
              (replace j {pj with conflict = Lib.IntSet.add i pj.conflict} ext_base)

    (*Invariant j is the new witness in the base*)
    let compare i j ext_base =
      let emb_to_i = find_extension i ext_base in
      let emb_to_j = find_extension j ext_base in
      match Cat.share ext_base.sharing.unique (emb_to_i,emb_to_j) with
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
              let pi = find i ext_base in
              let pj = find j ext_base in
              (*Special cases, when sharing reveals a sub-graph relationship*)
              if iso_left then
                (*Both left and right embeddings of the span are actually isos*)
                if iso_right then (*passing observable of pj to pi*)
                  let obs_emb,obs_ids = match pj.obs with None -> failwith "not a witness" | Some v -> v in
                  let obs_emb,obs_ids,new_obs =
                    match pi.obs with
                      None -> ((sh_left @@ (Cat.invert sh_right)) @@ obs_emb, obs_ids, true)
                    | Some (obs_emb,obs_ids') -> (obs_emb,obs_ids'@obs_ids, false) (*first obs_id in the list points to the reference graph*)
                  in
                  let ext_base = replace i {pi with obs = Some (obs_emb,obs_ids)} ext_base in
                  let ext_base = cut_leaf j ext_base in
                  if new_obs then
                    (*sons of i should know that i is a now the id of a witness*)
                    update_witnesses i ext_base
                  else
                    ext_base
                else (*Iso left but not iso right*)
                  let hom_pi_pj = get_hom (sh_right @@ (Cat.invert sh_left)) in
                  add_extension i j hom_pi_pj ext_base
              else (*not iso left*)
                if iso_right then (*but iso right*)
                  let hom_pj_pi = get_hom (sh_left @@ (Cat.invert sh_right)) in
                  add_extension j i hom_pj_pi ext_base
                else (*neither iso right nor left*)
                  let ext_base =
                    match tile_s.Cat.cospan with
                      None -> add_conflict i j ext_base
                    | Some _ -> ext_base
                  in
                  let hom_mp_pi = get_hom sh_left in
                  let hom_mp_pj = get_hom sh_right in
                  let mp = {value = emb_s.Cat.src ;
                            next = Lib.IntMap.add  i hom_mp_pi (Lib.IntMap.add j hom_mp_pj Lib.IntMap.empty) ;
                            prev = [0];
                            witnesses = Lib.IntSet.add j pi.witnesses ;
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
           ext_base

    let insert id_obs tile ext_base =
      let rec deep_insert ext_base acc = function
          [] -> if acc = [] then ext_base else deep_insert ext_base [] acc
        | i::tl ->
           match tile.Cat.cospan with
             None -> failwith "Witness tile is incomplete"
           | Some (obs_emb,wit_emb) ->
              let acc =
                if ext_base.sharing.deep then
                  let p = find i ext_base in
                  List.fold_left
                    (fun acc j ->
                     
                    ) acc p.prev
                else acc
              in
              deep_insert (share_insert i wit_emb id_obs obs_emb ext_base) acc tl
      in
      deep_insert empty 

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
