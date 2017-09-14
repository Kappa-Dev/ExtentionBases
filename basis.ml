module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)

    type point = {value : Graph.t ; next : (Hom.t * int) list ; obs : Cat.embeddings option ; conflict : Lib.IntSet.t}
    type param = {min : int ; deep : bool ; unique: bool}

    type t = {points : point Lib.IntMap.t ; size : int ; sharing : param}

    let add_point p ext_base =
      {ext_base with points = Lib.IntMap.add ext_base.size p ext_base.points ;
                     size = ext_base.size+1}

    let init h_eps min deep unique =
      let p0 = {value = h_eps ; next = [] ; obs = None ; conflict = Lib.IntSet.empty} in
      {points = Lib.IntMap.add 0 p0 Lib.IntMap.empty ; size = 1 ; sharing = {min = min ; deep = deep ; unique = unique}}

    let get_point i ext_base = Lib.IntMap.find i ext_base.points

    let to_emb i f j ext_base =
      try
        let iG = (get_point i ext_base).value in
        let jG = (get_point j ext_base).value in
        {Cat.src = iG ; Cat.trg = jG ; Cat.maps = [f]}
      with Not_found -> failwith "Unkown point identifier"

    let step span ext_base =
      match Cat.share ext_base.sharing.unique span with
        [] -> ext_base
      | (emb_sharing,_)::_ as sharings ->
         let n_trg = Graph.size_edge emb_sharing.Cat.trg in
         let n_src = Graph.size_edge emb_sharing.Cat.src in
         (*if computed sharing is interesting enough*)
         let ext_base =
           if n_trg - n_src >= ext_base.sharing.min then
             List.fold_left
               (fun ext_base (emb_s,tile_s) ->
                let 
               ) ext_base sharings
           else
             ext_base
         in
  end
