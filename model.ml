module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Graph.Make (Node)
    module Hom = Homomorphism.Make (Node)

    let (|>) = Cat.(|>)

    type t = {rules : (Graph.t * Graph.t) Lib.IntMap.t ; obs : Graph.t Lib.IntMap.t ; dict : Lib.Dict.t}
    type effect = {neg : Cat.arrows option ; pos : Cat.arrows option}

    let add_rule name (l,r) m =
      let id,dict = Lib.Dict.fresh m.dict in
      let dict = Lib.Dict.add id name dict in
      {rules = Lib.IntMap.add id (l,r) m.rules ; obs = Lib.IntMap.add id l m.obs ; dict = dict}

    let get_rule id m = Lib.IntMap.find id m.rules
    let get_obs id m = Lib.IntMap.find id m.obs

    let add_obs name o m =
      Printf.printf "Binding %s to graph %s\n" name (Graph.to_string o) ;
      try
        let id,dict = Lib.Dict.fresh m.dict in
        let dict = Lib.Dict.add id name dict in
        {m with obs = Lib.IntMap.add id o m.obs ; dict = dict}
      with
        Lib.Dict.Clashing -> (print_endline ("Name "^name^" already used, not adding observable!\n") ; m)

    let list m =
      let l_obs =
        Lib.IntMap.fold
          (fun id _ cont ->
           (Lib.Dict.to_name id m.dict)::cont
          ) m.obs []
      in
      let l_rules =
        Lib.IntMap.fold
          (fun id _ cont ->
            (Lib.Dict.to_name id m.dict)::cont
          ) m.rules []
      in
      (List.rev l_obs,List.rev l_rules)

    let empty = {rules = Lib.IntMap.empty ; obs = Lib.IntMap.empty ; dict = Lib.Dict.empty}

    let effect_of_rule (l,r) =
      let minus g h =
        let m = Graph.minus g h in
        if Graph.is_empty m then None
        else Some (Cat.identity m g)
      in
      {neg = minus l r ;
       pos = minus r l
      }

    let witnesses_of_rule ?obs r m =
      let enum_witnesses obs_name id_emb obs cont =
	let h_eps = Cat.src id_emb in
        let extensions = h_eps |> obs in
        List.fold_left (fun cont tile -> (obs_name,tile)::cont) cont extensions
      in
      let build_witnesses effect observables =
	Lib.IntMap.fold
	  (fun obs_id o (nw,pw) ->
           let neg_witnesses =
                match effect.neg with
                  None -> []
                | Some neg -> enum_witnesses obs_id neg o nw
	   in
	   let pos_witnesses =
             match effect.pos with
             | None -> []
             | Some pos -> enum_witnesses obs_id pos o pw
	   in
	   (neg_witnesses, pos_witnesses)
	  ) observables ([],[])
      in
      match obs with
        None -> build_witnesses (effect_of_rule r) m.obs
      | Some obs_id ->
         build_witnesses
           (effect_of_rule r)
           (Lib.IntMap.add
              obs_id
              (Lib.IntMap.find obs_id m.obs)
              Lib.IntMap.empty
           )
  end
