module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Graph.Make (Node)
    module Hom = Homomorphism.Make (Node)

    let (|>) = Cat.(|>)
    let (/|) = Cat.(/|)

    type t = {rules : (Graph.t * Graph.t) Lib.IntMap.t ; obs : Graph.t Lib.IntMap.t ; dict : Lib.Dict.t}
    type effect = {neg : Cat.arrows option ; pos : Cat.arrows option}

    let add_rule name (l,r) m =
      let id,dict = Lib.Dict.fresh m.dict in
      let dict = Lib.Dict.add id name dict in
      {rules = Lib.IntMap.add id (l,r) m.rules ; obs = Lib.IntMap.add id l m.obs ; dict = dict}

    let get_rule id m = Lib.IntMap.find id m.rules
    let get_obs id m = Lib.IntMap.find id m.obs

    let add_obs name o m =
      let id,dict = Lib.Dict.fresh m.dict in
      let dict = Lib.Dict.add id name dict in
      {m with obs = Lib.IntMap.add id o m.obs ; dict = dict}

    let list m =
      let l =
        Lib.IntMap.fold
          (fun id _ cont ->
           (Lib.Dict.to_name id m.dict)::cont
          ) m.obs []
      in
      List.rev l

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

    let witnesses_of_rule r m =
      let enum_witnesses obs_name id_emb obs =

	let h_eps = Cat.src id_emb in
	List.fold_left
	  (fun tiles gluing_tile ->
	   match Cat.upper_bound gluing_tile with
	     None -> tiles
	   | Some (h_eps_to_w,_) ->
              (*Checking that w and pi_eps have a sup.*)
              match Cat.share h_eps_to_w id_emb with
                [] -> tiles
              | (_,tile)::_ ->
                 if Cat.upper_bound tile = None then tiles
                 else (obs_name,gluing_tile)::tiles
	  ) [] (h_eps |> obs)
      in
      let build_witnesses effect observables =
	Lib.IntMap.fold
	  (fun obs_id o (nw,pw) ->
           let neg_witnesses =
                match effect.neg with
                  None -> []
                | Some neg -> enum_witnesses obs_id neg o
	   in
	   let pos_witnesses =
             match effect.pos with
             | None -> []
             | Some pos -> enum_witnesses obs_id pos o
	   in
	   (neg_witnesses@nw, pos_witnesses@pw)
	  ) observables ([],[])
      in
      build_witnesses (effect_of_rule r) m.obs
  end
