module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Cat.Graph
    module Hom = Cat.Hom

    let (><) = Cat.(><)

    type t = {rules : (Graph.t * Graph.t) Lib.IntMap.t ; obs : Graph.t Lib.IntMap.t ; dict : Lib.Dict.t}
    type effect = {neg : Cat.embeddings option ; pos : Cat.embeddings option}

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

    (** witnesses_of_model : model -> (r_id -> obs_id -> cospan list) where the [cospan] is always the identity for obs_id*)
    let witnesses_of_model m =
      let get_effects m = Lib.IntMap.fold
			    (fun id rule effects ->
			     (id,effect_of_rule rule)::effects
			    ) m.rules []
      in
      let enum_witnesses obs_name id_emb obs =
	let h_eps = id_emb.Cat.src in
	List.fold_left
	  (fun tiles gluing_tile ->
	   match gluing_tile.Cat.cospan with
	     None -> tiles
	   | Some (_,h_eps_to_w) ->
              assert (List.tl (h_eps_to_w.Cat.maps) = []) ;
              (*Checking that w and pi_eps have a sup.*)
              if Cat.mpo (h_eps_to_w,id_emb) = []
              then (print_string "discarded!\n" ; tiles)
              else (obs_name,gluing_tile)::tiles
	  ) [] (h_eps >< obs)
      in
      let build_witnesses effects observables =
	List.fold_left
	  (fun (nw,pw) (r_id,effect) ->
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
              let neg = try Lib.IntMap.find r_id nw with Not_found -> []
	      in
	      let pos = try Lib.IntMap.find r_id pw with Not_found -> []
	      in
	      (Lib.IntMap.add r_id (neg_witnesses@neg) nw, Lib.IntMap.add r_id (pos_witnesses@pos) pw)
	     ) observables (nw,pw)
	  ) (Lib.IntMap.empty,Lib.IntMap.empty) effects

      in
      let build_extensions witnesses =
	Lib.IntMap.fold
	  (fun rule_id tiles extb ->
	   List.fold_left
	     (fun extensions (obs_id,tile) -> (*rule_id --(+/-)--> obs_id through tile *)
	      match tile.Cat.cospan with
		None -> failwith "Invariant violation: gluing is not complete"
	      | Some cospan ->
		 let ext_r_id = try Lib.IntMap.find rule_id extensions with Not_found -> Lib.IntMap.empty
		 in
                 let ext_r_id_obs_id = try Lib.IntMap.find obs_id ext_r_id with Not_found -> []
                 in
		 Lib.IntMap.add rule_id (Lib.IntMap.add obs_id (cospan::ext_r_id_obs_id) ext_r_id) extensions
	     ) extb tiles
	  ) witnesses Lib.IntMap.empty
      in
      let neg_witnesses,pos_witnesses = build_witnesses (get_effects m) m.obs
      in
      let neg_extensions = build_extensions neg_witnesses in
      let pos_extensions = build_extensions pos_witnesses in
      (neg_extensions,pos_extensions)
  end
