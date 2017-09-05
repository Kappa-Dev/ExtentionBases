module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Cat.Graph
    module Hom = Cat.Hom

    let (><) = Cat.(><)

    type t = {rules : (Graph.t * Graph.t) Lib.IntMap.t ; obs : Graph.t Lib.IntMap.t ; dict : string Lib.IntMap.t ; fresh : int}
    type effect = {neg : Cat.embeddings option ; pos : Cat.embeddings option ; name : int}

    let name_of_id id m = Lib.IntMap.find id m.dict

    let add_rule name (l,r) m =
      let id = m.fresh in
      {rules = Lib.IntMap.add id (l,r) m.rules ; obs = Lib.IntMap.add id l m.obs ; dict = Lib.IntMap.add id name m.dict ; fresh = m.fresh+1}

    let add_obs name o m =
      let id = m.fresh in
      {m with obs = Lib.IntMap.add id o m.obs ; dict = Lib.IntMap.add id name m.dict ; fresh = m.fresh+1}

    let empty = {rules = Lib.IntMap.empty ; obs = Lib.IntMap.empty ; dict = Lib.IntMap.empty ; fresh = 0}

    let effect_of_rule id (l,r) =
      let minus g h =
        let m = Graph.minus g h in
        if Graph.is_empty m then None
        else Some (Cat.identity m g)
      in
      {neg = minus l r ;
       pos = minus r l ;
       name = id
      }


    let witnesses_of_model m =
      let get_effects m = Lib.IntMap.fold
			    (fun id rule effects ->
			     (effect_of_rule id rule)::effects
			    ) m.rules []
      in
      let enum_witnesses obs_name id_emb obs =
	let h_eps = id_emb.Cat.src in
	let pi_eps = id_emb.Cat.trg in
	List.fold_left
	  (fun tiles gluing_tile ->
	   match gluing_tile.Cat.cospan with
	     None -> tiles
	   | Some (_,h_eps_to_w) ->
              assert (List.tl (h_eps_to_w.Cat.maps) = []) ;

              (*Checking that w and pi_eps have a sup.*)
              if Cat.mpo (h_eps_to_w,id_emb) = [] then tiles
              else (obs_name,gluing_tile)::tiles
          (*
            (*Checking that h_eps' is included in the witness*)
            if Graph.is_included h_eps' witness then
            (obs_name,gluing_tile)::tiles
            else
            tiles
           *)
	  ) [] (h_eps >< obs)
      in
      let build_witnesses effects observables =
	List.fold_left
	  (fun (nw,pw) effect ->
	   Lib.IntMap.fold
	     (fun obs_name o (nw,pw) ->
	      let neg_witnesses =
                match effect.neg with
                  None -> []
                | Some neg -> enum_witnesses obs_name neg o
	      in
	      let pos_witnesses =
                match effect.pos with
                  | None -> []
                  | Some pos -> enum_witnesses obs_name pos o
	      in
	      let neg = try Lib.IntMap.find effect.name nw with Not_found -> []
	      in
	      let pos = try Lib.IntMap.find effect.name pw with Not_found -> []
	      in
	      (Lib.IntMap.add effect.name (neg_witnesses@neg) nw, Lib.IntMap.add effect.name (pos_witnesses@pos) pw)
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
		 let ext_r_id = try Lib.IntMap.find rule_id extensions with Not_found -> []
		 in
		 Lib.IntMap.add rule_id ((obs_id,cospan)::ext_r_id) extensions
	     ) extb tiles
	  ) witnesses Lib.IntMap.empty
      in
      let neg_witnesses,pos_witnesses = build_witnesses (get_effects m) m.obs
      in
      let neg_extensions = build_extensions neg_witnesses in
      let pos_extensions = build_extensions pos_witnesses in
      (neg_extensions,pos_extensions)
  end
