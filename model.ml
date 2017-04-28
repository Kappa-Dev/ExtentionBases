module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Cat.Graph
    module Hom = Cat.Hom
    module IMap = Lib.IntMap

    let (><) = Cat.(><)

    type t = {rules : (Graph.t * Graph.t) IMap.t ; obs : Graph.t IMap.t ; dict : string IMap.t ; fresh : int}
    type effect = {neg : Cat.embeddings ; pos : Cat.embeddings ; name : int}

    let name_of_id id m = IMap.find id m.dict
				    
    let add_rule name (l,r) m =
      let id = m.fresh in
      {rules = IMap.add id (l,r) m.rules ; obs = IMap.add id l m.obs ; dict = IMap.add id name m.dict ; fresh = m.fresh+1}
	
    let add_obs name o m =
      let id = m.fresh in
      {m with obs = IMap.add id o m.obs ; dict = IMap.add id name m.dict ; fresh = m.fresh+1}
	
    let empty = {rules = IMap.empty ; obs = IMap.empty ; dict = IMap.empty ; fresh = 0}
		  
    let effect_of_rule id (l,r) =
      {neg = Cat.identity (Graph.minus l r) l ;
       pos = Cat.identity (Graph.minus r l) r ;
       name = id
      }


    let witnesses_of_model m =
      let get_effects m = IMap.fold 
			    (fun id rule effects -> 
			     (effect_of_rule id rule)::effects
			    ) m.rules []
      in
      let enum_witnesses name id_emb obs =
	let h_eps = id_emb.Cat.src in
	let pi_eps = id_emb.Cat.trg in
	List.fold_left
	  (fun tiles gluing_tile ->
	   match gluing_tile.Cat.cospan with
	     None -> tiles
	   | Some (_,h_eps_to_w) ->
	      let mpos = Cat.mpo (Cat.identity h_eps pi_eps,h_eps_to_w) in
	      match mpos with
		[] -> tiles (*Gluing is incompatible with pi_eps*)
	      | [tile] -> (name,gluing_tile)::tiles (*should use [tile] here to minimize exploration*)
	      | _ -> failwith "Invariant violation: mpo should have at most one element"
	  ) [] (h_eps >< obs) 
      in
      let build_witnesses effects observables =
	List.fold_left
	  (fun (nw,pw) effect ->
	   IMap.fold
	     (fun obs_name o (nw,pw) ->
	      let neg_witnesses = enum_witnesses obs_name effect.neg o
	      in
	      let pos_witnesses = enum_witnesses obs_name effect.pos o
	      in
	      let neg = try IMap.find effect.name nw with Not_found -> []
	      in
	      let pos = try IMap.find effect.name pw with Not_found -> []
	      in
	      (IMap.add effect.name (neg_witnesses@neg) nw, IMap.add effect.name (pos_witnesses@pos) pw)
	     ) observables (nw,pw)
	  ) (IMap.empty,IMap.empty) effects

      in
      let build_extensions witnesses =
	IMap.fold
	  (fun rule_id tiles extb ->
	   List.fold_left
	     (fun extensions (obs_id,tile) -> (*rule_id --(+/-)--> obs_id through tile *)
	      match tile.Cat.cospan with
		None -> failwith "Invariant violation: gluing is not complete"
	      | Some cospan ->
		 let ext_r_id = try IMap.find rule_id extensions with Not_found -> []
		 in
		 IMap.add rule_id ((obs_id,cospan)::ext_r_id) extensions
	     ) extb tiles
	  ) witnesses IMap.empty
      in
      let neg_witnesses,pos_witnesses = build_witnesses (get_effects m) m.obs
      in
      let neg_extensions = build_extensions neg_witnesses in
      let pos_extensions = build_extensions pos_witnesses in
      IMap.iter
	(fun rule_id l ->
	 List.iter
	   (fun (obs_id,cospan) ->
	    Printf.printf "%s -(-)-> %s is:\n %s\n"
			  (name_of_id rule_id m)
			  (name_of_id obs_id m)
			  (Cat.string_of_co_span cospan)
	   ) l ;
	) neg_extensions ;
      IMap.iter
	(fun rule_id l ->
	 List.iter
	   (fun (obs_id,cospan) ->
	    Printf.printf "%s -(+)-> %s is:\n %s\n"
			  (name_of_id rule_id m)
			  (name_of_id obs_id m)
			  (Cat.string_of_co_span cospan)
	   ) l ;
	) pos_extensions
  end
