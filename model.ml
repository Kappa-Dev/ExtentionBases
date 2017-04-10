module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Cat.Graph
    module Hom = Cat.Hom

    let (><) = Cat.(><)

    type t = {rules : (Graph.t * Graph.t) list ; obs : Graph.t list}
    type effect = {neg : Cat.embeddings ; pos : Cat.embeddings}
	       
    let add_rule (l,r) m = {rules = (l,r)::m.rules ; obs = l::m.obs}
    let add_obs o m = {m with obs = o::m.obs}
    let empty = {rules = [] ; obs = [] }
		     
    let effect_of_rule (l,r) =
      {neg = Cat.identity (Graph.minus l r) l ;
       pos = Cat.identity (Graph.minus r l) r }

    let witnesses_of_model m =
      let get_effects m = List.map effect_of_rule m.rules
      in
      let enum_witnesses id_emb obs =
	let h_eps = id_emb.Cat.src in
	let pi_eps = id_emb.Cat.trg in
	List.fold_left
	  (fun tiles gluing_tile ->
	   match Cat.sup_of_tile gluing_tile with
	     None -> tiles
	   | Some w ->
	      let mpo = Cat.multi_pushout [Hom.identity (Graph.nodes h_eps)] w pi_eps in
	      match mpo with
		[(None,_)] -> tiles (*Gluing is incompatible with pi_eps*)
	      | [(Some sup,hom)] -> gluing_tile::tiles (*should use [(sup,hom)] here to minimize exploration*)
	      | _ -> failwith "Invariant violation: mpo should have at most one element"
	  ) [] (h_eps >< obs) 
      in
      let rec build_witnesses effects nw pw = function
	  [] -> (nw,pw)
	| o::obs_l ->
	   let nw,pw =
	     List.fold_left
	       (fun (nw,pw) effect ->
		let neg_witnesses = enum_witnesses effect.neg o
		in
		let pos_witnesses = enum_witnesses effect.pos o
		in
		(neg_witnesses@nw,pos_witnesses@pw)
	       ) (nw,pw) effects
	   in
	   build_witnesses effects nw pw obs_l
      in
      build_witnesses (get_effects m) [] [] m.obs
      
  end
