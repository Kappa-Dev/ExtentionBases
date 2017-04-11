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
      let get_effects m = IMap.fold (fun id rule effects -> (effect_of_rule id rule)::effects) m.rules []
      in
      let enum_witnesses name id_emb obs =
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
	      | [(Some sup,hom)] -> (name,gluing_tile)::tiles (*should use [(sup,hom)] here to minimize exploration*)
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
      let build_spans witnesses =
	let embeddings = 
	  IMap.fold
	    (fun rule_id tiles extb ->
	     let ext_rule_id = 
	       List.fold_left
		 (fun ext_rule_id (obs_id,tile) -> (*rule_id --(+/-)--> obs_id through tile *)
		  match Cat.sup_of_tile tile with
		    None -> failwith "Invariant violation: gluing is not complete"
		  | Some sup ->
		     (Cat.identity (Cat.right_of_tile tile) sup)::ext_rule_id
		 ) [] tiles
	     in
	     ext_rule_id@extb
	    ) witnesses []
	in
	let spans,_ =
	  List.fold_left
	    (fun (cont,offset) emb ->
	     let spans,_ =
	       List.fold_left
		 (fun (spans,offset) emb' ->
		  if offset >= 0 then (spans,offset-1)
		  else
		    ((emb,emb')::spans,offset)
		 ) ([],offset) embeddings
	     in
	     (spans@cont,offset+1)
	    ) ([],0) embeddings
	in
	spans
      in
      build_witnesses (get_effects m) m.obs
		      (*
      let neg_witnesses,pos_witnesses = build_witnesses (get_effects m) m.obs
      in
      let neg_spans = build_spans neg_witnesses in
      let pos_spans = build_spans pos_witnesses in
      print_string (String.concat "\n" (List.map Cat.string_of_span neg_spans)) ; print_newline() ; 
      print_string (String.concat "\n" (List.map Cat.string_of_span pos_spans)) 
		       *)
  end
