module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    module Hom = Homomorphism.Make (Node)
    module Model = Model.Make (Node)

    let draw_line u v g =
      let g =
	List.fold_left
	  (fun g u ->
	   Graph.add_node u g
	  ) g [u;v] in
      Graph.add_edge u v g

    let rec draw line_list g =
      match line_list with
	[] -> g
      | (u,v)::tl ->
	 let g' = draw_line u v g in
	 draw tl g'


    let graph_of_library name =
      try
	let edges = Lib.StringMap.find name Node.library in
	draw edges Graph.empty
      with
	Graph.Incoherent -> failwith (name^" is not a coherent graph!")


    let generate_tests () =
      let one = graph_of_library "one" in
      let house = graph_of_library "house" in
      let dsquare = graph_of_library "dsquare" in
      let model = Model.add_rule "one->house" (one,house) Model.empty in
      let eff_oh = Model.effect_of_rule (one,house) in
      Printf.printf "Negative effect of one->house: %s\n" (match eff_oh.Model.neg with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;
      Printf.printf "Positive effect of one->house: %s\n" (match eff_oh.Model.pos with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;

      let model = Model.add_rule "house->dsquare" (house,dsquare) model in
      let eff_hd = Model.effect_of_rule (house,dsquare) in

      Printf.printf "Negative effect of house->dsquare: %s\n" (match eff_hd.Model.neg with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;
      Printf.printf "Positive effect of house->dsquare: %s\n" (match eff_hd.Model.pos with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;

      let model = Lib.StringMap.fold
		    (fun name _ model ->
		     Model.add_obs name (graph_of_library name) model
		    ) Node.library model
      in
      print_newline() ;
      let nw,pw = Model.witnesses_of_model model in
      Lib.IntMap.iter (fun r_id pos_map ->
		       let rule_name = Lib.Dict.to_name r_id model.Model.dict
		       in
                       Lib.IntMap.iter
                         (fun obs_id l ->
                          Printf.printf "Rule %s has %d positive witnesse(s) for observable %s\n" rule_name (List.length l) (Lib.Dict.to_name obs_id model.Model.dict)
                         ) pos_map ;
		      ) pw ;
      print_newline() ;
      Lib.IntMap.iter (fun r_id neg_map ->
		       let rule_name = Lib.Dict.to_name r_id model.Model.dict
		       in
                       Lib.IntMap.iter
                         (fun obs_id l ->
                          Printf.printf "Rule %s has %d negative witnesse(s) for observable %s\n" rule_name (List.length l) (Lib.Dict.to_name obs_id model.Model.dict) ;
                          List.iter (fun cospan -> Printf.printf "%s\n" (Cat.string_of_co_span cospan)) l ;
                         ) neg_map ;
		      ) nw ;
      print_newline()

  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode)
module DegreeShape = Make (Node.DegreeNode)
