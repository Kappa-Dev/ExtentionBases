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
      let square = graph_of_library "square" in
      let dsquare = graph_of_library "dsquare" in
      let model = Model.add_rule "1->house" (one,house) Model.empty in
      let eff = Model.effect_of_rule 0 (one,house) in
      Printf.printf "Negative effect of 1->house: %s\n" (match eff.Model.neg with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;
      Printf.printf "Positive effect of 1->house: %s\n" (match eff.Model.pos with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;
      let model = Model.add_rule "house->dsquare" (house,dsquare) model in
      let eff = Model.effect_of_rule 0 (house,dsquare) in
      Printf.printf "Negative effect of house->dsquare: %s\n" (match eff.Model.neg with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;
      Printf.printf "Positive effect of house->dsquare: %s\n" (match eff.Model.pos with None -> "none" | Some emb -> Cat.string_of_embeddings emb) ;

      let model = Lib.StringMap.fold
		    (fun name _ model ->
		     Model.add_obs name (graph_of_library name) model
		    ) Node.library model
      in
      print_newline() ;
      let nw,pw = Model.witnesses_of_model model in
      Lib.IntMap.iter (fun obs_id neglist ->
		       let obs_name = Model.name_of_id obs_id model
		       in
                       Printf.printf "observable %s has %d negative witnesses\n" obs_name (List.length neglist) ;
                       let _ =
		         List.fold_left (fun (prev_name,counter) (name_id,neg_effect) ->
				         let name = Model.name_of_id name_id model in
                                         if prev_name = name then
                                           (prev_name,counter+1)
                                         else
                                           (Printf.printf "%d witnesses for %s\n" counter name ;
                                            (name,1))
				        ) ("",0) neglist
                       in
                       print_newline() ;
		      ) nw ;
      print_newline()
  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode)
module DegreeShape = Make (Node.DegreeNode)
