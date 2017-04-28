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
      let void = graph_of_library "empty" in
      let two = graph_of_library "two" in
      print_string "------- RULES ---------\n" ;
      let model = Model.add_rule "0->2" (void,two) Model.empty in
      let model = Model.add_rule "2->0" (two,void) model in
      let model = Lib.StringMap.fold
		    (fun name _ model ->
		     Model.add_obs name (graph_of_library name) model
		    ) Node.library model
      in
      print_newline() ;
      Model.witnesses_of_model model ;
			       (*
      let nw,pw = Model.witnesses_of_model model in
      
      Lib.IntMap.iter (fun obs_id neglist ->
		       let obs_name = Model.name_of_id obs_id model
		       in
		       List.iter (fun (name_id,neg) ->
				  let name = Model.name_of_id name_id model in
				  print_string ("Negative witness for ** "^name^" |><| "^obs_name^" ** \n") ;
				  print_string (Cat.string_of_tile neg) ;
				  print_newline() ;
				 ) neglist ;
		      ) nw ;
      print_newline() ;
      Lib.IntMap.iter (fun obs_id poslist ->
		       let obs_name = Model.name_of_id obs_id model
		       in
		       List.iter (fun (name_id,pos) ->
				  let name = Model.name_of_id name_id model in
				  print_string ("Positive witness for ** "^name^" |><| "^obs_name^" ** \n") ;
				  print_string (Cat.string_of_tile pos) ;
				  print_newline() ;
				 ) poslist ;
		      ) pw ;*)
      print_newline()        
  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode) 
module DegreeShape = Make (Node.DegreeNode)  
