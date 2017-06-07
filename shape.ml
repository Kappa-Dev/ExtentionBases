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
      let ext1 = List.hd (Cat.flatten (Cat.extension_class (Cat.embed one house))) in
      let ext2 = List.hd (Cat.flatten (Cat.extension_class (Cat.embed one dsquare))) in
      Printf.printf "adding sharing to: \n %s\n" (Cat.string_of_span (ext1,ext2)) ;
      print_string (Cat.share (ext1,ext2)) ;
      print_newline () ;

      (*let model = Model.add_rule "0->1" (void,one) Model.empty in
      let model = Model.add_rule "1->house" (one,house) model in
      let model = Model.add_rule "1->square" (house,square) model in
      let model = Lib.StringMap.fold
		    (fun name _ model ->
		     Model.add_obs name (graph_of_library name) model
		    ) Node.library model
      in
      print_newline() ;
      Model.witnesses_of_model model ;
      let one_to_square = Cat.extension_class (Cat.embed one square) in
      let one_to_house = Cat.extension_class (Cat.embed one house) in
      let share = Cat.share one_to_square one_to_house in
      print_string share ; print_newline () ;*)
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
