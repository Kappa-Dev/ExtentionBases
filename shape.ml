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
	 	     
    let copy g =
      match Cat.multi_pushout [Hom.empty] Graph.empty g with
	[] -> failwith "Invariant violation"
      | [(Some g',_)] -> g'
      | _ -> failwith "Invariant violation"
			      
    let string_of_tiles = fun tiles ->
      String.concat
	"\n*********** \n"
	(List.map
	   (fun tile ->
	    match tile.Cat.cospan with
	      None -> (Cat.string_of_span tile.Cat.span)^"\n[NO_SUP]"
	    | Some co_span ->
	       (Cat.string_of_span tile.Cat.span)^"\n"^(Cat.string_of_co_span co_span)
	   ) tiles
	)

    let graph_of_library name =
      try
	let edges = Lib.StringMap.find name Node.library in
	draw edges Graph.empty
      with
	Graph.Incoherent -> failwith (name^" is not a coherent graph!")

				     
    let generate_tests () =
      let (><) = Cat.(><) in
      let void = graph_of_library "empty" in
      let square = graph_of_library "square" in
      let house = graph_of_library "house" in
      let triangle = graph_of_library "triangle" in
      let one = graph_of_library "one" in
      let embeddings = Cat.embed square house in
      print_string "------- EQUIVALENCE CLASSES ---------\n" ;
      print_string "Embeddings...\n\n" ;
      print_string "Embeddings of square into house are: \n" ;
      print_string (Cat.string_of_embeddings embeddings) ;
      print_newline() ;
      print_string "Extensions of square into house are: \n" ;
      print_string (Cat.string_of_embeddings (Cat.extension_class embeddings)) ;
      print_newline() ;
      print_string "Matches of square into house are: \n" ;
      print_string (Cat.string_of_embeddings (Cat.matching_class embeddings)) ;
      print_newline() ;    
      let embeddings = Cat.embed house house in
      print_string "Auto morphisms of house are: \n" ;
      print_string (Cat.string_of_embeddings embeddings) ;
      print_newline() ;
      print_string "------- GLUINGS ---------\n" ;
      let gluings =  square >< house in
      print_string "Gluings of square into house are: \n" ;
      print_string (string_of_tiles gluings) ;
      print_newline() ;
      let gluings =  triangle >< triangle in
      print_string "Gluings of triangles into itself are: \n" ;
      print_string (string_of_tiles gluings) ;
      print_newline() ;
      print_string "------- RULES ---------\n" ;
      let model = Model.add_rule (one,square) Model.empty in
      let model = Model.add_rule (void,one) model in
      let model = Lib.StringMap.fold
		    (fun name _ model ->
		     Model.add_obs (graph_of_library name) model
		    ) Node.library model
      in
      let witnesses = Model.witnesses_of_model model in
      print_string "Negative witnesses of the model are: \n" ;
      print_string (string_of_tiles ((fun (neg,pos) -> neg) witnesses)) ;
      print_newline() ;
    
  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode) 
module DegreeShape = Make (Node.DegreeNode)  
			  
let test =
  print_string "***** Simple nodes *****\n" ;
  SimpleShape.generate_tests() ;
  print_string "***** Kappa nodes ***** \n" ;
  KappaShape.generate_tests() ;
  print_string "***** Degree nodes ***** \n" ;
  DegreeShape.generate_tests()

