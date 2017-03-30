module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    module Hom = Homomorphism.Make (Node)
		    
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
			      
    let string_of_gluings = fun gluings ->
      String.concat
	"\n"
	(List.map
	   (fun (inter,_,_,hom,sup_opt) ->
	    match sup_opt with
	      None -> (Graph.to_string inter^" using "^(Hom.to_string hom)^"[NO SUP]")
	    | Some sup ->
	       (Graph.to_string inter^" using "^(Hom.to_string hom)^" sup is "^(Graph.to_string sup)) 
	   ) gluings
	)

    let graph_of_library name =
      try
	let edges = Lib.StringMap.find name Node.library in
	draw edges Graph.empty
      with
	Graph.Incoherent -> failwith (name^" is not a coherent graph!")

    let generate_tests () =
      let square = graph_of_library "square" in
      let house = graph_of_library "house" in
      let arrows = Cat.create square house in
      print_string "Embeddings...\n\n" ;
      print_string "Embeddings of square into house are: \n" ;
      print_string (Cat.to_string arrows) ;
      print_newline() ;
      print_string "Extensions of square into house are: \n" ;
      print_string (Cat.to_string (Cat.extension_class arrows)) ;
      print_newline() ;
      print_string "Matches of square into house are: \n" ;
      print_string (Cat.to_string (Cat.matching_class arrows)) ;
      print_newline() ;    
      let arrows = Cat.create house house in
      print_string "Auto morphisms of house are: \n" ;
      print_string (Cat.to_string arrows) ;
      print_newline() ;
      let gluings = Cat.gluings square house in
      print_string "Gluings of square into house are: \n" ;
      print_string (string_of_gluings gluings) ;
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
  let abc = KappaShape.graph_of_library "abc" in
  let abd = KappaShape.graph_of_library "abd" in
  let gluings = KappaShape.Cat.gluings abc abd in
  print_string "Gluings of abc into abd are: \n" ;
  print_string (KappaShape.string_of_gluings gluings) ;
  print_string "***** Degree nodes ***** \n" ;
  DegreeShape.generate_tests()
