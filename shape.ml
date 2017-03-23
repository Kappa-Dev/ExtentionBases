module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = GraphCat.Make (Node)
    module Hom = Morphism.Make_structure_preserving (Node)
		    
    let draw_line p_u p_v g =
      let u = Node.create p_u in
      let v = Node.create p_v in
      let g =
	List.fold_left
	  (fun g u ->
	   Graph.add_node u g
	  ) g [u;v] in
     Graph.add_edge u v g

    let rec draw line_list g =
      match line_list with
	[] -> Some g
      | (p_u,p_v)::tl ->
	   let opt = try Some (draw_line p_u p_v g) with Graph.Incoherent -> None
	   in
	   match opt with
	     Some g' -> draw tl g'
	   | None -> None

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
	     | Some sup -> (Graph.to_string inter^" using "^(Hom.to_string hom)^" sup is "^(Graph.to_string sup)) 
	   ) gluings
	)
		  
  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode) 
module DegreeShape = Make (Node.DegreeNode)  

let test =
  match
    DegreeShape.draw 
      [
	([0;2],[1;1]) ;
	([0;2],[2;1])
      ]
      DegreeShape.Graph.empty
  with
    None -> print_string "Graph is incoherent\n" 
  | Some g -> print_string (DegreeShape.Graph.to_string g) ; print_newline ()

let test2 () =
  print_string "Starting test...\n" ;
  let kl =
    KappaShape.draw 
      [
	([0;0;0],[1;0;0]) ;
	([0;1;0],[2;1;0]) 
      ]
      KappaShape.Graph.empty
  in
  let kdis =
    KappaShape.draw 
      [
	([0;0;0],[1;0;0]) ;
	([2;1;0],[3;1;0]) 
      ]
      KappaShape.Graph.empty
  in
  let kl,kdis = 
    match (kl,kdis) with
      (Some g,Some h) -> (g,h)
    | _ -> failwith "Graph is undefined\n" 
  in
  let khouse =
    KappaShape.draw
      [ (*Base*)
	([0;0;0],[1;0;0]) ;
	([1;1;0],[2;1;0]) ;
	([2;0;0],[3;0;0]) ;
	([3;1;0],[0;1;0]) ;
	(*Roof*)
	([3;2;0],[2;2;0]) 
      ]
      KappaShape.Graph.empty
  in
  match khouse with
    None -> print_string "Graph is undefined\n"
  | Some khouse ->
     print_string "Extensions of |_ into Khouse:\n" ;
     print_string (KappaShape.Cat.to_string (KappaShape.Cat.extension_class (KappaShape.Cat.create kl khouse))) ;
     print_newline() ;print_newline() ;
     print_string "Gluings of |_ into Khouse:\n" ;
     print_string (KappaShape.string_of_gluings (KappaShape.Cat.gluings kl khouse)) ;
     print_newline ()
	   

let test() =
  let two =
    match
      SimpleShape.draw [([0],[1]);([1],[2])] SimpleShape.Graph.empty
    with Some g -> g | None -> failwith "Empty"
  in
  let three =
    match
      SimpleShape.draw
	[
	  ([0],[1]);([1],[2]);([0],[3])
	] SimpleShape.Graph.empty with Some g -> g | None -> failwith "Empty"
  in
  let arrows = SimpleShape.Cat.create two three in
  print_string "Extensions of two edges into a three:\n" ;
  print_string (SimpleShape.Cat.to_string (SimpleShape.Cat.extension_class arrows)) ;
  print_newline () ;
  print_string "Gluings of two edges into three:\n" ;
  print_string (SimpleShape.string_of_gluings (SimpleShape.Cat.gluings two three)) ;
  print_newline () ;
  print_string "Renaming three:\n" ;
  print_string (SimpleShape.Graph.to_string (SimpleShape.copy three)) ;
  print_newline()
  
	       
