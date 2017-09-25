module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Cat.Graph
    module Hom = Cat.Hom

    module Model = Model.Make (Node)
    module EB = Basis.Make (Node)

    open Lib.Util

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
      debug_mode () ;

      if db() then Printexc.record_backtrace true ;
      let one = graph_of_library "one" in
      let house = graph_of_library "house" in
      let dsquare = graph_of_library "dsquare" in
      let square = graph_of_library "square" in

      let model = Model.add_rule "one->house" (one,house) Model.empty in
      let model = Model.add_rule "house->dsquare" (house,dsquare) model in
      let model = Model.add_rule "square->dsquare" (square,dsquare) model in
      let model = Model.add_rule "house->one" (house,one) model in

      let model = Lib.StringMap.fold
		    (fun name _ model ->
		     Model.add_obs name (graph_of_library name) model
		    ) Node.library model
      in
      let nw,pw = Model.witnesses_of_rule (house,dsquare) model in
      let neg_ext_base = List.fold_left
                           (fun ext_base (id_obs,tile) ->
                             EB.insert id_obs tile ext_base
                           ) (EB.empty 1) nw
      in
      let pos_ext_base = List.fold_left
                           (fun ext_base (id_obs,tile) ->
                             EB.insert id_obs tile ext_base
                           ) (EB.empty 1) pw
      in
      let d = open_out "neg_base.dot" in
      let d' = open_out "pos_base.dot" in
      Printf.fprintf d "%s\n" (EB.to_dot neg_ext_base) ;
      Printf.fprintf d' "%s\n" (EB.to_dot pos_ext_base) ;
      close_out d ;
      close_out d'
  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode)
module DegreeShape = Make (Node.DegreeNode)
