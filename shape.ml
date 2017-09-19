module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Cat.Graph
    module Hom = Cat.Hom

    module Model = Model.Make (Node)
    module EB = Basis.Make (Node)

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

      let model = Model.add_rule "house->dsquare" (house,dsquare) model in

      let model = Lib.StringMap.fold
		    (fun name _ model ->
		     Model.add_obs name (graph_of_library name) model
		    ) Node.library model
      in
      let nw,pw = Model.witnesses_of_rule (house,dsquare) model in
      (*let pos_ext_base = Basis.create (house,dsquare) pw in*)
      ()

      (*
      Lib.IntMap.fold
        (fun r_id witMap ext_basis ->
         let r = Model.get_rule r_id model in
         let eff = Model.effect_of_rule r in
         let init_eb = function
             None -> None
           | Some emb -> Some EB.init emb.src 0 false true
         in
         let pos_ext_b = init_eb eff.Model.pos in
         let neg_ext_b = init_eb eff.Model.neg in
         match pos_ext_b with
           None -> None
         | Some ext_base ->
            let witnesses = Lib.IntMap.find r_id pw in
            let ext_base =
              Lib.IntMap.fold
                (fun obs_id cospans ext_base ->
                 ...
                ) witnesses ext_base
            in
            Lib.IntMap.add r_id ext_base ext_basis
        ) nw Lib.IntMap.empty
       *)
  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode)
module DegreeShape = Make (Node.DegreeNode)
