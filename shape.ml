exception Change_shape of string

module Make (Node:Node.NodeType) =
  struct
    module Cat = Cat.Make (Node)
    module Graph = Graph.Make (Node)
    module Hom = Homomorphism.Make (Node)

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

    let (=>) = Cat.(=>)
    let (|>) = Cat.(|>)

  let simple_tests () =
      let one = graph_of_library "one" in
      let square = graph_of_library "square" in
      let open_square = graph_of_library "osquare" in
      List.iter (fun g -> if Graph.is_connex g then print_string "true\n" else print_string "false\n")
                [one;square;open_square; Graph.sum one one] ;
      let f_list = Cat.flatten (Cat.extension_class (one => open_square)) in
      let g_list = Cat.flatten (Cat.extension_class (one => square)) in
      let f = List.hd (List.filter (fun f -> Cat.is_identity f) f_list) in
      let g = List.hd (List.filter (fun f -> Cat.is_identity f) g_list) in
      let sharing = Cat.share f g in
      List.iter
        (fun (sh,tile) ->
          Printf.printf "(square <-- one --> osquare) %s:\n" (Cat.string_of_arrows sh) ;
          print_string (Cat.string_of_tile tile) ;
          print_newline() ;
        ) sharing
    (*print_string "square |> one one\n" ;
      List.iter (fun tile ->
		 let emb = Cat.arrows_of_tile tile in
		 Printf.printf "%s:\n %s\n" (Cat.string_of_arrows emb) (Cat.string_of_tile tile)
		) (square |> (Graph.sum one one))
     *)

let process_result model = function
  | Parser.Mode s ->
    log "Changing mode. Current model has been erased.";
    raise (Change_shape s)
  | Parser.Debug ->
    begin
      debug_mode () ;
      Printexc.record_backtrace (db());
      model
    end
  | Parser.List ->
     log (String.concat "\n" (Model.list model)) ;
     model
  | Parser.Build (l,r) ->
    (try
       let (lg,rg) = graph_of_library l, graph_of_library r in
       let nw,pw = Model.witnesses_of_rule (lg,rg) model in
       let get_seed = function
           (id_obs,tile)::_ -> Cat.left_of_tile tile
         | [] -> Graph.empty
       in
       let pos_ext_base =
         List.fold_left
           (fun ext_base (id_obs,tile) ->
              match Cat.upper_bound tile with
                None -> failwith "no witness"
              | Some (to_w,from_o) ->
                if db() then
                  Printf.printf "Inserting witness of observable '%s': %s\n"
                    (Lib.Dict.to_name id_obs model.Model.dict)
                    (Cat.string_of_cospan (to_w,from_o)) ; flush stdout ;
                EB.insert to_w from_o id_obs ext_base
           ) (EB.empty (get_seed pw)) pw
       in
       let d2 = open_out "pos_web.dot" in
       Printf.fprintf d2 "%s\n%s"
         (EB.to_dot ~show_conflict:false
            model.Model.dict pos_ext_base)
         (EB.to_dot_content pos_ext_base) ;
       close_out d2 ;
       model
     with Not_found ->
       log "Unrecognized rule shapes" ;
       model
    )
  | Parser.Add v ->
    if Lib.StringMap.mem v Node.library then
      let graph = graph_of_library v in
      Model.add_obs v graph model
    else
      begin
        log "Unrecognized shape" ;
        model
      end
  | Parser.Add_named (lst,v) ->
    let edges = Node.tn lst in
    let graph = draw edges Graph.empty in
    Model.add_obs v graph model
  | Parser.Load f ->
     log (Printf.sprintf "<Attempting to load file %s>" f) ;
     model

  let interactive debug =
    let rec session model =
    (match (LNoise.linenoise "> ") with
     | None ->
       log "Attempting to save session history";
       ignore (LNoise.history_save histfile);
       exit 0
     | Some v ->
       ignore (LNoise.history_add v);
       (match Parser.parse v with
        | Result.Ok result ->
          session (process_result model result)
        | Error _ -> log "Parse error."; session model);
    )
    in
    (*let pid = Unix.fork () in
    if pid = 0 then (*child process*)
      try
        Unix.execvp "node" [|"web/server.js"|]
      with
        exn -> log (Printexc.to_string exn)
    else (*parent process*)
      session Model.empty
     *)
    session Model.empty
  end

module SimpleShape = Make (Node.SimpleNode)
module KappaShape = Make (Node.KappaNode)
module DegreeShape = Make (Node.DegreeNode)
