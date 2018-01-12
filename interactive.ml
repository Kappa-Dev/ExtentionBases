exception Change_shape of string

module type InteractiveType =
  sig
    type t
    val empty : t
    val simple_tests : unit -> unit
    val interactive : unit -> unit
    val process_command : t -> Parser.command -> t
  end

module Make (Node:Node.NodeType) =
  (struct
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

type t = {model : Model.t ; show_positive : bool ; eb : (EB.t * EB.t) option ; rule : (string * string) option}
let empty = {model = Model.empty ; show_positive = true ; eb = None; rule = None}

let output env =
  if db() then flush stdout ;
  match env.eb with
    None -> ()
  | Some (pb,nb) ->
     let eb = if env.show_positive then pb else nb
     in
     let d = open_out "web_eb.dot" in
     Printf.fprintf d "%s\n%s"
       (EB.to_dot ~show_conflict:false
          env.model.Model.dict eb)
       (EB.to_dot_content eb) ;
     close_out d

let build_base ?obs_name env =
  match env.rule with
    None -> env
   | Some (l,r) ->
      let (lg,rg) = graph_of_library l, graph_of_library r in
      let nw,pw =
        match obs_name with
          None -> Model.witnesses_of_rule (lg,rg) env.model
        | Some o ->
           let obs_id = (Lib.Dict.to_id o env.model.Model.dict)
           in
           Model.witnesses_of_rule ~obs:obs_id (lg,rg) env.model
      in
      let eb_pos,eb_neg =
        match env.eb with
          None ->
          let get_seed = function
              (id_obs,tile)::_ -> Cat.left_of_tile tile
            | [] -> Graph.empty
          in
          (EB.empty (get_seed pw) , EB.empty (get_seed nw))
        | Some basis -> basis
      in
      let pos_ext_base =
        List.fold_left
          (fun ext_base (id_obs,tile) ->
            match Cat.upper_bound tile with
              None -> failwith "no witness"
            | Some (to_w,from_o) ->
               if db() then
                 Printf.printf "Inserting witness of observable '%s': %s\n"
                   (Lib.Dict.to_name id_obs env.model.Model.dict)
                   (Cat.string_of_cospan (to_w,from_o)) ; flush stdout ;
               EB.insert to_w from_o id_obs ext_base
          ) eb_pos pw
      in
      let neg_ext_base =
        List.fold_left
          (fun ext_base (id_obs,tile) ->
            match Cat.upper_bound tile with
              None -> failwith "no witness"
            | Some (to_w,from_o) ->
               if db() then
                 Printf.printf "Inserting witness of observable '%s': %s\n"
                   (Lib.Dict.to_name id_obs env.model.Model.dict)
                   (Cat.string_of_cospan (to_w,from_o)) ; flush stdout ;
               EB.insert to_w from_o id_obs ext_base
          ) eb_neg nw
      in
      {env with eb = Some (pos_ext_base,neg_ext_base)}

let rec process_command env = function
  | Parser.Mode s ->
     log "Changing mode. Current model has been erased.";
     raise (Change_shape s)
  | Parser.Debug ->
     begin
       debug_mode () ;
       Printexc.record_backtrace (db());
       env
     end
  | Parser.List ->
     log ("Observables:\n") ;
     log (String.concat "\n" (proj_left (Model.list env.model))) ;
     log ("Rules:\n") ;
     log (String.concat "\n" (proj_right (Model.list env.model))) ;
     env
  | Parser.Build (l,r) ->
     (try
        log (Printf.sprintf "Generating extension basis for rule %s -> %s" l r);
        let env = {env with rule = Some (l,r)} in
        let env = build_base env in
        output env ;
        env
      with Not_found ->
        log "Unrecognized rule shapes" ;
        env
     )
  | Parser.Add v ->
     if Lib.StringMap.mem v Node.library then
       let graph = graph_of_library v in
       let model = Model.add_obs v graph env.model in
       match env.eb with
         None -> {env with model = model}
       | Some _ ->
          let env = build_base ~obs_name:v {env with model = model}
          in output env ; env
     else
       begin
         log "Unrecognized shape" ;
         env
       end
  | Parser.Output positive -> let env = {env with show_positive = positive} in output env ; env
  | Parser.Add_named (lst,v) ->
     let edges = Node.tn lst in
     let graph = draw edges Graph.empty in
     let env = {env with model = Model.add_obs v graph env.model} in
     let env = build_base ~obs_name:v env in
     output env ;
     env
  | Parser.Exit -> log "exiting" ; exit 0
  | Parser.Reset -> empty
  | Parser.Shell (inst,args) ->
     let pid = Unix.fork () in
     if pid = 0 then Unix.execvp inst args
     else
       let _ = Unix.wait () in
       env
  | Parser.Load file ->
     let run_line acc lineno line = match Parser.parse line with
       | Result.Ok command -> (match command with
                               | Parser.Mode _ ->
                                  log (Printf.sprintf "Ignoring mode command at line %d" lineno);
                                  Some acc
                               | _ ->
                                  Some (process_command acc command))
       | Result.Error _ ->
          log (Printf.sprintf "Parse error at line %d" lineno);
          None
     in
     each_line file run_line env

  let interactive debug =
    let rec session env =
    (match (LNoise.linenoise "> ") with
     | None ->
       log "Attempting to save session history";
       ignore (LNoise.history_save histfile);
       exit 0
     | Some line ->
       ignore (LNoise.history_add line);
       (match Parser.parse line with
        | Result.Ok command ->
           (try session (process_command env command) with exn -> log (Printexc.to_string exn) ; session env)
        | Result.Error s -> log ("Parse error "^s); session env);
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
    session empty
  end:InteractiveType)

module SPrompt = Make (Node.SimpleNode)
module KPrompt = Make (Node.KappaNode)
module DPrompt = Make (Node.DegreeNode)
