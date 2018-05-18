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

    let (=~=>) g h = Cat.flatten (Cat.extension_class (g => h))

    let simple_tests_old () =
      let one = graph_of_library "one" in
      let w1 = graph_of_library "square" in
      let w2 = graph_of_library "triangle" in
      let o2_to_o8 = one =~=> w1 in
      let o2_to_w = one =~=> w2 in
      let sharings =
        List.fold_left (fun sharings o2_o8 ->
            List.fold_left (fun sharings o2_w ->
                (Cat.share o2_o8 o2_w)::sharings
              ) sharings o2_to_w
          ) [] o2_to_o8
      in
      let ext_base = EB.of_sharings sharings in
      let d = open_out "web_eb.dot" in
      let str = EB.to_dot_content ext_base in
      Printf.fprintf d "%s\n%s" (EB.to_dot false Lib.Dict.empty ext_base) str ;
      close_out d


    let simple_tests () =
      let dsquare = graph_of_library "dsquare"
      in
      let house = graph_of_library "house"
      in
      let one = graph_of_library "one" in
      let o2_to_o8 = one =~=> dsquare in
      let o2_to_w = one =~=> house in
      List.iter (fun o2_o8 ->
          List.iter (fun o2_w ->
              let inf_to_mp,mp_to_base,mp_to_w = Cat.share_new o2_o8 o2_w in
              Printf.printf "%s \n %s \n" (Cat.string_of_arrows inf_to_mp) (Cat.string_of_span (mp_to_base,mp_to_w))
            ) o2_to_w
        ) o2_to_o8


    type t = {model : Model.t ;
              show_positive : bool ;
              eb : (EB.t * EB.t) option ;
              rule : (string * string) option
             }
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
           (EB.to_dot true env.model.Model.dict eb)
           (EB.to_dot_content eb) ;
         close_out d

    let build_base ?obs_name max_step env =
      match env.rule with
        None -> env
      | Some (l,r) ->
         let lg =
           try graph_of_library l
           with Not_found ->
             Model.get_obs (Lib.Dict.to_id l env.model.Model.dict) env.model
         in
         let rg = try graph_of_library r
                  with
                    Not_found ->
                    Model.get_obs (Lib.Dict.to_id r env.model.Model.dict) env.model
         in
         print_endline "Generating witnesses..." ;
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
                  (id_obs,tile)::_ ->
                  (
                    let g = Cat.left_of_tile tile in
                    let () = Printf.printf "tile is %s\n" (Cat.string_of_tile tile)
                    in
                    g
                  )
                | [] -> Graph.empty
              in
              (EB.empty (get_seed pw) , EB.empty (get_seed nw))
           | Some basis -> basis
         in
         print_endline "Computing sharing..." ;
         let pos_ext_base =
           try
             List.fold_left
               (fun ext_base (id_obs,tile) ->
                 match Cat.upper_bound tile with
                   None -> failwith "no witness"
                 | Some (to_w,from_o) ->
                    if db() then
                      Printf.printf "Inserting witness of observable '%s': %s\n"
                        (Lib.Dict.to_name id_obs env.model.Model.dict)
                        (Cat.string_of_cospan (to_w,from_o)) ; flush stdout ;
                    EB.insert ~max_step:max_step to_w from_o id_obs ext_base
               ) eb_pos pw
           with EB.Invariant_failure (str,ext_base) -> print_endline (red str) ; ext_base
         in
         let neg_ext_base =
           try
           List.fold_left
             (fun ext_base (id_obs,tile) ->
               match Cat.upper_bound tile with
                 None -> failwith "no witness"
               | Some (to_w,from_o) ->
                  if db() then
                    Printf.printf "Inserting witness of observable '%s': %s\n"
                      (Lib.Dict.to_name id_obs env.model.Model.dict)
                      (Cat.string_of_cospan (to_w,from_o)) ; flush stdout ;
                  EB.insert ~max_step:max_step to_w from_o id_obs ext_base
             ) eb_neg nw
           with EB.Invariant_failure (str,ext_base) -> print_endline (red str) ; ext_base
         in
         {env with eb = Some (pos_ext_base,neg_ext_base)}

    let rec process_command env = function
      | Parser.Mode s ->
         log "Changing mode. Current model has been erased.";
         raise (Change_shape s)
      | Parser.Debug ->
         begin
           debug_mode () ;
           env
         end
      | Parser.List ->
         log ("Observables:\n") ;
         log (String.concat "\n" (proj_left (Model.list env.model))) ;
         log ("Rules:\n") ;
         log (String.concat "\n" (proj_right (Model.list env.model))) ;
         env
      | Parser.Build (l,r,mx) ->
         log (Printf.sprintf "Generating extension basis for rule %s -> %s" l r);
         let env = {env with rule = Some (l,r) ; eb = None} in
         let env = build_base mx env in
         output env ;
         env
      | Parser.Add v ->
         if Lib.StringMap.mem v Node.library then
           let graph = graph_of_library v in
           let model = Model.add_obs v graph env.model in
           match env.eb with
             None -> {env with model = model}
           | Some _ ->
              let env = build_base ~obs_name:v None {env with model = model}
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
         let env = build_base ~obs_name:v None env in
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
        let _ = Unix.waitpid [Unix.WNOHANG] in
        let prompt () = if db() then "db> " else "> " in
        (match (LNoise.linenoise (prompt debug)) with
         | None ->
            log "Attempting to save session history";
            ignore (LNoise.history_save histfile);
            exit 0
         | Some line ->
            ignore (LNoise.history_add line);
            (match Parser.parse line with
             | Result.Ok command ->
                if db() then session (process_command env command)
                else
                  (try session (process_command env command) with exn -> if db() then raise exn else log (Printexc.to_string exn) ; session env)
             | Result.Error s -> log ("Parse error "^s); session env);
        )
      in
      session empty
  end:InteractiveType)

module SPrompt = Make (Node.SimpleNode)
module KPrompt = Make (Node.KappaNode)
module DPrompt = Make (Node.DegreeNode)
