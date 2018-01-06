open Lib.Util

type mode = SimpleT | Complete | Interactive
type shape = Simple | Degree | Kappa

let simple_tests shape = match shape with
  | Simple -> Shape.SimpleShape.simple_tests ()
  | Degree -> Shape.DegreeShape.simple_tests ()
  | Kappa -> Shape.KappaShape.simple_tests ()

let generate_tests shape = match shape with
  | Simple -> Shape.SimpleShape.generate_tests ()
  | Degree -> Shape.DegreeShape.generate_tests ()
  | Kappa -> Shape.KappaShape.generate_tests ()

let shape_matcher = function
  | "simple" -> Some Simple
  | "degree" -> Some Degree
  | _ -> Some Kappa

let ask_shape () = ask_until "[kappa|simple|degree] (kappa) " shape_matcher

let rec interactive maybe_shape =
  let shape = match maybe_shape with
    | Some shape -> shape
    | None -> ask_shape () in
  log "entering interactive extension base builder."; log "" ;
  try
    match shape with 
    | Simple -> Shape.SimpleShape.interactive ()
    | Degree -> Shape.DegreeShape.interactive ()
    | Kappa -> Shape.KappaShape.interactive ()
  with Shape.Change_shape s -> 
    let shape = match shape_matcher s with
      | Some shape -> shape
      | None -> ask_shape ()
    in interactive (Some shape)

let test shape debug mode = 
  if debug then debug_mode () else ();
  match mode with
  | SimpleT -> simple_tests shape
  | Complete -> generate_tests shape
  | Interactive -> interactive (Some shape)

let () =
  ignore (LNoise.history_load histfile);
  if Array.length Sys.argv > 1 then
    (if Sys.argv.(1) = "auto" then
       test Kappa false Complete
     else if Sys.argv.(1) = "interactive" then
       interactive None 
    )
  else
    let shape = ask_shape () in
    let debug = ask_until "Debug mode y/n (n)? > "
        (function "y" -> Some true
                | _ -> Some false
        )
    in
    let mode = ask_until "Interactive, Simple or complete test (i/s/c)? (i) > "
        (function "s" -> Some SimpleT
                | "c" -> Some Complete
                | _ -> Some Interactive
        )
    in test shape debug mode
