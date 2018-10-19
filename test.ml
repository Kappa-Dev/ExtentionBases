open Lib.Util

module Simple = Interactive.SPrompt
module Degree = Interactive.DPrompt
module Kappa = Interactive.KPrompt

type mode = SimpleT | Interactive
type shape = Simple | Degree | Kappa

let simple_tests shape = match shape with
  | Simple -> Simple.simple_tests ()
  | Degree -> Degree.simple_tests ()
  | Kappa -> Kappa.simple_tests ()

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
    | Simple -> Simple.interactive ()
    | Degree -> Degree.interactive ()
    | Kappa -> Kappa.interactive ()
  with Interactive.Change_shape s ->
    let shape = match shape_matcher s with
      | Some shape -> shape
      | None -> ask_shape ()
    in interactive (Some shape)

let load shape file = (match shape with
  | Some Simple -> ignore (Simple.process_command Simple.empty (Parser.Load file))
  | Some Degree -> ignore (Degree.process_command Degree.empty (Parser.Load file))
  | Some Kappa -> ignore (Kappa.process_command Kappa.empty (Parser.Load file))
  | _ -> failwith "Impossible"); log ""

let test shape debug mode =
  if debug then debug_mode () else ();
  match mode with
  | SimpleT -> simple_tests shape
  | Interactive -> interactive (Some shape)

let () =
  ignore (LNoise.history_load histfile);
  if Array.length Sys.argv > 1 then
    let file = Sys.argv.(1) in
    Kappa.bench file
  else
    let shape = Kappa in
    let debug = false
    in
    let mode = Interactive
    in test shape debug mode
