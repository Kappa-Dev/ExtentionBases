open Lib.Util

let test =
  let input = ask_until "[kappa|simple|degree]\n" (function "kappa"|"simple"|"degree" -> true | _ -> false)
  in
  let debug = ask_until "Debug mode y/n? \n" (function "y"|"n" -> true | _ -> false)
  in
  let debug =
    match debug with
      "y" -> true
      | _ -> false
  in
  match input with
    "kappa" ->
    begin
      Shape.KappaShape.generate_tests debug ;
      print_string "done\n"
    end
  | "simple" ->
     begin
       Shape.SimpleShape.generate_tests debug ;
       print_string "done\n"
     end
  | "degree" ->
     begin
       Shape.DegreeShape.generate_tests debug ;
       print_string "done\n"
     end
  | _ -> failwith "Invalid argument"
