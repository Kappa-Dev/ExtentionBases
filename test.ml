open Lib.Util

let test =
  let input = ask_until "[kappa|simple|degree]\n" (function "kappa"|"simple"|"degree" -> true | _ -> false)
  in
  match input with
    "kappa" ->
    begin
      print_string "***** Kappa nodes ***** \n" ;
      Shape.KappaShape.generate_tests() ;
    end
  | "simple" ->
     begin
       print_string "***** Simple nodes *****\n" ;
       Shape.SimpleShape.generate_tests()
     end
  | "degree" ->
     begin
       print_string "***** Degree nodes ***** \n" ;
       Shape.DegreeShape.generate_tests()
     end
  | _ -> failwith "Invalid argument"
