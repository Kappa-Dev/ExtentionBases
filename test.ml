open Lib.Util

let test =
  let input = ask_until "[kappa|simple|degree] (kappa)\n"
              (function "kappa" -> (true,0)
                      | "simple" -> (true,1)
                      | "degree" -> (true,2)
                      | _ -> (true,0)
              )
  in
  let debug = ask_until "Debug mode y/n (n)? \n"
                        (function "y" -> (true,true)
                                | "n" -> (true,false)
                                | _ -> (true,false)
                        )
  in
  let simple_test = ask_until "Simple or complete test (s/c)? (s)\n"
                       (function "s" -> (true,true)
                               | "c" -> (true,false)
                               | _ -> (true,true)
                       )
  in
  match input with
    0 ->
    begin
      if simple_test then
        Shape.KappaShape.simple_tests debug
      else
        Shape.KappaShape.generate_tests debug ;
      print_string "done\n"
    end
  | 1 ->
     begin
      if simple_test then
        Shape.SimpleShape.simple_tests debug
      else
        Shape.SimpleShape.generate_tests debug ;
       print_string "done\n"
     end
  | 2 ->
     begin
      if simple_test then
        Shape.DegreeShape.simple_tests debug
      else
        Shape.DegreeShape.generate_tests debug ;
       print_string "done\n"
     end
  | _ -> failwith "Invalid argument"
