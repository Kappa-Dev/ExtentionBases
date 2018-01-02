open Lib.Util

let test input debug mode =
  match input with
    0 ->
    begin
      if mode=1 then
        Shape.KappaShape.simple_tests debug
      else
        if mode=2 then
          Shape.KappaShape.generate_tests debug
        else
          Shape.KappaShape.interactive_tests debug ;
      print_string "done\n"
    end
  | 1 ->
     begin
       if mode=1 then
         Shape.SimpleShape.simple_tests debug
       else
         if mode=2 then
           Shape.SimpleShape.generate_tests debug
         else
           Shape.SimpleShape.interactive_tests debug ;
       print_string "done\n" ;
     end
  | 2 ->
     begin
       if mode=1 then
         Shape.DegreeShape.simple_tests debug
       else
         if mode=2 then
           Shape.DegreeShape.generate_tests debug
         else
           Shape.DegreeShape.interactive_tests debug ;
       print_string "done\n" ;
     end
  | _ -> failwith "Invalid argument"


let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "auto" then
    test 0 false 2
  else
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
    let mode = ask_until "Interactive, Simple or complete test (i/s/c)? (i)\n"
                         (function "s" -> (true,1)
                                 | "c" -> (true,2)
                                 | "i" -> (true,0)
                                 | _ -> (true,0)
                         )
    in test input debug mode
