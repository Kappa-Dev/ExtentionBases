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
  let test = ask_until "Interactive, Simple or complete test (i/s/c)? (i)\n"
                       (function "s" -> (true,1)
                               | "c" -> (true,2)
                               | "i" -> (true,0)
                               | _ -> (true,0)
                       )
  in
  match input with
    0 ->
    begin
      if test=1 then
        Shape.KappaShape.simple_tests debug
      else
        if test=2 then
          Shape.KappaShape.generate_tests debug
        else
          Shape.KappaShape.interactive_tests debug ;
      print_string "done\n"
    end
  | 1 ->
     begin
       if test=1 then
         Shape.SimpleShape.simple_tests debug
       else
         if test=2 then
           Shape.SimpleShape.generate_tests debug
         else
           Shape.SimpleShape.interactive_tests debug ;
       print_string "done\n" ;
     end
  | 2 ->
     begin
       if test=1 then
         Shape.DegreeShape.simple_tests debug
       else
         if test=2 then
           Shape.DegreeShape.generate_tests debug
         else
           Shape.DegreeShape.interactive_tests debug ;
       print_string "done\n" ;
     end
  | _ -> failwith "Invalid argument"
