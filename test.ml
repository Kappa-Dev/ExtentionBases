let test =
  print_string "[kappa|simple|degree]\n";
  let input = read_line() in
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
