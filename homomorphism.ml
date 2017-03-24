module Make (Node:Node.NodeType) =
  struct
    module NodeBij = Bijection.Make (Node)
    module IntBij =
      Bijection.Make (struct type t = int let compare = compare let to_string = string_of_int end)
				   
    exception Not_structure_preserving 
    exception Not_injective 

    type node = Node.t
    type t = {tot : NodeBij.t ; sub : IntBij.t }

    let is_equal hom hom' = NodeBij.is_equal (fun u v -> Node.compare u v = 0) hom.tot hom'.tot
					     
    let is_sub hom hom' =
      try
	NodeBij.fold
	  (fun u v b ->
	   let v' = NodeBij.find u hom'.tot in
	   (compare v v' = 0) && b
	  ) hom.tot true
      with
	Not_found -> false
		       
    let empty =
      {tot = NodeBij.empty ;
       sub = IntBij.empty 
      }
	
	
    let is_empty hom = NodeBij.is_empty hom.tot
    let is_identity hom = IntBij.is_identity hom.sub
					     
    let add_sub u_i v_i hom =
      let bij = IntBij.add u_i v_i hom.sub in
      {hom with sub = bij}
      	
    let add u v hom =
      let () =
	Node.fold_prop (fun i u_i _ ->
			assert (Node.arity > i) ;
			try
			  let v_i = Node.get_prop v i in
			  let f = Node.prop.(i) in
			  if List.mem v_i (f u_i) then () 
			  else raise Not_structure_preserving
			with
			  Not_found -> raise Not_structure_preserving
					     
		       ) u ()
      in
      let u_i,v_i = Node.id u,Node.id v in
      try
	let hom' = add_sub u_i v_i hom
	in
	assert (
	    match (try Some (NodeBij.find u hom.tot) with Not_found -> None) with
	      None -> true
	    | Some v' -> (Node.compare v v') = 0
	  ) ;
	{hom' with tot = NodeBij.add u v hom.tot}
      with
	IntBij.Not_bijective _ -> raise Not_injective

    let find u hom = NodeBij.find u hom.tot
    let cofind u hom = NodeBij.cofind u hom.tot
				  
    let id_image u hom =
      try Some (IntBij.find (Node.id u) hom.sub) with Not_found -> None 

    let fold f hom = NodeBij.fold (fun u v cont -> f u v cont) hom.tot

    let sum hom hom' = fold (fun u v hom_sum -> add u v hom_sum) hom hom'
      			    
    let mem u hom = NodeBij.mem u hom.tot

    let to_string hom =
      if is_identity hom then
	let l = 
	  fold (fun u _ cont ->
		(Node.to_string u)::cont
	       ) hom []
	in
	"Id_{"^(String.concat "," l)^"}"
      else
	let l = 
	  fold (fun u v cont ->
		((Node.to_string u)^"->"^(Node.to_string v))::cont
	       ) hom []
	in
	"["^(String.concat " + " l)^"]"

				      
  end
    
