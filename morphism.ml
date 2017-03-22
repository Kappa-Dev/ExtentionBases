open IntStruct

module type Bijective =
  sig
    type t
    val empty : t
    val is_identity : t -> bool
    val fold : (int -> int -> 'a -> 'a) -> t -> 'a -> 'a
    val mem : int -> t -> bool
    val find : int -> t -> int
    val add : int -> int -> t -> t
    val to_string : t -> string
    val is_equal : t -> t -> bool
    val sum : t -> t -> t
    exception Not_bijective of int * int * t
  end
       
module Bijection =
  (struct
    type t = I of IntSet.t | B of (int IntMap.t) * (int IntMap.t)

    exception Not_bijective of int * int * t
												  
    let empty = I IntSet.empty

    let is_equal bij bij' =
      match (bij,bij') with
	(I s, I s') -> IntSet.equal s s'
      | (I _, B _) | (B _, I _) -> false
      | (B (m,_), B (m',_)) -> IntMap.equal (fun i j -> i=j) m m'
	
    let cardinal = function
	I s -> IntSet.cardinal s
      | B (m,_) -> IntMap.cardinal m

    let is_identity = function
	I _ -> true
      | B _ -> false
      
    let fold f = function
      	I dom -> IntSet.fold (fun i cont -> f i i cont) dom 
      | B (map,_) -> IntMap.fold (fun i j cont -> f i j cont) map
		  
    let mem i = function
	I dom -> IntSet.mem i dom
      | B (m,_) -> IntMap.mem i m

    let comem i = function
	I dom -> IntSet.mem i dom
      | B (_,m) -> IntMap.mem i m

    let find i = function
	I dom -> IntSet.find i dom
      | B (m,_) -> IntMap.find i m

    let cofind i = function
	I dom -> IntSet.find i dom
      | B (_,m) -> IntMap.find i m
        
    let add i j bij =
      let valid = 
	if mem i bij then
	  try
	    j = find i bij
	  with Not_found -> failwith "Invariant violation"
	else
	  not (comem j bij)
      in
      if not valid then raise (Not_bijective (i,j,bij))
      else			 
	match bij with
	  I dom ->
	  begin
	    if i = j then I (IntSet.add i dom)
	    else
	      let map =
		IntSet.fold
		  (fun i map ->
		   IntMap.add i i map
		  ) dom IntMap.empty
	      in
	      B (IntMap.add i j map, IntMap.add j i map)
	  end
	| B (map,comap) -> B (IntMap.add i j map, IntMap.add j i comap)


    let sum bij bij' = fold (fun i j bij_sum -> add i j bij_sum) bij bij'
      
    let to_string = function
	I dom ->
	begin
	  let l =
	    IntSet.fold (fun i cont -> (string_of_int i)::cont) dom []
	  in
	  ("Id_{"^(String.concat "," l)^"}")
	end
      | bij ->
	 "("^(String.concat ","
			    (fold
			       (fun i j l -> ((string_of_int i)^"->"^(string_of_int j))::l
			       ) bij [])
	     )^")"
		 
  end:Bijective)

module type Homomorphic =
  sig
    exception Not_structure_preserving 
    exception Not_injective 
    type t
    type node
    val empty : t
    val is_empty : t -> bool
    val add : node -> node -> t -> t
    val find : node -> t -> node
    val mem : node -> t -> bool
    val fold : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a
    val to_string : t -> string
    val id_image : node -> t -> int option
    val is_equal : t -> t -> bool
    val is_sub : t -> t -> bool
    val is_identity : t -> bool
    val sum : t -> t -> t 
  end
 
module Make_structure_preserving (Node:Node.NodeType) =
  (struct
    module NodeMap = Map.Make (Node)
    exception Not_structure_preserving 
    exception Not_injective 

    type node = Node.t
    type t = {tot : node NodeMap.t ; sub : Bijection.t }

    let is_equal hom hom' = NodeMap.equal (fun u v -> Node.compare u v = 0) hom.tot hom'.tot

					  
    let is_sub hom hom' =
      try
	NodeMap.fold
	  (fun u v b ->
	   let v' = NodeMap.find u hom'.tot in
	   (compare v v' = 0) && b
	  ) hom.tot true
      with
	Not_found -> false
	    
    let empty =
      {tot = NodeMap.empty ;
       sub = Bijection.empty 
      }
  
	
    let is_empty hom = NodeMap.is_empty hom.tot
    let is_identity hom = Bijection.is_identity hom.sub
					
    let add_sub u_i v_i hom =
      let bij = Bijection.add u_i v_i hom.sub in
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
	    match (try Some (NodeMap.find u hom.tot) with Not_found -> None) with
	      None -> true
	    | Some v' -> (Node.compare v v') = 0
	  ) ;
	{hom' with tot = NodeMap.add u v hom.tot}
      with
	Bijection.Not_bijective _ -> raise Not_injective

    let find u hom = NodeMap.find u hom.tot
				  
    let id_image u hom =
      try Some (Bijection.find (Node.id u) hom.sub) with Not_found -> None 

    let fold f hom = NodeMap.fold (fun u v cont -> f u v cont) hom.tot

    let sum hom hom' = fold (fun u v hom_sum -> add u v hom_sum) hom hom'
      				  
    let mem u hom = NodeMap.mem u hom.tot

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

      
  end:Homomorphic with type node = Node.t)
       
