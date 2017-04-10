
module type NodeType =
  sig
    type t 
    val id : t -> int
    val arity : int
    val prop : (int -> int list) array
    val get_prop : t -> int -> int
    val fold_prop : (int -> int -> 'a -> 'a) -> t -> 'a -> 'a
    val compare : t -> t -> int
    val create : int list -> t
    val to_string : t -> string
    val coh : (t*t) list -> (t*t) -> bool
    val rename : int -> t -> t
    val library : (t*t) list Lib.StringMap.t
  end


module SimpleNode =
  (struct
      type t = int
      let arity = 0
      let rename i u = i
			 
      let id u = u
      let prop = [||]
		   
      let get_prop _ i = 
	try
	  prop.(i) 
	with
	  Invalid_argument _ -> raise Not_found
				      
      let fold_prop _ _ cont = cont
				 
      let compare = Pervasives.compare
		      
      let create l = 
	match l with 
	  [i] -> i
	| _ -> failwith "Cannot parse node"
			
      			
      let to_string = string_of_int
			
      let coh _ _ = true

      let library =
	let void = [] in
	let house =
	  [
	    ([0],[1]) ;
	    ([1],[2]) ;
	    ([2],[3]) ;
	    ([3],[0]) ;
	    ([3],[4]) ;
	    ([2],[4])
	  ]
	in
	let square =
	  [
	    ([10],[11]) ;
	    ([11],[12]) ;
	    ([12],[13]) ;
	    ([13],[10]) ;
	  ]
	in
	let triangle =
	  [
	    ([20],[21]) ;
	    ([21],[22]) ;
	    ([20],[22])
	  ]
	in
	let one = [([100],[200])] in
	let two = [([0],[1]);([1],[2])] 
	in
	let tn = List.map (fun (l,l') -> (create l,create l')) in
	let lib = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	let lib = Lib.StringMap.add "one" (tn one) lib in
	let lib = Lib.StringMap.add "two" (tn two) lib in
	Lib.StringMap.add "house" (tn house)
			  (Lib.StringMap.add "square" (tn square)
					     (Lib.StringMap.add "triangle" (tn triangle) lib))
			  
			  end:NodeType)
    
module KappaNode =
  (struct
      type t = {ag_id : int ; port_id : int ; label : int}
		 
      let arity = 2
      let prop = [| (fun port_id -> [port_id]) ; (fun label -> [label]) |]
		   
      let id u = u.ag_id
		   
      let rename i u = {u with ag_id = i}
			 
      let get_prop u = function
	| 0 -> u.port_id
	| 1 -> u.label
	| _ -> raise Not_found

      let fold_prop f u cont = f 1 u.label (f 0 u.port_id cont)
				 
      let compare u v = Pervasives.compare (u.ag_id,u.port_id) (v.ag_id,v.port_id)
					   
      let create l = 
	match l with 
	  [i;p;l] -> {ag_id = i ; port_id = p ; label = l}
	| _ -> failwith "Cannot parse node"
			
      			
      let to_string u =
	(string_of_int u.ag_id)^"."^(string_of_int (u.port_id))

      let coh edges (w,x) =
	let ok u v =
	  if u.ag_id = v.ag_id then ((u.port_id != v.port_id) && (u.label = v.label))
	  else true
	in
	List.for_all
	  (fun (u,v) ->
	   ok u x && ok v x && ok u w && ok v w && ok w x
	  ) edges

      let library =
	let void = [] in
	let house =
	  [
	    ([0;0;0],[1;0;0]) ;
	    ([1;1;0],[2;1;0]) ;
	    ([2;0;0],[3;0;0]) ;
	    ([3;1;0],[0;1;0]) ;
	    ([3;2;0],[4;0;0]) ;
	    ([4;1;0]),[2;2;0]
	  ]
	in
	let square =
	  [
	    ([10;0;0],[11;0;0]) ;
	    ([11;1;0],[12;1;0]) ;
	    ([12;0;0],[13;0;0]) ;
	    ([13;1;0],[10;1;0])
	  ]
	in
	let triangle =
	  [
	    ([20;0;0],[21;0;0]) ;
	    ([20;2;0],[22;0;0]) ;
	    ([22;1;0],[21;2;0])
	  ]
	in
	let one = [([300;0;0],[301;0;0])] in 
	let tn = List.map (fun (l,l') -> (create l,create l')) 
	in
	let lib = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	let lib = Lib.StringMap.add "house" (tn house) lib
	in
	let lib = Lib.StringMap.add "square" (tn square) lib
	in
	let lib = Lib.StringMap.add "one" (tn one) lib in
	Lib.StringMap.add "triangle" (tn triangle) lib

    end:NodeType)

module DegreeNode =
  (struct
      type t = {id : int ; max_degree : int}
		 
      let arity = 1
      let prop = [|fun i -> [i]|]
		   
      let id u = u.id
		   
      let rename i u = {u with id = i}
			 
      let get_prop = fun u i -> if i = 0 then u.max_degree else raise Not_found

      let fold_prop f u cont = f 0 u.max_degree cont
				 
      let compare u v = Pervasives.compare u.id v.id
					   
      let create l = 
	match l with 
	  [i;d] -> {id = i ; max_degree = d}
	| _ -> failwith "Cannot parse node"
			
      let to_string u =
	"["^(string_of_int u.id)^";"^(string_of_int (u.max_degree))^"]"

      let coh edges (w,x) =
	let dw,dx =
	  List.fold_left
	    (fun (dw,dx) (u,v) ->
	     let dw = if (u.id = w.id) || (v.id=w.id) then dw+1 else dw in
	     let dx = if (u.id = x.id) || (v.id=x.id) then dx+1 else dx in
	     (dw,dx)
	    ) (1,1) edges
	in
	(dw <= w.max_degree) && (dx <= x.max_degree)

      let library =
	let void = [] in
	let house =
	  [
	    ([0;2],[1;2]) ;
	    ([1;2],[2;3]) ;
	    ([2;3],[3;3]) ;
	    ([3;3],[0;2]) ;
	    ([3;3],[4;2]) ;
	    ([2;3],[4;2])
	  ]
	in
	let square =
	  [
	    ([10;2],[11;2]) ;
	    ([11;2],[12;3]) ;
	    ([12;3],[13;3]) ;
	    ([13;3],[10;2]) ;
	  ]
	in
	let triangle =
	  [
	    ([20;3],[21;3]) ;
	    ([21;3],[22;2]) ;
	    ([20;3],[22;2])
	  ]
	in
	let one = [([100;3],[200;3])]
	in 
	let tn = List.map (fun (l,l') -> (create l,create l')) in
	let lib0 = Lib.StringMap.add "empty" (tn void) Lib.StringMap.empty in
	Lib.StringMap.add "one" (tn one)
			  (Lib.StringMap.add "house" (tn house)
					     (Lib.StringMap.add "square" (tn square)
								(Lib.StringMap.add "triangle" (tn triangle) lib0)))
			  
end:NodeType)
