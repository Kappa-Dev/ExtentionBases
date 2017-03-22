open IntStruct
       
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
    val coh : (t * t) -> (t * t) -> bool
    val rename : int -> t -> t
    exception Incoherent
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
			
      exception Incoherent
		  
      let to_string = string_of_int
			
      let coh _ _ = true
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
			
      exception Incoherent
		  
      let to_string u = "["^(string_of_int u.ag_id)^";"^(string_of_int (u.port_id))^";"^(string_of_int (u.label))^"]"

      let coh (u,v) (w,x) =
	let ok u v = if u.ag_id = v.ag_id then (u.port_id != v.port_id) && (u.label = v.label) else true in
	ok u v && ok u x && ok v w && ok v x && ok u v && ok w x
				       			     
    end:NodeType)
