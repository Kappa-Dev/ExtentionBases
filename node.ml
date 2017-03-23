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
    val coh : (t*t) list -> (t*t) -> bool
    val rename : int -> t -> t
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
	"["^(string_of_int u.ag_id)^";"^(string_of_int (u.port_id))^";"^(string_of_int (u.label))^"]"

      let coh edges (w,x) =
	let ok u v =
	  if u.ag_id = v.ag_id then ((u.port_id != v.port_id) && (u.label = v.label))
	  else true
	in
	List.for_all
	  (fun (u,v) ->
	   ok u x && ok v x && ok u w && ok v w && ok w x
	  ) edges
	  
    end:NodeType)

module DegreeNode =
  (struct
      type t = {id : int ; max_degree : int}
      
      let arity = 0
      let prop = [||]
		   
      let id u = u.id
		   
      let rename i u = {u with id = i}
		    
      let get_prop _ = raise Not_found

      let fold_prop _ _ cont = cont
			    
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
	   let dw = if (u = w) || (v=w) then dw+1 else dw in
	   let dx = if (u = x) || (v=x) then dx+1 else dx in
	   (dw,dx)
	  ) (1,1) edges
	in
	(dw <= w.max_degree) && (dx <= x.max_degree)  
	  
    end:NodeType)
