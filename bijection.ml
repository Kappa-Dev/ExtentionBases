module Make (Content:Lib.OrderedType) =
  struct
    module CMap = Map.Make(Content)
    module CSet = Set.Make(Content)

    type t = I of CSet.t | B of ((Content.t CMap.t) * (Content.t CMap.t))

    let domain = function
        I s -> CSet.elements s
      | B (m,_) -> CMap.fold (fun i _ cont -> i::cont) m []

    exception Not_bijective of Content.t * Content.t * t

    let empty = I CSet.empty

    let size = function
        I s -> CSet.cardinal s
      | B (m,_) -> CMap.cardinal m

    let invert = function
        I s -> I s
      | B (m,m') -> B (m',m)

    let identity clist = I (List.fold_left (fun set c -> CSet.add c set) CSet.empty clist)

    let is_equal f bij bij' =
      match (bij,bij') with
	(I s, I s') -> CSet.equal s s'
      | (I _, B _) | (B _, I _) -> false
      | (B (m,_), B (m',_)) -> CMap.equal f m m'

    let is_empty = function
	I s -> CSet.is_empty s
      | _ -> false

    let cardinal = function
	I s -> CSet.cardinal s
      | B (m,_) -> CMap.cardinal m

    let is_identity = function
	I _ -> true
      | B _ -> false

    let fold f = function
      	I dom -> CSet.fold (fun i cont -> f i i cont) dom
      | B (map,_) -> CMap.fold (fun i j cont -> f i j cont) map


    let mem i = function
	I dom -> CSet.mem i dom
      | B (m,_) -> CMap.mem i m

    let comem i = function
	I dom -> CSet.mem i dom
      | B (_,m) -> CMap.mem i m

    let find i = function
	I dom -> CSet.find i dom
      | B (m,_) -> CMap.find i m

    let cofind i = function
	I dom -> CSet.find i dom
      | B (_,m) -> CMap.find i m

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
	    if i = j then I (CSet.add i dom)
	    else
	      let map =
		CSet.fold
		  (fun i map ->
		   CMap.add i i map
		  ) dom CMap.empty
	      in
	      B (CMap.add i j map, CMap.add j i map)
	  end
	| B (map,comap) -> B (CMap.add i j map, CMap.add j i comap)


    let sum bij bij' = fold (fun i j bij_sum -> add i j bij_sum) bij bij'

    let to_string = function
	I dom ->
	begin
	  let l =
	    CSet.fold (fun i cont -> (Content.to_string i)::cont) dom []
	  in
	  ("Id_{"^(String.concat "," l)^"}")
	end
      | bij ->
	 "("^(String.concat ","
			    (fold
			       (fun i j l -> ((Content.to_string i)^":"^(Content.to_string j))::l
			       ) bij [])
	     )^")"

    let to_dot_label bij =
      "[ label=\""^(to_string bij)^"\"]"
  end
