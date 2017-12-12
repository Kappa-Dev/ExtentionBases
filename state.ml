module type StateType =
  sig
    type t
    type node
    type byte_inst = CHECK of node * node | GOTO of node * node
    type native_inst
    type matching
    val compile : byte_inst -> native_inst
    val exec : matching -> t -> matching list -> native_inst -> matching list
  end

module MakeGeneric (Node:Node.NodeType) =
  (struct
    module Graph = Graph.Make (Node)
    module Hom = Homomorphism.Make (Node)

    type t = Graph.t
    type node = Node.t
    type byte_inst = CHECK of node * node | GOTO of node * node
    type native_inst = byte_inst
    type matching = Hom.t

    let (@) f u = try Hom.find u f with Not_found -> failwith "Invalid partial matching"

    let compile = fun inst -> inst
    let exec f state cont = function
        CHECK (u,v) -> if Graph.has_edge (f@u) (f@v) state then f::cont else cont
      | GOTO (u,v) ->
         List.fold_left
           (fun cont v' ->
             if Node.compatible v v' then
               try (Hom.add v v' f)::cont
               with
                 Hom.Not_injective -> cont
               | Hom.Not_structure_preserving -> failwith "Invariant violation"
             else
               cont
           ) cont (Graph.bound_to (f@u) state)

  end:StateType with type node = Node.t and type matching = Homomorphism.Make(Node).t)

module Kappa =
  (struct
    type node = Node.KappaNode.t
    (*[|(p_1,A_1) ; ...; (p_n,A_n)|] meaning port i is connected to port p_i of agent A_i*)
    type agent = {name : int ; ports : (int * int) array}
    type t = agent array
    type byte_inst = CHECK of node * node | GOTO of node * node
    module Hom = Homomorphism.Make(Node.KappaNode)
    type matching = Hom.t
    type native_inst = matching -> t -> matching list -> matching list

    let port_of = fun node -> Node.KappaNode.get_structure node 0
    let id_of = Node.KappaNode.id
    let compatible = Node.KappaNode.compatible
    let node_of = Node.KappaNode.create

    let (@) f u = try Hom.find u f with Not_found -> failwith "Invalid parital matching"

    let compile = function
        CHECK (u,v) ->
        (fun f state cont ->
          let u_s = f@u in
          let v_s = f@v in
          let a,i = state.(id_of u_s).ports.(port_of u_s) in
          if (a = id_of v_s && i = port_of v_s) then f::cont else cont
        )
      | GOTO (u,v) ->
         (fun f state cont ->
           try
             let u_s = f@u in
             let a,i = state.(id_of u_s).ports.(port_of u_s) in
             let v_s = node_of [a;i;state.(a).name] in
             if compatible v v_s then (Hom.add v v_s f)::cont
             else cont
           with Hom.Not_injective -> cont
              | Hom.Not_structure_preserving -> failwith "Invariant violation"
         )

    let exec f state cont inst = inst f state cont

  end:StateType with type node = Node.KappaNode.t and type matching = Homomorphism.Make(Node.KappaNode).t)
