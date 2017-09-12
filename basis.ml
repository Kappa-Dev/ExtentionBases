module Make (Node:Node.NodeType) =
  struct
    module Hom = Homomorphism.Make (Node)
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)

    type point = {value : Graph.t ; next : int list ; obs : Cat.embeddings option}
    type t = {extensions : point Lib.IntMap.t ; size : int}

    let empty = {extensions = Lib.IntMap.empty ; size = 0}
  end
