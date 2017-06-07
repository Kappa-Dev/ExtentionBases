module type OrderedType = sig type t val compare : t -> t -> int val to_string : t -> string end

module IntMap = Map.Make (struct type t = int let compare = compare end)

module IntSet = Set.Make (struct type t = int let compare = compare end)

module StringMap = Map.Make (struct type t = string let compare = compare end)
