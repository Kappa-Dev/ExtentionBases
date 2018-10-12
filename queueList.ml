type 'a t = {mutable hp: 'a Queue.t ; lp : 'a Queue.t}
exception Empty

let create () =
  {hp = Queue.create () ; lp = Queue.create ()}

let add_hp e ql = Queue.add e ql.hp ; ql
let add_lp e ql = Queue.add e ql.lp ; ql

let pop ql =
  try Queue.pop ql.hp with
    Queue.Empty ->
    try
      Queue.pop ql.lp
    with
      Queue.Empty -> raise Empty

let fold f ql cont =
  let cont =
    Queue.fold
      (fun cont e ->
        f e cont
      ) cont ql.hp
  in
  Queue.fold
    (fun cont e ->
      f e cont
    ) cont ql.lp

let elements ql =
  List.rev (fold (fun e l -> e::l) ql [])

let is_empty ql =
   Queue.is_empty ql.hp && Queue.is_empty ql.lp
