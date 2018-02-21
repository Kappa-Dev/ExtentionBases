type 'a t = {mutable hp: 'a list ; mutable lp : 'a list}
exception Empty

let create () =
  {hp = [] ; lp = []}

let add_hp e ql = ql.hp <- e::ql.hp ; ql
let add_lp e ql = ql.lp <- e::ql.lp ; ql

let pop ql =
  match ql.hp with
    e::tl -> ql.hp <- tl ; e
  | [] ->
     begin
       match ql.lp with
         [] -> raise Empty
       | e::tl -> ql.lp <- tl ; e
     end

let fold f ql cont =
  let cont =
    List.fold_left
      (fun cont e ->
        f e cont
      ) cont ql.hp
  in
  List.fold_left
    (fun cont e ->
      f e cont
    ) cont ql.lp

let elements ql =
  List.rev (fold (fun e l -> e::l) ql [])

let is_empty ql =
   ql.hp = [] && ql.lp = []
