module Make (Node:Node.NodeType) =
  struct
    module Graph = Graph.Make (Node)
    module Cat = Cat.Make (Node)
    open Lib.Util

    type point = {value : Graph.t ;
                  next : Cat.embeddings Lib.IntMap.t ;
                  prev : int list ;
                  obs : (Cat.embeddings * int) list ;
                  conflict : Lib.IntSet.t ;
                  witnesses : Lib.IntSet.t}

    type param = {min : int ; deep : bool ; unique: bool}

    type t = {points : point Lib.IntMap.t ; fresh : int ; sharing : param ; leaves : Lib.IntSet.t ; extensions : Cat.embeddings Lib.IntMap.t}


    let to_dot dict ext_base =
      let l =
        Lib.IntMap.fold
          (fun i p dot_string ->
           let str = Printf.sprintf "%d [label=\"%d{sees: %s}[obs: %s]\"];" i
                                    i
                                    (String.concat "," (Lib.IntSet.fold (fun i cont -> string_of_int i::cont) p.witnesses []))
                                    (match p.obs with
                                       [] -> ""
                                     | ol -> String.concat ","
                                                           (List.map (fun (emb,x) ->
                                                                (Cat.string_of_embeddings ~nocolor:true emb)
                                                                  ^","^(Lib.Dict.to_name x dict)
                                                              ) ol))
           in
           let str2 =
             String.concat "\n"
                           (Lib.IntMap.fold
                              (fun j _ dot_string ->
                               (Printf.sprintf "%d -> %d ;" i j)::dot_string
                              ) p.next [])
           in
           let str3 =
             String.concat "\n"
                           (Lib.IntSet.fold
                              (fun j dot_string ->
                               (Printf.sprintf "%d -> %d [style = dotted];" i j)::dot_string
                              ) p.conflict [])
           in
           (str^str2^str3)::dot_string
          ) ext_base.points []
      in
      "digraph G{\n"^(String.concat "\n" l)^"\n}"

    let add p ext_base =
      ({ext_base with points = Lib.IntMap.add ext_base.fresh p ext_base.points ;
                      leaves = Lib.IntSet.add ext_base.fresh ext_base.leaves ;
                      fresh = ext_base.fresh+1
       },ext_base.fresh)

    let replace i p ext_base =
      assert (Lib.IntMap.mem i ext_base.points) ;
      {ext_base with points = Lib.IntMap.add i p ext_base.points}

    let mem i ext_base = Lib.IntMap.mem i ext_base.points

    let empty ?(deep=true) ?(unique=true) ?(min=1) h_eps =
      assert (min>0) ;
      {points = Lib.IntMap.add 0 {value = h_eps ;
                                  next = Lib.IntMap.empty ;
                                  prev = [] ;
                                  obs = [] ;
                                  conflict = Lib.IntSet.empty ;
                                  witnesses = Lib.IntSet.empty
                                 } Lib.IntMap.empty ;
       fresh = 1 ;
       sharing = {min = min ; deep = deep ; unique = unique} ;
       leaves = Lib.IntSet.singleton 0;
       extensions = Lib.IntMap.add 0 (Cat.identity h_eps h_eps) Lib.IntMap.empty
      }

    let is_empty ext_base = ext_base.fresh = 1

    let find i ext_base = Lib.IntMap.find i ext_base.points

    let cut_leaf i ext_base =
      let pi = find i ext_base in

      let ext_base = (*removing i from prev of successors of i*)
        Lib.IntMap.fold
          (fun j hom ext_base ->
           let pj = find j ext_base in
           replace j {pj with prev = List.filter (fun x -> x<>i) pj.prev} ext_base
          ) pi.next ext_base
      in
      let ext_base = (*removing i from next and witnesses of predecessors of i*)
        List.fold_left
          (fun ext_base j ->
           let pj = find j ext_base in
           replace j {pj with next = Lib.IntMap.remove i pj.next ;
                              witnesses = Lib.IntSet.remove i pj.witnesses
                     } ext_base
          ) ext_base pi.prev
      in
      {ext_base with points = Lib.IntMap.remove i ext_base.points}


    let (@@) = Cat.vertical_compose

    let update_witnesses i ext_base =
      let rec propagate prevs updated ext_base =
        match prevs with
          [] -> ext_base
        | j::tl ->
           if Lib.IntSet.mem j updated then propagate tl updated ext_base
           else
             let p = find j ext_base in
             propagate (p.prev@tl) (Lib.IntSet.add j updated) (replace j {p with witnesses = Lib.IntSet.add i p.witnesses} ext_base)
      in
      propagate (find i ext_base).prev Lib.IntSet.empty ext_base

    let find_extension i ext_base =
      if db() then print_string ("find_extension "^(string_of_int i)^"\n") ;

      if not (mem i ext_base) then
        failwith ("Unkown point "^(string_of_int i)^" in extension base")
      else
        Lib.IntMap.find i ext_base.extensions

    let add_step i j emb_ij ext_base =
      if db() then Printf.printf "Add Step %d |-> %d = %s-%s->%s\n" i j (Graph.to_string emb_ij.Cat.src) (Cat.string_of_embeddings emb_ij) (Graph.to_string emb_ij.Cat.trg) ;

      let pi = find i ext_base in
      let pj = find j ext_base in
      let new_wit = match pj.obs with
          [] -> pj.witnesses
        | _ -> Lib.IntSet.add j pj.witnesses
      in
      replace j {pj with prev = i::pj.prev}
              (replace i {pi with next = Lib.IntMap.add j emb_ij pi.next ;
                                  witnesses = Lib.IntSet.union pi.witnesses new_wit
                         } {ext_base with leaves = Lib.IntSet.remove i ext_base.leaves})


    let add_extension emb_w obs_opt conflict witnesses ext_base =
      let pw = {value = emb_w.Cat.trg ;
                next = Lib.IntMap.empty ;
                prev = [0] ;
                obs = obs_opt ;
                conflict = conflict ;
                witnesses = witnesses
               }
      in
      let ext_base,k = add pw ext_base in
      if db() then Printf.printf "Add extension 0 --> %d : %s\n" k (Cat.string_of_embeddings emb_w);
      ({ext_base with leaves = Lib.IntSet.add k ext_base.leaves ; extensions = Lib.IntMap.add k emb_w ext_base.extensions},k)

    let add_conflict i j ext_base =
      let pi = find i ext_base in
      let pj = find j ext_base in
      replace i {pi with conflict = Lib.IntSet.add j pi.conflict}
              (replace j {pj with conflict = Lib.IntSet.add i pj.conflict} ext_base)

    type sharing_info = {to_w : Cat.embeddings ; to_base : Cat.embeddings ; to_midpoint : Cat.embeddings ; has_sup : bool}
    type comparison = Iso of Cat.embeddings | Below of sharing_info | Above of sharing_info | Incomp of sharing_info

    let compare mp mp_to_i i mp_to_w ext_base =
      (*let obs_emb,obs_id =
        match (find w ext_base).obs with
          None -> failwith "Not a witness"
        | Some (ext,ids) -> ext,List.hd ids
      in*)
      if db() then
        begin
          Printf.printf "\t Sharing %s\n"  (Cat.string_of_span (mp_to_i,mp_to_w))
        end;
      match Cat.share ext_base.sharing.unique (mp_to_i,mp_to_w) with
        [] -> failwith "\t Extension should at least share their sources"
      | sharings ->
         List.fold_left
           (fun comparisons (ext_mp,sharing_tile) ->
            let sh_to_base,sh_to_w = sharing_tile.Cat.span in
            let _ = if db() then Printf.printf "Sharing is %s\n" (Cat.string_of_span (sh_to_base,sh_to_w)) in
            let iso_to_w = Cat.is_iso sh_to_w in
            let iso_to_base = Cat.is_iso sh_to_base in
            if iso_to_w then
              if iso_to_base then
                begin
                  let cmp = Iso (sh_to_base @@ (Cat.invert sh_to_w) ) (*Iso: w (<)--> i *)
                  in
                  cmp::comparisons
                end
              else
                begin
                  let cmp = Below {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = ext_mp ; has_sup = true} (*Below wit -> i*)
                  in
                  cmp::comparisons
                end
            else
              if iso_to_base then
                begin
                  let cmp = Above {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = ext_mp ; has_sup = true} (*Above i -> wit *)
                  in
                  cmp::comparisons
                end
              else
                let is_compatible =
                  match sharing_tile.Cat.cospan with
                    None -> false
                  | Some _ -> true
                in
                (Incomp {to_w = sh_to_w ; to_base = sh_to_base ; to_midpoint = ext_mp ; has_sup = is_compatible})::comparisons
           ) [] sharings

    let add_obs i ext obs_id ext_base =
      let pi = find i ext_base in
      let pi =
        match pi.obs with
          [] -> {pi with obs = [ext,obs_id]}
        | obs_ids -> {pi with obs = (ext,obs_id)::obs_ids}
      in
      replace i pi ext_base

    let remove_prev i k ext_base =
      let pi = find i ext_base in
      replace i {pi with prev = List.filter (fun j ->  j <> k) pi.prev} ext_base

    let remove_next i k ext_base =
      let pi = find i ext_base in
      replace i {pi with next = Lib.IntMap.remove k pi.next} ext_base

    let remove_step i j ext_base =
      let ext_base = remove_prev j i ext_base in
      remove_next i j ext_base

    let remove_point i ext_base =
      if db() then Printf.printf "Removing point %d\n" i ;
      let pi = find i ext_base in
      let ext_base =
        List.fold_left (fun ext_base j ->
                        remove_next j i ext_base
                       ) ext_base pi.prev
      in
      let ext_base =
        Lib.IntMap.fold (fun j _ ext_base ->
                         remove_prev j i ext_base
                        ) pi.next ext_base
      in
      {ext_base with extensions = Lib.IntMap.remove i ext_base.extensions ;
                     points = Lib.IntMap.remove i ext_base.points ;
                     leaves = Lib.IntSet.remove i ext_base.leaves}

    let insert ext_wit obs_emb obs_id ext_base =
      let rec push inf inf_to_w ext_base = function
          [] -> if db() then Printf.printf "Push stack: {}\n" ; ext_base
          | (i,emb_i)::tl as call_st ->
             if not (mem i ext_base) then push inf inf_to_w ext_base tl
             else
               let _ =  if db() then Printf.printf "Push stack: {%s}\n" (String.concat "," (List.map (fun (i,_) -> string_of_int i) call_st))
               in
               let comparisons = compare inf emb_i i inf_to_w ext_base
               in
               assert (comparisons<>[]) ;
               let ext_base,cont,inf,inf_to_w =
                 List.fold_left
                   (fun (ext_base,cont,inf,inf_to_w) cmp ->
                    if db() then Printf.printf "Continuation {%s}\n" (String.concat "," (List.map (fun (i,_) -> string_of_int i) cont)) ;
                    match cmp with

                      (*i <---(> w): emb*)
                      Iso emb ->
                      if db() then print_string (red "iso\n");
                      (*let ext_base =
                        if w<>0 then remove_point w ext_base
                        else ext_base
                      in*)
                      (add_obs i (emb@@obs_emb) obs_id ext_base,[],inf,inf_to_w)

                      (* emb: w --> mp*)
                      | Below sh_info ->
                         if db() then print_string (blue ("below "^(string_of_int i)^"\n"));
                         let pi = find i ext_base in
                         let ext_base,w =
                           add_extension ((Cat.invert sh_info.to_w)@@ext_wit)
                                         [obs_emb @@ sh_info.to_midpoint,obs_id]
                                         pi.witnesses Lib.IntSet.empty ext_base
                         in
                         let ext_base = add_step inf w sh_info.to_midpoint ext_base in
                         let ext_base = remove_step inf i ext_base in
                         (add_step w i sh_info.to_base ext_base,cont,inf,sh_info.to_midpoint)

                      (* emb: i --> w *)
                      | Above sh_info ->
                         if db() then print_string (yellow ("above "^(string_of_int i)^"\n"));
                         let emb_i_w = sh_info.to_w@@(Cat.invert sh_info.to_base) in
                         let pi = find i ext_base in
                         if Lib.IntMap.is_empty pi.next then
                           let ext_base,w =
                             add_extension ext_wit
                                           [obs_emb,obs_id]
                                           Lib.IntSet.empty Lib.IntSet.empty ext_base
                           in
                           (add_step i w emb_i_w ext_base, cont, i, emb_i_w)
                         else
                           let _ = if db() then print_string "Defering insertion\n" in
                           (ext_base,Lib.IntMap.fold
                                       (fun j emb cont ->
                                        (j,emb)::cont
                                       ) pi.next cont,i,emb_i_w)

                      (*i <-- mp --> w *)
                      | Incomp sh_info ->
                         if db() then print_string (green (Printf.sprintf "I found a midpoint %s!\n" (Graph.to_string sh_info.to_midpoint.Cat.trg)));
                         let conflict_w =
                           if sh_info.has_sup then Lib.IntSet.empty
                           else Lib.IntSet.singleton i
                         in
                         let ext_base,w =
                           add_extension ext_wit
                                         [obs_emb,obs_id]
                                         Lib.IntSet.empty Lib.IntSet.empty ext_base
                         in
                         let pw = find w ext_base in
                         let ext_base = replace w {pw with conflict = conflict_w} ext_base in
                         let pi = find i ext_base in
                         let conflict_i = if sh_info.has_sup then Lib.IntSet.add w pi.conflict else pi.conflict in
                         let ext_base = replace i {pi with conflict = conflict_i} ext_base in

                         let witnesses_mp = Lib.IntSet.add w pi.witnesses in

                         let ext_base,mp =
                           add_extension (sh_info.to_midpoint@@(find_extension inf ext_base))
                                         [] (*no observable*)
                                         Lib.IntSet.empty (*no immediate conflict*)
                                         witnesses_mp (*inherits the witnesses of i and {w}*)
                                         ext_base
                         in

                         if db() then print_string (green ("new point "^(string_of_int mp)^"\n"));
                         let mp_to_w = sh_info.to_w in
                         let ext_base = add_step inf mp sh_info.to_midpoint ext_base in
                         let ext_base = add_step mp i sh_info.to_base ext_base in
                         let ext_base = add_step mp w mp_to_w ext_base in
                         let ext_base = remove_step inf i ext_base in
                         let ext_base = remove_step inf w ext_base in
                         (ext_base,cont,mp,mp_to_w)
                   ) (ext_base,tl,inf,inf_to_w) comparisons
               in
                 push inf inf_to_w ext_base cont
      in
      (*
      let ext_base,w =
        add_extension ext_wit (Some (obs_emb,[obs_id])) Lib.IntSet.empty Lib.IntSet.empty ext_base
      in
       *)
      let p0 = find 0 ext_base in
      let id_0 = Cat.identity p0.value p0.value in
      push 0 ext_wit ext_base [(0,id_0)]


  end
