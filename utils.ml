(* NOTE(dbp 2017-02-18): Due to issues with js_of_ocaml (assertion
   failures), we've removed the dependency on Core_kernel and instead
   replicated the few functions needed here, at the same names. *)

module List' = struct
  module Assoc = struct
    let rec remove xs x = match xs with
      | (y,v)::rest when y = x -> remove rest x
      | v::rest -> v :: remove rest x
      | [] -> []
    let find_exn l k = List.assoc k l
    let find l k = try Some (find_exn l k) with Not_found -> None
    let add l k v = (k,v)::l
    let mem l k = List.mem_assoc k l
  end

  let map ~f l = List.map f l
  let for_all ~f l = List.for_all f l
  let mem l x = List.mem x l
  let for_all2_exn ~f l1 l2 =
    if List.length l1 <> List.length l2 then
      raise (Failure "for_all2_exn: lists not the same length")
    else List.for_all2 f l1 l2
  let length = List.length
  let append = List.append
  let fold_left ~f ~init l = List.fold_left f init l
  let zip_exn l1 l2 =
    if List.length l1 <> List.length l2 then
      raise (Failure "zip_exn: lists not the same length")
    else List.combine l1 l2
  let concat = List.concat
  let mapi ~f l = List.mapi f l
  let nth_exn l n = List.nth l n
  let nth l n = try Some (List.nth l n) with Failure _ | Invalid_argument _ -> None
  let iter ~f l = let _ = List.map f l in ()
  let init ~f n =
    let rec init' i =
      if i = n then [] else (f i) :: init' (i+1)
    in init' 0
  let last_exn l = match l with
    | [] -> raise (Failure "last_exn: given empty list")
    | _ -> List.hd (List.rev l)
  let rec take l n = if n = 0 then [] else
      match l with
      | [] -> raise (Failure "take: not enough elements")
      | x::xs -> x :: take xs (n-1)
  let rec drop l n = if n = 0 then l else
      match l with
      | [] -> raise (Failure "drop: not enough elements")
      | _::xs -> drop xs (n-1)
  let split_n l n = (take l n, drop l n)
  let map2_exn ~f l1 l2 =
    if List.length l1 <> List.length l2 then
      raise (Failure "map2_exn: lists not the same length")
    else List.map2 f l1 l2
  let rev = List.rev
  let exists ~f l = List.exists f l
  let sort ~cmp l = List.sort cmp l
end
module List = List'

module Option' = struct
  let value ~default = function | None -> default | Some v -> v
  let (>>|) o f = match o with
    | None -> None
    | Some v -> Some (f v)
end
module Option = Option'

let replace rm r w = (r, w) :: List.Assoc.remove rm r

let list_subset l1 l2 = List.for_all ~f:(fun x -> List.mem l2 x) l1

let rec list_replace i l x =
  if i < 0 then raise (Failure "list_replace: don't pass negative indices!") else
    match (i, l) with
    | (0, _::xs) -> x::xs
    | (_, y::xs) -> y::(list_replace (i-1) xs x)
    | (_, []) -> raise (Failure "list_replace: index larger than list")

let list_index l x =
  let rec f i l =
    match l with
    | [] -> None
    | x'::_ when x' = x -> Some i
    | _::xs -> f (i+1) xs
  in f 0 l

let list_for_all2 ~f l1 l2 =
  try List.for_all2_exn ~f l1 l2
  with _ -> false

let global_replace c replacement str =
  let len = String.length str in
  let buf = Buffer.create len in
  for i = 0 to len - 1 do
    if str.[i] <> c
    then Buffer.add_char buf str.[i]
    else Buffer.add_string buf replacement
  done;
  Buffer.contents buf
