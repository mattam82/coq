(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** This module implements an "untyped store", in this particular case
    we see it as an extensible record whose fields are left
    unspecified. ***)

(** We use a dynamic "name" allocator. But if we needed to serialise
    stores, we might want something static to avoid troubles with
    plugins order. *)

module type T =
sig
end

module type S =
sig
  type t
  type 'a merge_field = 'a option -> 'a option -> 'a option
  type 'a field
  val empty : t
  val set : t -> 'a field -> 'a -> t
  val get : t -> 'a field -> 'a option
  val remove : t -> 'a field -> t
  val merge : t -> t -> t
  val field : 'a merge_field -> 'a field
  val default_merge_field : 'a merge_field
end

module Make (M : T) : S =
struct

  let next =
    let count = ref 0 in fun () ->
      let n = !count in
      incr count;
      n

  type t = Obj.t option array
  (** Store are represented as arrays. For small values, which is typicial,
      is slightly quicker than other implementations. *)

  type 'a merge_field = 'a option -> 'a option -> 'a option

  type 'a field = int * 'a merge_field

let allocate len : t = Array.make len None

let empty : t = [||]

let set (s : t) (i : 'a field) (v : 'a) : t =
  let i, merge = i in
  let len = Array.length s in
  let nlen = if i < len then len else succ i in
  let () = assert (0 <= i) in
  let ans = allocate nlen in
  Array.blit s 0 ans 0 len;
  Array.unsafe_set ans i (Some (Obj.repr (v, merge)));
  ans

let get (s : t) (i : 'a field) : 'a option =
  let i, merge = i in
  let len = Array.length s in
  if len <= i then None
  else Option.map fst (Obj.magic (Array.unsafe_get s i))

let remove (s : t) (i : 'a field) =
  let len = Array.length s in
  let i, merge = i in
  let () = assert (0 <= i) in
  let ans = allocate len in
  Array.blit s 0 ans 0 len;
  if i < len then Array.unsafe_set ans i None;
  ans

let merge (s1 : t) (s2 : t) : t =
  let len1 = Array.length s1 in
  let len2 = Array.length s2 in
  let nlen = if len1 < len2 then len2 else len1 in
  let ans = allocate nlen in
  (** Important: No more allocation from here. *)
  let merge vo vn =
    let merge, m =
      match vo, vn with
      | None, None ->
         (fun _ _ -> None), None
      | Some v, None ->
         let (v : 'a), (merge : 'a merge_field) = Obj.magic v in
         merge, merge (Some v) None
      | None, Some v ->
         let (v : 'a), (merge : 'a merge_field) = Obj.magic v in
         merge, merge None (Some v)
      | Some v, Some v' ->
         let v, (merge : 'a merge_field) = Obj.magic v in
         let v', merge' = Obj.magic v' in
         merge, merge (Some v) (Some v')
    in
    Option.map (fun v -> Obj.repr (v, merge)) m
  in
  for i = 0 to pred nlen do
    let v1 = if i < len1 then Array.unsafe_get s1 i else None in
    let v2 = if i < len2 then Array.unsafe_get s2 i else None in
    Array.unsafe_set ans i (merge v1 v2)
  done;
  ans

let field merge = next (), merge

let default_merge_field x y =
  match x, y with
  | None, None -> None
  | Some _, _ -> x
  | _, Some _ -> y

end
