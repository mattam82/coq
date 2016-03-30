(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
(* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
(* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)
(* Support for universe polymorphism by MS [2014] *)

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey, Matthieu
   Sozeau, Pierre-Marie Pédrot *)

open Pp
open Errors
open Util

(* Universes are stratified by a partial ordering $\le$.
   Let $\~{}$ be the associated equivalence. We also have a strict ordering
   $<$ between equivalence classes, and we maintain that $<$ is acyclic,
   and contained in $\le$ in the sense that $[U]<[V]$ implies $U\le V$.

   At every moment, we have a finite number of universes, and we
   maintain the ordering in the presence of assertions $U<V$ and $U\le V$.

   The equivalence $\~{}$ is represented by a tree structure, as in the
   union-find algorithm. The assertions $<$ and $\le$ are represented by
   adjacency lists *)

module type Hashconsed =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val hcons : t -> t
end

module HashedList (M : Hashconsed) :
sig
  type t = private Nil | Cons of M.t * int * t
  val nil : t
  val cons : M.t -> t -> t
end =
struct
  type t = Nil | Cons of M.t * int * t
  module Self =
  struct
    type _t = t
    type t = _t
    type u = (M.t -> M.t)
    let hash = function Nil -> 0 | Cons (_, h, _) -> h
    let equal l1 l2 = match l1, l2 with
    | Nil, Nil -> true
    | Cons (x1, _, l1), Cons (x2, _, l2) -> x1 == x2 && l1 == l2
    | _ -> false
    let hashcons hc = function
    | Nil -> Nil
    | Cons (x, h, l) -> Cons (hc x, h, l)
  end
  module Hcons = Hashcons.Make(Self)
  let hcons = Hashcons.simple_hcons Hcons.generate Hcons.hcons M.hcons
  (** No recursive call: the interface guarantees that all HLists from this
      program are already hashconsed. If we get some external HList, we can
      still reconstruct it by traversing it entirely. *)
  let nil = Nil
  let cons x l =
    let h = M.hash x in
    let hl = match l with Nil -> 0 | Cons (_, h, _) -> h in
    let h = Hashset.Combine.combine h hl in
    hcons (Cons (x, h, l))
end

module HList = struct

  module type S = sig
    type elt
    type t = private Nil | Cons of elt * int * t
    val hash : t -> int
    val nil : t
    val cons : elt -> t -> t
    val tip : elt -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val map : (elt -> elt) -> t -> t
    val smartmap : (elt -> elt) -> t -> t
    val exists : (elt -> bool) -> t -> bool
    val for_all : (elt -> bool) -> t -> bool
    val for_all2 : (elt -> elt -> bool) -> t -> t -> bool
    val mem : elt -> t -> bool
    val remove : elt -> t -> t
    val to_list : t -> elt list
    val compare : (elt -> elt -> int) -> t -> t -> int
  end

  module Make (H : Hashconsed) : S with type elt = H.t =
  struct
  type elt = H.t
  include HashedList(H)

  let hash = function Nil -> 0 | Cons (_, h, _) -> h

  let tip e = cons e nil

  let rec fold f l accu = match l with
  | Nil -> accu
  | Cons (x, _, l) -> fold f l (f x accu)

  let rec map f = function
  | Nil -> nil
  | Cons (x, _, l) -> cons (f x) (map f l)

  let smartmap = map
  (** Apriori hashconsing ensures that the map is equal to its argument *)

  let rec exists f = function
  | Nil -> false
  | Cons (x, _, l) -> f x || exists f l

  let rec for_all f = function
  | Nil -> true
  | Cons (x, _, l) -> f x && for_all f l

  let rec for_all2 f l1 l2 = match l1, l2 with
  | Nil, Nil -> true
  | Cons (x1, _, l1), Cons (x2, _, l2) -> f x1 x2 && for_all2 f l1 l2
  | _ -> false

  let rec to_list = function
  | Nil -> []
  | Cons (x, _, l) -> x :: to_list l

  let rec remove x = function
  | Nil -> nil
  | Cons (y, _, l) ->
    if H.equal x y then l
    else cons y (remove x l)

  let rec mem x = function
  | Nil -> false
  | Cons (y, _, l) -> H.equal x y || mem x l

  let rec compare cmp l1 l2 = match l1, l2 with
  | Nil, Nil -> 0
  | Cons (x1, h1, l1), Cons (x2, h2, l2) ->
    let c = Int.compare h1 h2 in
    if c == 0 then
      let c = cmp x1 x2 in
      if c == 0 then
        compare cmp l1 l2
      else c
    else c
  | Cons _, Nil -> 1
  | Nil, Cons _ -> -1

  end
end

module RawLevel =
struct
  open Names
  type t =
    | Prop
    | Set
    | Level of int * DirPath.t
    | Var of int

  (* Hash-consing *)

  let equal x y =
    x == y ||
      match x, y with
      | Prop, Prop -> true
      | Set, Set -> true
      | Level (n,d), Level (n',d') ->
        Int.equal n n' && DirPath.equal d d'
      | Var n, Var n' -> Int.equal n n'
      | _ -> false

  let compare u v =
    match u, v with
    | Prop,Prop -> 0
    | Prop, _ -> -1
    | _, Prop -> 1
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Level (i1, dp1), Level (i2, dp2) ->
      if i1 < i2 then -1
      else if i1 > i2 then 1
      else DirPath.compare dp1 dp2
    | Level _, _ -> -1
    | _, Level _ -> 1
    | Var n, Var m -> Int.compare n m

  let hequal x y =
    x == y ||
      match x, y with
      | Prop, Prop -> true
      | Set, Set -> true
      | Level (n,d), Level (n',d') ->
        n == n' && d == d'
      | Var n, Var n' -> n == n'
      | _ -> false

  let hcons = function
    | Prop as x -> x
    | Set as x -> x
    | Level (n,d) as x -> 
      let d' = Names.DirPath.hcons d in
        if d' == d then x else Level (n,d')
    | Var n as x -> x

  open Hashset.Combine

  let hash = function
    | Prop -> combinesmall 1 0
    | Set -> combinesmall 1 1
    | Var n -> combinesmall 2 n
    | Level (n, d) -> combinesmall 3 (combine n (Names.DirPath.hash d))

end

module LevelName = struct

  open Names

  type raw_level = RawLevel.t =
  | Prop
  | Set
  | Level of int * DirPath.t
  | Var of int

  (** Embed levels with their hash value *)
  type t = { 
    hash : int;
    data : RawLevel.t }

  let equal x y = 
    x == y || Int.equal x.hash y.hash && RawLevel.equal x.data y.data

  let hash x = x.hash

  let data x = x.data

  (** Hashcons on levels + their hash *)

  module Self = struct
    type _t = t
    type t = _t
    type u = unit
    let equal x y = x.hash == y.hash && RawLevel.hequal x.data y.data
    let hash x = x.hash
    let hashcons () x =
      let data' = RawLevel.hcons x.data in
      if x.data == data' then x else { x with data = data' }
  end

  let hcons =
    let module H = Hashcons.Make(Self) in
    Hashcons.simple_hcons H.generate H.hcons ()

  let make l = hcons { hash = RawLevel.hash l; data = l }

  let set = make Set
  let prop = make Prop

  let is_small x = 
    match data x with
    | Level _ -> false
    | Var _ -> false
    | Prop -> true
    | Set -> true
 
  let is_prop x =
    match data x with
    | Prop -> true
    | _ -> false

  let is_set x =
    match data x with
    | Set -> true
    | _ -> false

  let compare u v =
    if u == v then 0
    else
      let c = Int.compare (hash u) (hash v) in
	if c == 0 then RawLevel.compare (data u) (data v)
	else c

  let natural_compare u v =
    if u == v then 0
    else RawLevel.compare (data u) (data v)
	    
  let to_string x = 
    match data x with
    | Prop -> "Prop"
    | Set -> "Set"
    | Level (n,d) -> Names.DirPath.to_string d^"."^string_of_int n
    | Var n -> "Var(" ^ string_of_int n ^ ")"

  let pr u = str (to_string u)

  let apart u v =
    match data u, data v with
    | Prop, Set | Set, Prop -> true
    | _ -> false

  let vars = Array.init 20 (fun i -> make (Var i))

  let var n = 
    if n < 20 then vars.(n) else make (Var n)

  let var_index u =
    match data u with
    | Var n -> Some n | _ -> None

  let make m n = make (Level (n, Names.DirPath.hcons m))

end

(** Level maps *)
module LMap = struct 
  module M = HMap.Make (LevelName)
  include M

  let union l r = 
    merge (fun k l r -> 
      match l, r with
      | Some _, _ -> l
      | _, _ -> r) l r

  let subst_union l r = 
    merge (fun k l r -> 
      match l, r with
      | Some (Some _), _ -> l
      | Some None, None -> l
      | _, _ -> r) l r

  let diff ext orig =
    fold (fun u v acc -> 
      if mem u orig then acc 
      else add u v acc)
      ext empty

  let pr f m =
    h 0 (prlist_with_sep fnl (fun (u, v) ->
      LevelName.pr u ++ f v) (bindings m))
end

module LSet = struct
  include LMap.Set

  let pr prl s =
    str"{" ++ prlist_with_sep spc prl (elements s) ++ str"}"

  let of_array l =
    Array.fold_left (fun acc x -> add x acc) empty l

end


type 'a universe_map = 'a LMap.t

type universe_level_name = LevelName.t

type universe_level_subst_fn = LevelName.t -> LevelName.t

type universe_set = LSet.t

(* An algebraic universe [universe] is either a universe variable
   [Level.t] or a formal universe known to be greater than some
   universe variables and strictly greater than some (other) universe
   variables

   Universes variables denote universes initially present in the term
   to type-check and non variable algebraic universes denote the
   universes inferred while type-checking: it is either the successor
   of a universe present in the initial term to type-check or the
   maximum of two algebraic universes
*)

module Level = struct
  type t = LevelName.t * int
  type _t = t
	      
  (* Hashing of expressions *)
  module ExprHash = 
    struct
      type t = _t
      type u = LevelName.t -> LevelName.t
      let hashcons hdir (b,n as x) = 
	let b' = hdir b in 
	if b' == b then x else (b',n)
      let equal l1 l2 =
        l1 == l2 || 
          match l1,l2 with
	  | (b,n), (b',n') -> b == b' && n == n'
                                            
      let hash (x, n) = n + LevelName.hash x
                                       
    end
        
  module HExpr = struct 
    module H = Hashcons.Make(ExprHash)

    type t = ExprHash.t

    let hcons =
      Hashcons.simple_hcons H.generate H.hcons LevelName.hcons
    let hash = ExprHash.hash
    let equal x y = x == y ||
	              (let (u,n) = x and (v,n') = y in
	               Int.equal n n' && LevelName.equal u v)

  end

  let hcons = HExpr.hcons
  let hash = HExpr.hash

  let make l = hcons (l, 0)
  let name (x, y) = x

  let compare u v =
    if u == v then 0
    else 
      let (x, n) = u and (x', n') = v in
      if Int.equal n n' then LevelName.compare x x'
      else n - n'

  let natural_compare u v =
    if u == v then 0
    else 
      let (x, n) = u and (x', n') = v in
      if Int.equal n n' then LevelName.natural_compare x x'
      else n - n'

  let prop = make LevelName.prop
  let set = make LevelName.set
  let type1 = hcons (LevelName.set, 1)

  let is_prop = function
    | (l,0) -> LevelName.is_prop l
    | _ -> false

  let is_set = function
    | (l,0) -> LevelName.is_set l
    | _ -> false
	    
  let is_small = function
    | (l,0) -> LevelName.is_small l
    | _ -> false

  let equal x y = x == y ||
                    (let (u,n) = x and (v,n') = y in
	             Int.equal n n' && LevelName.equal u v)

  let leq (u,n) (v,n') =
    let cmp = LevelName.compare u v in
    if Int.equal cmp 0 then n <= n'
    else if n <= n' then 
      (LevelName.is_prop u && LevelName.is_small v)
    else false

  let succ (u,n) =
    if LevelName.is_prop u then type1
    else hcons (u, n + 1)

  let addn k (u,n as x) =
    assert(k >= 0);
    if k = 0 then x 
    else if LevelName.is_prop u then
      hcons (LevelName.set,n+k)
    else hcons (u,n+k)
	       
  let super (u,n as x) (v,n' as y) =
    let cmp = LevelName.compare u v in
    if Int.equal cmp 0 then 
      if n < n' then Inl true
      else Inl false
    else if is_prop x then Inl true
    else if is_prop y then Inl false
    else Inr cmp

  let to_string (v, n) =
    if Int.equal n 0 then LevelName.to_string v
    else LevelName.to_string v ^ "+" ^ string_of_int n

  let pr x = str(to_string x)

  let pr_with f (v, n) = 
    if Int.equal n 0 then f v
    else f v ++ str"+" ++ int n

  let is_level = function
    | (v, 0) -> true
    | _ -> false

  let level = function
    | (v,0) -> Some v
    | _ -> None
	    
  let get_level (v,n) = v

  let var_index (v, _) = LevelName.var_index v
                          
  let map f (v, n as x) = 
    let v' = f v in 
    if v' == v then x
    else if LevelName.is_prop v' && n != 0 then
      hcons (LevelName.set, n)
    else hcons (v', n)

  let apart (x, n) (y, m) =
    LevelName.apart x y && Int.equal n m

end

type universe_level = Level.t

module Universe =
struct
  (* Invariants: non empty, sorted and without duplicates *)
    
  let compare_expr = Level.compare

  module Huniv = HList.Make(Level.HExpr)
  type t = Huniv.t
  open Huniv
    
  let equal x y = x == y || 
    (Huniv.hash x == Huniv.hash y && 
       Huniv.for_all2 Level.equal x y)

  let hash = Huniv.hash

  let compare x y =
    if x == y then 0
    else 
      let hx = Huniv.hash x and hy = Huniv.hash y in
      let c = Int.compare hx hy in 
	if c == 0 then
	  Huniv.compare (fun e1 e2 -> compare_expr e1 e2) x y
	else c

  let rec hcons = function
  | Nil -> Huniv.nil
  | Cons (x, _, l) -> Huniv.cons x (hcons l)

  let make l = Huniv.tip l
  let make_name l = Huniv.tip (Level.make l)
                              
  let tip x = Huniv.tip x

  let pr l = match l with
    | Cons (u, _, Nil) -> Level.pr u
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma Level.pr (to_list l)) ++
        str ")"

  let pr_with f l = match l with
    | Cons (u, _, Nil) -> Level.pr_with f u
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma (Level.pr_with f) (to_list l)) ++
        str ")"

  let is_level l = match l with
    | Cons (l, _, Nil) -> Level.is_level l
    | _ -> false

  let var_index l = match l with
    | Cons (l, _, Nil) -> Level.var_index l
    | _ -> None

  let rec is_levels l = match l with
    | Cons (l, _, r) -> Level.is_level l && is_levels r
    | Nil -> true

  let level l = match l with
    | Cons (l, _, Nil) -> Some l
    | _ -> None

  let level_name l = match l with
    | Cons (l, _, Nil) -> Level.level l
    | _ -> None

  let level_set l = 
    fold (fun x acc -> LSet.add (Level.get_level x) acc) l LSet.empty

  let rec levels l = match l with
    | Cons (l, _, ls) -> l :: levels ls
    | Nil -> []
         
  let is_small u = 
    match u with
    | Cons (l, _, Nil) -> Level.is_small l
    | _ -> false

  (* The lower predicative level of the hierarchy that contains (impredicative)
     Prop and singleton inductive types *)
  let type0m = tip Level.prop

  (* The level of sets *)
  let type0 = tip Level.set

  (* When typing [Prop] and [Set], there is no constraint on the level,
     hence the definition of [type1_univ], the type of [Prop] *)    
  let type1 = tip (Level.succ Level.set)

  let is_type0m x = equal type0m x
  let is_type0 x = equal type0 x

  (* Returns the formal universe that lies just above the universe variable u.
     Used to type the sort u. *)
  let super l = 
    if is_small l then type1
    else
      Huniv.map (fun x -> Level.succ x) l

  let addn n l =
    assert (n >= 0);
    Huniv.map (fun x -> Level.addn n x) l

  let rec merge_univs l1 l2 =
    match l1, l2 with
    | Nil, _ -> l2
    | _, Nil -> l1
    | Cons (h1, _, t1), Cons (h2, _, t2) ->
      (match Level.super h1 h2 with
      | Inl true (* h1 < h2 *) -> merge_univs t1 l2
      | Inl false -> merge_univs l1 t2
      | Inr c -> 
        if c <= 0 (* h1 < h2 is name order *)
	then cons h1 (merge_univs t1 l2)
	else cons h2 (merge_univs l1 t2))

  let sort u =
    let rec aux a l = 
      match l with
      | Cons (b, _, l') ->
        (match Level.super a b with
	| Inl false -> aux a l'
	| Inl true -> l
	| Inr c ->
	  if c <= 0 then cons a l
	  else cons b (aux a l'))
      | Nil -> cons a l
    in 
      fold (fun a acc -> aux a acc) u nil
	
  (* Returns the formal universe that is greater than the universes u and v.
     Used to type the products. *)
  let sup x y = merge_univs x y

  let empty = nil

  let exists = Huniv.exists

  let for_all = Huniv.for_all

  let smartmap = Huniv.smartmap

end

type universe = Universe.t

(* The level of predicative Set *)
let type0m_univ = Universe.type0m
let type0_univ = Universe.type0
let type1_univ = Universe.type1
let is_type0m_univ = Universe.is_type0m
let is_type0_univ = Universe.is_type0
let is_univ_variable l = Universe.level l != None
let is_small_univ = Universe.is_small
let pr_uni = Universe.pr

let sup = Universe.sup
let super = Universe.super

open Universe

let universe_level = Universe.level

(* Miscellaneous functions to remove or test local univ assumed to
   occur in a universe *)

let univ_level_mem u v = Huniv.mem u v

let univ_level_rem u v min = 
  match Universe.level v with
  | Some u' -> if Level.equal u u' then min else v
  | None -> Huniv.remove ((* Level.make  *)u) v

(* Is u mentionned in v (or equals to v) ? *)


(**********************************************************************)
(** Universe polymorphism                                             *)
(**********************************************************************)

(** A universe level substitution, note that no algebraic universes are
    involved *)

type universe_level_subst = LevelName.t universe_map

(** A full substitution might involve algebraic universes *)
type universe_subst = universe universe_map

(** Substitution functions *)

(** With level to level substitutions. *)
let subst_univs_level_level_name subst l =
  try LMap.find l subst
  with Not_found -> l

let subst_univs_level_level subst l =
  Level.map (fun u -> subst_univs_level_level_name subst u) l
                     
let subst_univs_level_universe subst u =
  let u' = Universe.smartmap (subst_univs_level_level subst) u in
    if u == u' then u
    else Universe.sort u'
	                       
(** With level to universe substitutions. *)
type universe_subst_fn = universe_level_name -> universe

let make_subst subst = fun l -> LMap.find l subst

let subst_univs_expr_opt fn (l,n) =
  Universe.addn n (fn l)

let subst_univs_universe fn ul =
  let subst, nosubst = 
    Universe.Huniv.fold (fun u (subst,nosubst) -> 
      try let a' = subst_univs_expr_opt fn u in
	    (a' :: subst, nosubst)
      with Not_found -> (subst, u :: nosubst))
      ul ([], [])
  in 
    if CList.is_empty subst then ul
    else 
      let substs = 
	List.fold_left Universe.merge_univs Universe.empty subst
      in
	List.fold_left (fun acc u -> Universe.merge_univs acc (Universe.Huniv.tip u))
	  substs nosubst

module Instance : sig 
    type t = Universe.t array

    val empty : t
    val is_empty : t -> bool
      
    val of_array : Universe.t array -> t
    val to_array : t -> Universe.t array

    val append : t -> t -> t
    val equal : t -> t -> bool
    val length : t -> int

    val hcons : t -> t
    val hash : t -> int

    val share : t -> t * int

    val level_subst_fn : universe_level_subst_fn -> t -> t
    val subst_fn : universe_subst_fn -> t -> t
    
    val pr : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
    val levels : t -> LSet.t
    val map : (Universe.t -> Universe.t) -> t -> t
end = 
struct
  type t = Universe.t array

  let empty : t = [||]

  module HInstancestruct =
  struct
    type _t = t
    type t = _t
    type u = Universe.t -> Universe.t

    let hashcons huniv a = 
      let len = Array.length a in
	if Int.equal len 0 then empty
	else begin
	  for i = 0 to len - 1 do
	    let x = Array.unsafe_get a i in
	    let x' = huniv x in
	      if x == x' then ()
	      else Array.unsafe_set a i x'
	  done;
	  a
	end

    let equal t1 t2 =
      t1 == t2 ||
	(Int.equal (Array.length t1) (Array.length t2) &&
	   let rec aux i =
	     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
	   in aux 0)
	
    let hash a = 
      let accu = ref 0 in
	for i = 0 to Array.length a - 1 do
	  let l = Array.unsafe_get a i in
	  let h = Universe.hash l in
	    accu := Hashset.Combine.combine !accu h;
	done;
	(* [h] must be positive. *)
	let h = !accu land 0x3FFFFFFF in
	  h
  end

  module HInstance = Hashcons.Make(HInstancestruct)

  let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons Universe.hcons
    
  let hash = HInstancestruct.hash
    
  let share a = (hcons a, hash a)
	      
  let empty = hcons [||]

  let is_empty x = Int.equal (Array.length x) 0

  let append x y =
    if Array.length x = 0 then y
    else if Array.length y = 0 then x 
    else Array.append x y

  let of_array a =
    assert(Array.for_all (fun x -> not (Universe.is_type0m x)) a);
    a

  let to_array a = a

  let length a = Array.length a

  let level_subst_fn fn t = 
    let t' = CArray.smartmap (Universe.smartmap (Level.map fn)) t in
      if t' == t then t else of_array t'

  let subst_fn fn t =
    CArray.smartmap (fun x -> subst_univs_universe fn x) t

  let levels x =
    Array.fold_left (fun acc x -> LSet.union (Universe.level_set x) acc)
                    LSet.empty x

  let pr fn =
    prvect_with_sep spc (Universe.pr_with fn)

  let map f t =
    CArray.smartmap f t

  let equal t u = 
    t == u ||
      (Array.is_empty t && Array.is_empty u) ||
      (CArray.for_all2 Universe.equal t u 
	 (* Necessary as universe instances might come from different modules and 
	    unmarshalling doesn't preserve sharing *))

end
  
module Abstraction : sig
  type t = LevelName.t array
                       
  val empty : t
  val is_empty : t -> bool
                       
  val of_array : LevelName.t array -> t
  val to_array : t -> LevelName.t array
                                 
  val append : t -> t -> t
  val equal : t -> t -> bool
  val length : t -> int
                     
  val hcons : t -> t
  val hash : t -> int
                   
  val share : t -> t * int
                        
  val subst_fn : universe_level_subst_fn -> t -> t
                                                 
  val pr : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  val levels : t -> LSet.t
  val instance : t -> Instance.t
end = 
struct
  type t = LevelName.t array

  let empty : t = [||]

  module HAbstractionstruct =
  struct
    type _t = t
    type t = _t
    type u = LevelName.t -> LevelName.t

    let hashcons huniv a = 
      let len = Array.length a in
	if Int.equal len 0 then empty
	else begin
	  for i = 0 to len - 1 do
	    let x = Array.unsafe_get a i in
	    let x' = huniv x in
	      if x == x' then ()
	      else Array.unsafe_set a i x'
	  done;
	  a
	end

    let equal t1 t2 =
      t1 == t2 ||
	(Int.equal (Array.length t1) (Array.length t2) &&
	   let rec aux i =
	     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
	   in aux 0)
	
    let hash a = 
      let accu = ref 0 in
	for i = 0 to Array.length a - 1 do
	  let l = Array.unsafe_get a i in
	  let h = LevelName.hash l in
	    accu := Hashset.Combine.combine !accu h;
	done;
	(* [h] must be positive. *)
	let h = !accu land 0x3FFFFFFF in
	  h
  end

  module HAbstraction = Hashcons.Make(HAbstractionstruct)

  let hcons = Hashcons.simple_hcons HAbstraction.generate HAbstraction.hcons LevelName.hcons
    
  let hash = HAbstractionstruct.hash
    
  let share a = (hcons a, hash a)
	      
  let empty = hcons [||]

  let is_empty x = Int.equal (Array.length x) 0

  let append x y =
    if Array.length x = 0 then y
    else if Array.length y = 0 then x 
    else Array.append x y

  let of_array a =
    assert(Array.for_all (fun x -> not (LevelName.is_prop x)) a);
    a

  let instance a =
    Instance.of_array (Array.map Universe.make_name a)

  let to_array a = a

  let length a = Array.length a

  let subst_fn fn t = 
    let t' = CArray.smartmap fn t in
      if t' == t then t else of_array t'

  let levels x = LSet.of_array x

  let pr =
    prvect_with_sep spc

  let equal t u = 
    t == u ||
      (Array.is_empty t && Array.is_empty u) ||
      (CArray.for_all2 LevelName.equal t u 
	 (* Necessary as universe instances might come from different modules and 
	    unmarshalling doesn't preserve sharing *))

end
                       
let subst_univs_level_abstraction subst i =
  Abstraction.subst_fn (subst_univs_level_level_name subst) i

let subst_univs_level_instance subst i =
  let i' = Instance.level_subst_fn (subst_univs_level_level_name subst) i in
    if i == i' then i
    else i'
           
type universe_instance = Instance.t

type 'a puniverses = 'a * Instance.t
let out_punivs (x, y) = x
let in_punivs x = (x, Instance.empty)
let eq_puniverses f (x, u) (y, u') =
  f x y && Instance.equal u u'


type constraint_type = Lt | Le | Eq

type explanation = (constraint_type * universe) list

let constraint_type_ord c1 c2 = match c1, c2 with
| Lt, Lt -> 0
| Lt, _ -> -1
| Le, Lt -> 1
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, _ -> 1

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type univ_inconsistency = constraint_type * universe * universe * explanation option

exception UniverseInconsistency of univ_inconsistency

let error_inconsistency o u v (p:explanation option) =
  raise (UniverseInconsistency (o,make u,make v,p))

(* Constraints and sets of constraints. *)    

type 'a univ_constraint = 'a * constraint_type * 'a

let pr_constraint_type op = 
  let op_str = match op with
    | Lt -> " < "
    | Le -> " <= "
    | Eq -> " = "
  in str op_str

module UConstraintOrd =
struct
  type t = Level.t univ_constraint
  let compare (u,c,v) (u',c',v') =
    let i = constraint_type_ord c c' in
    if not (Int.equal i 0) then i
    else
      let i' = Level.compare u u' in
      if not (Int.equal i' 0) then i'
      else Level.compare v v'
end

module Constraint :
sig
  type t
         
  val empty : t
  val is_empty : t -> bool
  val union : t -> t -> t
  val diff : t -> t -> t
  val fold : (Level.t univ_constraint -> 'a -> 'a) -> t -> 'a -> 'a
  val equal : t -> t -> bool
  val for_all : (Level.t univ_constraint -> bool) -> t -> bool
  val pr : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
                        
  type 'a constraint_function = 'a -> 'a -> t -> t

  val enforce : Universe.t univ_constraint -> t -> t
  val enforce_eq : universe constraint_function
  val enforce_leq : universe constraint_function
  val enforce_eq_level : universe_level constraint_function
  val enforce_leq_level : universe_level constraint_function
  val enforce_eq_instances : universe_instance constraint_function

  val add : Level.t univ_constraint -> t -> t
    
  val hcons_constraint : Level.t univ_constraint -> Level.t univ_constraint
  val hcons : t -> t
                                               
end = struct 
  module S = Set.Make(UConstraintOrd)
  include S

  module Hconstraint =
    Hashcons.Make(
        struct
          type t = Level.t univ_constraint
          type u = Level.t -> Level.t
          let hashcons hul (l1,k,l2) = (hul l1, k, hul l2)
          let equal (l1,k,l2) (l1',k',l2') =
	    l1 == l1' && k == k' && l2 == l2'
          let hash = Hashtbl.hash
        end)

  type _t = t
  module Hconstraints =
    Hashcons.Make(
        struct
          type t = _t
          type u = Level.t univ_constraint -> Level.t univ_constraint
          let hashcons huc s =
	    fold (fun x -> add (huc x)) s empty
          let equal s s' =
	    List.for_all2eq (==)
	                    (elements s)
	                    (elements s')
          let hash = Hashtbl.hash
        end)

  let hcons_constraint = Hashcons.simple_hcons Hconstraint.generate Hconstraint.hcons Level.hcons
  let hcons = Hashcons.simple_hcons Hconstraints.generate Hconstraints.hcons hcons_constraint
            
  let pr prl c =
    fold (fun (u1,op,u2) pp_std ->
      pp_std ++ Level.pr_with prl u1 ++ pr_constraint_type op ++
	Level.pr_with prl u2 ++ fnl () )  c (str "")

  (** Constraint functions. *)
  type 'a constraint_function = 'a -> 'a -> t -> t
         
  let enforce_eq_level u v c =
    (* We discard trivial constraints like u=u *)
    if Level.equal u v then c 
    else if Level.apart u v then
      error_inconsistency Eq u v None
    else add (u,Eq,v) c
             
  let enforce_eq u v c =
    match Universe.level u, Universe.level v with
    | Some u, Some v -> enforce_eq_level u v c
    | _ -> anomaly (Pp.str "A universe comparison can only happen between variables")
                                         
  let enforce_eq u v c =
    if Universe.equal u v then c
    else enforce_eq u v c
	            
  let check_univ_leq_one u v = Universe.exists (Level.leq u) v
  let check_univ_leq u v = 
    Universe.for_all (fun u -> check_univ_leq_one u v) u

  let enforce_leq_level u v c =
    if Level.leq u v then c else add (u,Le,v) c

  let enforce_leq u v c =
    let open Universe.Huniv in
    let rec aux acc v =
      match v with
      | Cons (v, _, l) ->
         aux (fold (fun u -> enforce_leq_level u v) u c) l
      | Nil -> acc
    in aux c v
           
  let enforce_leq u v c =
    if check_univ_leq u v then c
    else enforce_leq u v c

  let enforce (u,d,v) =
    match d with
    | Eq -> enforce_eq u v
    | Le -> enforce_leq u v
    | Lt -> enforce_leq (super u) v

  let add (u, d, v) c =
    match d with
    | Eq -> enforce_eq_level u v c
    | Le -> enforce_leq_level u v c
    | Lt -> if Level.is_prop u && not (Level.is_prop v) then c
           else enforce_leq_level (Level.succ u) v c

  let enforce_eq_instances x y = 
    let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      anomaly (Pp.(++) (Pp.str "Invalid argument: enforce_eq_instances called with")
		 (Pp.str " instances of different lengths"));
    CArray.fold_right2 enforce_eq ax ay

                       
end

type constraints = Constraint.t
                          
(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

let constraints_of (_, cst) = cst

let subst_univs_level_constraint subst (u,d,v) =
  let u' = subst_univs_level_level subst u 
  and v' = subst_univs_level_level subst v in
    if d != Lt && Level.equal u' v' then None
    else Some (u',d,v')

let subst_univs_level_constraints subst csts =
  Constraint.fold 
    (fun c -> Option.fold_right Constraint.add (subst_univs_level_constraint subst c))
    csts Constraint.empty 
                                                     
(** A context of universe levels with universe constraints,
    representing local universe variables and constraints *)

module UContext =
struct
  type t = Abstraction.t constrained

  let make x = x

  (** Universe contexts (variables as a list) *)
  let empty = (Abstraction.empty, Constraint.empty)
  let is_empty (univs, cst) = Abstraction.is_empty univs && Constraint.is_empty cst

  let pr prl (univs, cst as ctx) =
    if is_empty ctx then mt() else
      h 0 (Abstraction.pr prl univs ++ str " |= ") ++
        h 0 (v 0 (Constraint.pr prl cst))

  let hcons (univs, cst) =
    (Abstraction.hcons univs, Constraint.hcons cst)

  let abstraction (univs, cst) = univs
  let constraints (univs, cst) = cst

  let union (univs, cst) (univs', cst') =
    Abstraction.append univs univs', Constraint.union cst cst'

  let dest x = x

  let size (x,_) = Abstraction.length x
  let instance (x, _) = Abstraction.instance x
                                      
end

type universe_context = UContext.t
let hcons_universe_context = UContext.hcons

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking. 
    Beware, representation could change.
*)

module ContextSet =
struct
  type t = universe_set constrained

  let empty = (LSet.empty, Constraint.empty)
  let is_empty (univs, cst) = LSet.is_empty univs && Constraint.is_empty cst

  let equal (univs, cst as x) (univs', cst' as y) =
    x == y || (LSet.equal univs univs' && Constraint.equal cst cst')
									
  let of_set s = (s, Constraint.empty)
  let singleton l = of_set (LSet.singleton l)
  let of_abstraction i = of_set (Abstraction.levels i)

  let union (univs, cst as x) (univs', cst' as y) =
    if x == y then x
    else LSet.union univs univs', Constraint.union cst cst'

  let append (univs, cst) (univs', cst') =
    let univs = LSet.fold LSet.add univs univs' in
    let cst = Constraint.fold Constraint.add cst cst' in
    (univs, cst)

  let diff (univs, cst) (univs', cst') =
    LSet.diff univs univs', Constraint.diff cst cst'

  let add_universe u (univs, cst) =
    LSet.add u univs, cst

  let add_constraints cst' (univs, cst) =
    univs, Constraint.union cst cst'

  let add_abstraction inst (univs, cst) =
    let v = Abstraction.to_array inst in
    let fold accu u = LSet.add u accu in
    let univs = Array.fold_left fold univs v in
    (univs, cst)

  let sort_levels a = 
    Array.sort LevelName.natural_compare a; a

  let to_context (ctx, cst) =
    (Abstraction.of_array (sort_levels (Array.of_list (LSet.elements ctx))), cst)

  let of_context (ctx, cst) =
    (Abstraction.levels ctx, cst)

  let pr prl (univs, cst as ctx) =
    if is_empty ctx then mt() else
      h 0 (LSet.pr prl univs ++ str " |= ") ++ h 0 (v 0 (Constraint.pr prl cst))

  let constraints (univs, cst) = cst
  let levels (univs, cst) = univs

end

type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

(** Substitutions. *)

let empty_subst = LMap.empty
let is_empty_subst = LMap.is_empty

let empty_level_subst = LMap.empty
let is_empty_level_subst = LMap.is_empty

let subst_univs_level fn l = 
  try Some (subst_univs_expr_opt fn l)
  with Not_found -> None

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_univs_level fn u in
  let v' = subst_univs_level fn v in
  match u', v' with
  | None, None -> Constraint.add c cstrs
  | Some u, None -> Constraint.enforce (u,d,make v) cstrs
  | None, Some v -> Constraint.enforce (make u,d,v) cstrs
  | Some u, Some v -> Constraint.enforce (u,d,v) cstrs

let subst_univs_constraints subst csts =
  Constraint.fold 
    (fun c cstrs -> subst_univs_constraint subst c cstrs)
    csts Constraint.empty 

let subst_instance_level_name s l =
  match l.LevelName.data with
  | LevelName.Var n -> s.(n) 
  | _ -> raise Not_found

let subst_instance_instance s i = 
  Array.smartmap (fun l -> subst_instance_level_name s l) i

let subst_instance_level s x =
  subst_univs_expr_opt (subst_instance_level_name s) x     

let subst_instance_universe s u =
  subst_univs_universe (subst_instance_level_name s) u
  (* let f x = subst_instance_level s x in *)
  (* let u' = Universe.smartmap f u in *)
  (*   if u == u' then u *)
  (*   else Universe.sort u' *)

let subst_instance_constraint s (u,d,v) =
  try
    let u' = subst_instance_level s u in
    (try let v' = subst_instance_level s v in
         (u',d,v')
     with Not_found -> (u',d,Universe.make v))
  with Not_found ->  
    let v' = subst_instance_level s v in
    (Universe.make u,d,v')
      
let subst_instance_constraints s csts =
  Constraint.fold 
    (fun c csts -> try let c' = subst_instance_constraint s c in
                  Constraint.enforce c' csts
                with Not_found -> Constraint.add c csts)
    csts Constraint.empty 

(* Abstraction by de Bruijn indices for universe levels *)
let make_abstraction_subst i = 
  let arr = Abstraction.to_array i in
    Array.fold_left_i (fun i acc l ->
      LMap.add l (LevelName.var i) acc)
      LMap.empty arr

let make_inverse_abstraction_subst i = 
  let arr = Abstraction.to_array i in
    Array.fold_left_i (fun i acc l ->
      LMap.add (LevelName.var i) l acc)
      LMap.empty arr

let abstract_universes poly ctx =
  let instance = UContext.abstraction ctx in
    if poly then
      let subst = make_abstraction_subst instance in
      let cstrs = subst_univs_level_constraints subst 
	(UContext.constraints ctx)
      in
      let ctx = UContext.make (instance, cstrs) in
	subst, ctx
    else empty_level_subst, ctx

(** Substitute instance inst for ctx in csts *)
let instantiate_univ_context (ctx, csts) =
  let subst = make_inverse_abstraction_subst ctx in
  (ctx, subst_univs_level_constraints subst csts)

let instantiate_univ_constraints u (_, csts) = 
  subst_instance_constraints u csts

(** Pretty-printing *)

let pr_constraints prl = Constraint.pr prl

let pr_universe_context = UContext.pr

let pr_universe_context_set = ContextSet.pr

let pr_universe_subst = 
  LMap.pr (fun u -> str" := " ++ Universe.pr u ++ spc ())

let pr_universe_level_subst = 
  LMap.pr (fun u -> str" := " ++ LevelName.pr u ++ spc ())

module Huniverse_set = 
  Hashcons.Make(
    struct
      type t = universe_set
      type u = universe_level_name -> universe_level_name
      let hashcons huc s =
	LSet.fold (fun x -> LSet.add (huc x)) s LSet.empty
      let equal s s' =
	LSet.equal s s'
      let hash = Hashtbl.hash
    end)

let hcons_universe_set = 
  Hashcons.simple_hcons Huniverse_set.generate Huniverse_set.hcons LevelName.hcons

let hcons_universe_context_set (v, c) = 
  (hcons_universe_set v, Constraint.hcons c)

let hcons_univ x = Universe.hcons x

let explain_universe_inconsistency prl (o,u,v,p) =
  let pr_uni = Universe.pr_with prl in
  let pr_rel = function
    | Eq -> str"=" | Lt -> str"<" | Le -> str"<=" 
  in
  let reason = match p with
    | None | Some [] -> mt()
    | Some p ->
      str " because" ++ spc() ++ pr_uni v ++
	prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ pr_uni v)
	p ++
	(if Universe.equal (snd (List.last p)) u then mt() else
	    (spc() ++ str "= " ++ pr_uni u)) 
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni v ++ reason

let compare_levels = LevelName.compare
let eq_levels = LevelName.equal
let equal_universes = Universe.equal



(** Aliases *)
let empty_constraint = Constraint.empty
[@@ deprecated]
let union_constraint = Constraint.union
[@@ deprecated]
let eq_constraint = Constraint.equal
[@@ deprecated]
let hcons_constraint = Constraint.hcons_constraint
[@@ deprecated]
let hcons_constraints = Constraint.hcons
[@@ deprecated]
let enforce_eq = Constraint.enforce_eq
[@@ deprecated]
let enforce_leq = Constraint.enforce_leq
[@@ deprecated]
let enforce_eq_level = Constraint.enforce_eq_level
[@@ deprecated]
let enforce_leq_level = Constraint.enforce_leq_level
[@@ deprecated]
let enforce_eq_instances = Constraint.enforce_eq_instances
[@@ deprecated]
                        
