(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
(* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
(* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey *)

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

module Level = struct

  type t =
    | Prop
    | Set
    | Level of int * Names.DirPath.t
  type _t = t

  (* Hash-consing *)
    
  module Hunivlevel =
  Hashcons.Make(
    struct
      type t = _t
      type u = Names.DirPath.t -> Names.DirPath.t
      let hashcons hdir = function
	| Prop as x -> x
	| Set as x -> x
	| Level (n,d) -> Level (n,hdir d)
      let equal l1 l2 =
        l1 == l2 ||
        match l1,l2 with
	| Prop, Prop -> true
	| Set, Set -> true
	| Level (n,d), Level (n',d') ->
	  n == n' && d == d'
	| _ -> false
      let hash = Hashtbl.hash
    end)
  
  let hcons = Hashcons.simple_hcons Hunivlevel.generate Names.DirPath.hcons

  let make m n = hcons (Level (n, m))

  let set = hcons Set
  let prop = hcons Prop

  let is_small = function
    | Level _ -> false
    | _ -> true

  let is_prop = function
    | Prop -> true
    | _ -> false

  let is_set = function
    | Set -> true
    | _ -> false

  (* A specialized comparison function: we compare the [int] part first.
     This way, most of the time, the [DirPath.t] part is not considered.

     Normally, placing the [int] first in the pair above in enough in Ocaml,
     but to be sure, we write below our own comparison function.

     Note: this property is used by the [check_sorted] function below. *)

  let compare u v =
    if u == v then 0
    else
    (match u,v with
    | Prop,Prop -> 0
    | Prop, _ -> -1
    | _, Prop -> 1
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Level (i1, dp1), Level (i2, dp2) ->
      if i1 < i2 then -1
      else if i1 > i2 then 1
      else Names.DirPath.compare dp1 dp2)

  let eq u v = u == v
  let leq u v = compare u v <= 0

  let to_string = function
    | Prop -> "Prop"
    | Set -> "Set"
    | Level (n,d) -> Names.DirPath.to_string d^"."^string_of_int n

  let pr u = str (to_string u)

end

let pr_universe_level_list l = 
  prlist_with_sep spc Level.pr l

module LSet = struct
  module M = Set.Make (Level)
  include M

  let pr s = 
    str"{" ++ pr_universe_level_list (elements s) ++ str"}"

  let of_list l =
    List.fold_left (fun acc x -> add x acc) empty l

  let of_array l =
    Array.fold_left (fun acc x -> add x acc) empty l
end

module LMap = struct 
  module M = Map.Make (Level)
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

  let elements = bindings
  let of_set s d = 
    LSet.fold (fun u -> add u d) s
      empty
    
  let of_list l =
    List.fold_left (fun m (u, v) -> add u v m) empty l 
    
  let universes m =
    fold (fun u _ acc -> LSet.add u acc) m LSet.empty

  let pr f m =
    h 0 (prlist_with_sep fnl (fun (u, v) ->
      Level.pr u ++ f v) (elements m))

  let find_opt t m =
    try Some (find t m)
    with Not_found -> None
end

type universe_level = Level.t

module LList = struct
  type t = Level.t list
  type _t = t
  module Huniverse_level_list = 
  Hashcons.Make(
    struct
      type t = _t
      type u = universe_level -> universe_level
      let hashcons huc s =
	List.fold_right (fun x a -> huc x :: a) s []
      let equal s s' = List.for_all2eq (==) s s'
      let hash = Hashtbl.hash
    end)

  let hcons = 
    Hashcons.simple_hcons Huniverse_level_list.generate Level.hcons

  let empty = hcons []
  let eq l l' = l == l' ||
    (try List.for_all2 Level.eq l l'
     with Invalid_argument _ -> false)

  let levels =
    List.fold_left (fun s x -> LSet.add x s) LSet.empty

end

type universe_level_list = universe_level list

type universe_level_subst_fn = universe_level -> universe_level

type universe_set = LSet.t
type 'a universe_map = 'a LMap.t

let compare_levels = Level.compare
let eq_levels = Level.eq

module Hashconsing = struct
  module Uid = struct
    type t = int

    let make_maker () =
      let _id = ref ~-1 in
	((fun () -> incr _id;!_id),
	 (fun () -> !_id),
	 (fun i -> _id := i))

    let dummy = -1

    external to_int : t -> int = "%identity"


    external of_int : int -> t= "%identity"
  end
    
  module Hcons = struct

    module type SA =
    sig
      type data
      type t
      val make : data -> t
      val node : t -> data
      val hash : t -> int
      val uid : t -> Uid.t
      val equal : t -> t -> bool
      val stats : unit -> unit
      val init : unit -> unit
    end

    module type S =
    sig

      type data
      type t = private { id : Uid.t;
			 key : int;
			 node : data }
      val make : data -> t
      val node : t -> data
      val hash : t -> int
      val uid : t -> Uid.t
      val equal : t -> t -> bool
      val stats : unit -> unit
      val init : unit -> unit
    end

    module Make (H : Hashtbl.HashedType) : S with type data = H.t =
    struct
      let uid_make,uid_current,uid_set = Uid.make_maker()
      type data = H.t
      type t = { id : Uid.t;
		 key : int;
		 node : data }
      let node t = t.node
      let uid t = t.id
      let hash t = t.key
      let equal t1 t2 = t1 == t2
      module WH = Weak.Make( struct
	type _t = t
	type t = _t
	let hash = hash
	let equal a b = a == b || H.equal a.node b.node
      end)
      let pool = WH.create 491

      exception Found of Uid.t
      let total_count = ref 0
      let miss_count = ref 0
      let init () =
	total_count := 0;
	miss_count := 0

      let make x =
	incr total_count;
	let cell = { id = Uid.dummy; key = H.hash x; node = x } in
	  try
	  WH.find pool cell
	  with
	  | Not_found ->
	  let cell = { cell with id = uid_make(); } in
	    incr miss_count;
	    WH.add pool cell;
	    cell

      exception Found of t

      let stats () = ()
    end
  end
  module HList = struct

    module type S = sig
      type elt
      type 'a node = Nil | Cons of elt * 'a

      module rec Node :
      sig
	include Hcons.S with type data = Data.t
      end
      and Data : sig
	include Hashtbl.HashedType with type t = Node.t node
      end
      type data = Data.t
      type t = Node.t
      val hash : t -> int
      val uid : t -> Uid.t
      val make : data -> t
      val equal : t -> t -> bool
      val nil : t
      val is_nil : t -> bool
      val tip : elt -> t
      val node : t -> t node
      val cons : (* ?sorted:bool -> *) elt -> t -> t
      val hd : t -> elt
      val tl : t -> t
      val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
      val map : (elt -> elt) -> t -> t
      val iter : (elt -> 'a) -> t -> unit
      val exists : (elt -> bool) -> t -> bool
      val for_all : (elt -> bool) -> t -> bool
      val rev : t -> t
      val rev_map : (elt -> elt) -> t -> t
      val length : t -> int
      val mem : elt -> t -> bool
      val remove : elt -> t -> t
      val stats : unit -> unit
      val init : unit -> unit
      val to_list : t -> elt list
      val compare : (elt -> elt -> int) -> t -> t -> int
    end

    module Make (H : Hcons.SA) : S with type elt = H.t =
    struct
      type elt = H.t
      type 'a node = Nil | Cons of elt * 'a
      module rec Node : Hcons.S with type data = Data.t = Hcons.Make (Data)
				and Data : Hashtbl.HashedType  with type t = Node.t node =
      struct
	type t = Node.t node
	let equal x y =
	  match x,y with
	  | _,_ when x==y -> true
	  | Cons (a,aa), Cons(b,bb) -> (aa==bb) && (H.equal a b)
	  | _ -> false
	let hash = function
	  | Nil -> 0
	  | Cons(a,aa) -> 17 + 65599 * (Uid.to_int (H.uid a)) + 491 * (Uid.to_int aa.Node.id)
      end
      
    type data = Data.t
    type t = Node.t
    let make = Node.make
    let node x = x.Node.node
    let hash x = x.Node.key
    let equal = Node.equal
    let uid x= x.Node.id
    let nil = Node.make Nil
    let stats = Node.stats
    let init = Node.init

    let is_nil =
      function { Node.node = Nil } -> true | _ -> false
				  
    (* doing sorted insertion allows to make
       better use of hash consing *)
    let rec sorted_cons e l =
      match l.Node.node with
      |	Nil -> Node.make (Cons(e, l))
      | Cons (x, ll) ->
      if H.uid e < H.uid x
      then Node.make (Cons(e, l))
      else Node.make (Cons(x, sorted_cons e ll))

    let cons e l =
      Node.make(Cons(e, l))
      
    let tip e = Node.make (Cons(e, nil))

    (* let cons ?(sorted=true) e l = *)
    (*   if sorted then sorted_cons e l else cons e l *)

    let hd = function { Node.node = Cons(a,_) } -> a | _ -> failwith "hd"
    let tl = function { Node.node = Cons(_,a) } -> a | _ -> failwith "tl"
    
    let fold f l acc =
      let rec loop acc l = match l.Node.node with
	| Nil -> acc
	| Cons (a, aa) -> loop (f a acc) aa
      in
	loop acc l

    let map f l  =
      let rec loop l = match l.Node.node with
	| Nil -> nil
	| Cons(a, aa) -> cons (f a) (loop aa)
      in
	loop l

    let iter f l =
      let rec loop l = match l.Node.node with
	| Nil -> ()
	| Cons(a,aa) ->  (f a);(loop aa)
      in
	loop l
	
    let exists f l =
      let rec loop l = match l.Node.node with
	| Nil -> false
	| Cons(a,aa) -> f a || loop aa
      in
	loop l
	
    let for_all f l =
      let rec loop l = match l.Node.node with
	| Nil -> true
	| Cons(a,aa) -> f a && loop aa
      in
	loop l

    let to_list l =
      let rec loop l = match l.Node.node with
	| Nil -> []
	| Cons(a,aa) -> a :: loop aa
      in
	loop l
	
    let remove x l =
      let rec loop l = match l.Node.node with
	| Nil -> l
	| Cons(a,aa) -> 
	  if H.equal a x then aa
	  else cons a (loop aa)
      in
	loop l

    let rev l = fold cons l nil
    let rev_map f l = fold (fun x acc -> cons (f x) acc) l nil
    let length l = fold (fun _ c -> c+1) l 0
    let rec mem e l =
      match l.Node.node with
      | Nil -> false
      | Cons (x, ll) -> x == e || mem e ll

    let rec compare cmp l1 l2 =
      if l1 == l2 then 0 else
	match node l1, node l2 with
	| Nil, Nil -> 0
	| _, Nil -> 1
	| Nil, _ -> -1
	| Cons (x1,l1), Cons(x2,l2) ->
          (match cmp x1 x2 with
          | 0 -> compare cmp l1 l2
          | c -> c)
      
    end
  end
end

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

module Universe =
struct
  (* Invariants: non empty, sorted and without duplicates *)

  module Expr = 
  struct
    type t = Level.t * int
    type _t = t
	
    (* Hashing of expressions *)
    module ExprHash = 
    struct
      type t = _t
      type u = Level.t -> Level.t
      let hashcons hdir (b,n as x) = 
	let b' = hdir b in 
	  if b' == b then x else (b',n)
      let equal l1 l2 =
        l1 == l2 || 
        match l1,l2 with
	| (b,n), (b',n') -> b == b' && n == n'
      let hash = Hashtbl.hash

    end

    module HExpr = 
    struct 

      include Hashcons.Make(ExprHash)

      type data = t
      type node = t

      let make =
	Hashcons.simple_hcons generate Level.hcons
      external node : node -> data = "%identity"
      let hash = ExprHash.hash
      let uid = hash
      let equal x y = x == y
      let stats _ = ()
      let init _ = ()
    end

    let hcons = HExpr.make

    let make l = hcons (l, 0)

    let compare u v =
      if u == v then 0
      else 
	let (x, n) = u and (x', n') = v in
	  if Int.equal n n' then Level.compare x x'
	  else n - n'

    let prop = make Level.prop
    let set = make Level.set
    let type1 = hcons (Level.set, 1)

    let is_prop = function
      | (l,0) -> Level.is_prop l
      | _ -> false

    let is_set = function
      | (l,0) -> Level.is_set l
      | _ -> false
      
    let is_type1 = function
      | (l,1) -> Level.is_set l
      | _ -> false
          
    let is_small = function
      | (l, 0) -> Level.is_small l
      | _ -> false

    (* let eq (u,n) (v,n') = *)
    (*   Int.equal n n' && Level.eq u v *)
    let eq x y = x == y

    let leq (u,n) (v,n') =
      let cmp = Level.compare u v in
	if Int.equal cmp 0 then n <= n'
	else if n <= n' then 
	  (Level.is_prop u && Level.is_small v)
	else false

    let successor (u,n) =
      if Level.is_prop u then type1
      else hcons (u, n + 1)

    let addn k (u,n as x) = 
      if k = 0 then x 
      else if Level.is_prop u then
	hcons (Level.set,n+k)
      else hcons (u,n+k)
	
    let super (u,n as x) (v,n' as y) =
      let cmp = Level.compare u v in
	if Int.equal cmp 0 then 
	  if n < n' then Inl true
	  else Inl false
	else if is_prop x then Inl true
	else if is_prop y then Inl false
	else Inr cmp

    let to_string (v, n) =
      if Int.equal n 0 then Level.to_string v
      else Level.to_string v ^ "+" ^ string_of_int n

    let pr x = str(to_string x)

    let level = function
      | (v,0) -> Some v
      | _ -> None
	
    let get_level (v,n) = v

    let map f (v, n as x) = 
      let v' = f v in 
	if v' == v then x
	else if Level.is_prop v' && n != 0 then
	  hcons (Level.set, n)
	else hcons (v', n)

  end

  module Hunivelt = struct
    let node x = x
    let make x = x
  end

  (* module Hunivelt = Hashconsing.Hcons.Make( *)
  (* struct *)
  (*   type t = Expr.t *)
  (*   let equal l1 l2 = *)
  (*     l1 == l2 ||  *)
  (*     match l1,l2 with *)
  (*     | (b,n), (b',n') -> b == b' && n == n' *)
  (*   let hash = Hashtbl.hash *)
  (* end) *)
    
  let compare_expr n m = Expr.compare (Hunivelt.node n) (Hunivelt.node m)
  let pr_expr n = Expr.pr (Hunivelt.node n)

  module Huniv = Hashconsing.HList.Make(Expr.HExpr)
  type t = Huniv.t
  open Huniv
    
  let eq x y = x == y (* Huniv.equal *)

  let compare u1 u2 =
    if eq u1 u2 then 0 else 
      Huniv.compare compare_expr u1 u2

  let hcons_unique = Huniv.make
  let normalize x = x
  (* let hcons_unique x = x *)
  let hcons x = hcons_unique (normalize x)

  let make l = Huniv.tip (Hunivelt.make (Expr.make l))
  let tip x = Huniv.tip (Hunivelt.make x)
    
  let equal_universes x y = 
    x == y
(* then true *)
(*     else *)
(* 	(\* Consider lists as sets, i.e. up to reordering, *)
(* 	   they are already without duplicates thanks to normalization. *\) *)
(*         CList.eq_set x' y' *)

  let pr l = match node l with
    | Cons (u, n) when is_nil n -> Expr.pr (Hunivelt.node u)
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma Expr.pr (List.map Hunivelt.node (to_list l))) ++
        str ")"
      
  let atom l = match node l with
    | Cons (l, n) when is_nil n -> Some l
    | _ -> None

  let level l = match node l with
    | Cons (l, n) when is_nil n -> Expr.level (Hunivelt.node l)
    | _ -> None

  let levels l = 
    fold (fun x acc -> LSet.add (Expr.get_level (Hunivelt.node x)) acc) l LSet.empty

  let is_small u = 
    match level (normalize u) with
    | Some l -> Level.is_small l
    | _ -> false

  (* The lower predicative level of the hierarchy that contains (impredicative)
     Prop and singleton inductive types *)
  let type0m = tip Expr.prop

  (* The level of sets *)
  let type0 = tip Expr.set

  (* When typing [Prop] and [Set], there is no constraint on the level,
     hence the definition of [type1_univ], the type of [Prop] *)    
  let type1 = tip (Expr.successor Expr.set)

  let is_type0m u =
    match level u with
    | Some l -> Level.is_prop l
    | _ -> false

  let is_type0 u =
    match level u with
    | Some l -> Level.is_set l
    | _ -> false

  let is_type1 u =
    match node u with
    | Cons (l, n) when is_nil n -> Expr.is_type1 (Hunivelt.node l)
    | _ -> false

  (* Returns the formal universe that lies juste above the universe variable u.
     Used to type the sort u. *)
  let super l = 
    Huniv.map (fun x -> Hunivelt.make (Expr.successor (Hunivelt.node x))) l

  let addn n l =
    Huniv.map (fun x -> Hunivelt.make (Expr.addn n (Hunivelt.node x))) l

  let rec merge_univs l1 l2 =
    match node l1, node l2 with
    | Nil, _ -> l2
    | _, Nil -> l1
    | Cons (h1, t1), Cons (h2, t2) ->
      (match Expr.super (Hunivelt.node h1) (Hunivelt.node h2) with
      | Inl true (* h1 < h2 *) -> merge_univs t1 l2
      | Inl false -> merge_univs l1 t2
      | Inr c -> 
        if c <= 0 (* h1 < h2 is name order *)
	then cons h1 (merge_univs t1 l2)
	else cons h2 (merge_univs l1 t2))

  let sort u =
    let rec aux a l = 
      match node l with
      | Cons (b, l') -> 
        (match Expr.super (Hunivelt.node a) (Hunivelt.node b) with
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

  let of_list l = 
    List.fold_right
      (fun x acc -> cons (Hunivelt.make x) acc)
      l nil
    
  let empty = nil
  let is_empty n = is_nil n

  let exists f l = 
    Huniv.exists (fun x -> f (Hunivelt.node x)) l

  let for_all f l = 
    Huniv.for_all (fun x -> f (Hunivelt.node x)) l

  let smartmap f l =
    Huniv.map (fun x -> 
      let n = Hunivelt.node x in
      let x' = f n in
	if x' == n then x else Hunivelt.make x')
      l

end

type universe = Universe.t

open Universe

(* type universe_list = UList.t *)
(* let pr_universe_list = UList.pr *)

let pr_uni = Universe.pr
let is_small_univ = Universe.is_small

let universe_level = Universe.level

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: Level.t;
      lt: Level.t list;
      le: Level.t list;
      rank : int}

let terminal u = {univ=u; lt=[]; le=[]; rank=0}

(* A Level.t is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)

type univ_entry =
    Canonical of canonical_arc
  | Equiv of Level.t


type universes = univ_entry LMap.t

let enter_equiv_arc u v g =
  LMap.add u (Equiv v) g

let enter_arc ca g =
  LMap.add ca.univ (Canonical ca) g

let is_type0m_univ = Universe.is_type0m

(* The level of predicative Set *)
let type0m_univ = Universe.type0m
let type0_univ = Universe.type0
let type1_univ = Universe.type1

let sup = Universe.sup
let super = Universe.super

let is_type0_univ = Universe.is_type0

let is_univ_variable l = Universe.level l != None

(* Every Level.t has a unique canonical arc representative *)

(* repr : universes -> Level.t -> canonical_arc *)
(* canonical representative : we follow the Equiv links *)

let repr g u =
  let rec repr_rec u =
    let a =
      try LMap.find u g
      with Not_found -> anomaly ~label:"Univ.repr"
	  (str"Universe " ++ Level.pr u ++ str" undefined")
    in
    match a with
      | Equiv v -> repr_rec v
      | Canonical arc -> arc
  in
  repr_rec u

let can g = List.map (repr g)

(* [safe_repr] also search for the canonical representative, but
   if the graph doesn't contain the searched universe, we add it. *)

let safe_repr g u =
  let rec safe_repr_rec u =
    match LMap.find u g with
      | Equiv v -> safe_repr_rec v
      | Canonical arc -> arc
  in
  try g, safe_repr_rec u
  with Not_found ->
    let can = terminal u in
    enter_arc can g, can

(* reprleq : canonical_arc -> canonical_arc list *)
(* All canonical arcv such that arcu<=arcv with arcv#arcu *)
let reprleq g arcu =
  let rec searchrec w = function
    | [] -> w
    | v :: vl ->
	let arcv = repr g v in
        if List.memq arcv w || arcu==arcv then
	  searchrec w vl
        else
	  searchrec (arcv :: w) vl
  in
  searchrec [] arcu.le


(* between : Level.t -> canonical_arc -> canonical_arc list *)
(* between u v = {w|u<=w<=v, w canonical}          *)
(* between is the most costly operation *)

let between g arcu arcv =
  (* good are all w | u <= w <= v  *)
  (* bad are all w | u <= w ~<= v *)
    (* find good and bad nodes in {w | u <= w} *)
    (* explore b u = (b or "u is good") *)
  let rec explore ((good, bad, b) as input) arcu =
    if List.memq arcu good then
      (good, bad, true) (* b or true *)
    else if List.memq arcu bad then
      input    (* (good, bad, b or false) *)
    else
      let leq = reprleq g arcu in
	(* is some universe >= u good ? *)
      let good, bad, b_leq =
	List.fold_left explore (good, bad, false) leq
      in
	if b_leq then
	  arcu::good, bad, true (* b or true *)
	else
	  good, arcu::bad, b    (* b or false *)
  in
  let good,_,_ = explore ([arcv],[],false) arcu in
    good

(* We assume  compare(u,v) = LE with v canonical (see compare below).
   In this case List.hd(between g u v) = repr u
   Otherwise, between g u v = []
 *)

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

(* Assuming the current universe has been reached by [p] and [l]
   correspond to the universes in (direct) relation [rel] with it,
   make a list of canonical universe, updating the relation with
   the starting point (path stored in reverse order). *)
let canp g (p:explanation Lazy.t) rel l : (canonical_arc * explanation Lazy.t) list =
  List.map (fun u -> (repr g u, lazy ((rel,Universe.make u):: Lazy.force p))) l

type order = EQ | LT of explanation Lazy.t | LE of explanation Lazy.t | NLE

(** [compare_neq] : is [arcv] in the transitive upward closure of [arcu] ?

  In [strict] mode, we fully distinguish between LE and LT, while in
  non-strict mode, we simply answer LE for both situations.

  If [arcv] is encountered in a LT part, we could directly answer
  without visiting unneeded parts of this transitive closure.
  In [strict] mode, if [arcv] is encountered in a LE part, we could only
  change the default answer (1st arg [c]) from NLE to LE, since a strict
  constraint may appear later. During the recursive traversal,
  [lt_done] and [le_done] are universes we have already visited,
  they do not contain [arcv]. The 4rd arg is [(lt_todo,le_todo)],
  two lists of universes not yet considered, known to be above [arcu],
  strictly or not.

  We use depth-first search, but the presence of [arcv] in [new_lt]
  is checked as soon as possible : this seems to be slightly faster
  on a test.
*)

let compare_neq strict g arcu arcv =
  (* [c] characterizes whether (and how) arcv has already been related
     to arcu among the lt_done,le_done universe *)
  let rec cmp c lt_done le_done = function
  | [],[] -> c
  | (arc,p)::lt_todo, le_todo ->
    if List.memq arc lt_done then
      cmp c lt_done le_done (lt_todo,le_todo)
    else
      let lt_new = canp g p Lt arc.lt@ canp g p Le arc.le in
      (try
	 let p = List.assq arcv lt_new in
	 if strict then LT p else LE p
       with Not_found ->
	 cmp c (arc::lt_done) le_done (lt_new@lt_todo,le_todo))
  | [], (arc,p)::le_todo ->
    if arc == arcv then
      (* No need to continue inspecting universes above arc:
	 if arcv is strictly above arc, then we would have a cycle.
         But we cannot answer LE yet, a stronger constraint may
	 come later from [le_todo]. *)
      if strict then cmp (LE p) lt_done le_done ([],le_todo) else LE p
    else
      if (List.memq arc lt_done) || (List.memq arc le_done) then
	cmp c lt_done le_done ([],le_todo)
      else
	let lt_new = canp g p Lt arc.lt in
	(try
	  let p = List.assq arcv lt_new in
	  if strict then LT p else LE p
	 with Not_found ->
	   let le_new = canp g p Le arc.le in
	   cmp c lt_done (arc::le_done) (lt_new, le_new@le_todo))
  in
  cmp NLE [] [] ([],[arcu,Lazy.from_val []])

let compare g arcu arcv =
  if arcu == arcv then EQ else compare_neq true g arcu arcv

let is_leq g arcu arcv =
  arcu == arcv ||
 (match compare_neq false g arcu arcv with
     NLE -> false
   | (EQ|LE _|LT _) -> true)

let is_lt g arcu arcv =
  match compare g arcu arcv with
      LT _ -> true
    | (EQ|LE _|NLE) -> false

(* Invariants : compare(u,v) = EQ <=> compare(v,u) = EQ
                compare(u,v) = LT or LE => compare(v,u) = NLE
                compare(u,v) = NLE => compare(v,u) = NLE or LE or LT

   Adding u>=v is consistent iff compare(v,u) # LT
    and then it is redundant iff compare(u,v) # NLE
   Adding u>v is consistent iff compare(v,u) = NLE
    and then it is redundant iff compare(u,v) = LT *)

(** * Universe checks [check_eq] and [check_leq], used in coqchk *)

(** First, checks on universe levels *)

let check_equal g u v =
  let g, arcu = safe_repr g u in
  let _, arcv = safe_repr g v in
  arcu == arcv

let check_smaller g strict u v =
  let g, arcu = safe_repr g u in
  let g, arcv = safe_repr g v in
  if strict then
    is_lt g arcu arcv
  else
    arcu == snd (safe_repr g Level.prop) || is_leq g arcu arcv

(** Then, checks on universes *)

type 'a check_function = universes -> 'a -> 'a -> bool

(* let equiv_list cmp l1 l2 = *)
(*   let rec aux l1 l2 = *)
(*     match l1 with *)
(*     | [] -> l2 = [] *)
(*     | hd :: tl1 -> *)
(*       let rec aux' acc = function *)
(* 	| hd' :: tl2 ->  *)
(* 	  if cmp hd hd' then aux tl1 (acc @ tl2) *)
(* 	  else aux' (hd' :: acc) tl2 *)
(* 	| [] -> false *)
(*       in aux' [] l2 *)
(*   in aux l1 l2 *)

let incl_list cmp l1 l2 =
  Huniv.for_all (fun x1 -> Huniv.exists (fun x2 -> cmp x1 x2) l2) l1

let compare_list cmp l1 l2 =
  (l1 == l2) || (* (equiv_list cmp l1 l2) *)
  (incl_list cmp l1 l2 && incl_list cmp l2 l1)

let check_equal_expr g x y =
  x == y || (let (u, n) = Hunivelt.node x and (v, m) = Hunivelt.node y in 
	       n = m && check_equal g u v)

(** [check_eq] is also used in [Evd.set_eq_sort],
    hence [Evarconv] and [Unification]. In this case,
    it seems that the Atom/Max case may occur,
    hence a relaxed version. *)

(* let gen_check_eq strict g u v = *)
(*   match u,v with *)
(*     | Atom ul, Atom vl -> check_equal g ul vl *)
(*     | Max(ule,ult), Max(vle,vlt) -> *)
(*         (\* TODO: remove elements of lt in le! *\) *)
(*         compare_list (check_equal g) ule vle && *)
(*         compare_list (check_equal g) ult vlt *)
(*     | _ -> *)
(*       (\* not complete! (Atom(u) = Max([u],[]) *\) *)
(*       if strict then anomaly (str "check_eq") *)
(*       else false (\* in non-strict mode, under-approximation *\) *)

(* let check_eq = gen_check_eq true *)
(* let lax_check_eq = gen_check_eq false *)
let check_eq g u v =
  compare_list (check_equal_expr g) u v
let check_eq_level g u v = u == v || check_equal g u v
let lax_check_eq = check_eq

let check_smaller_expr g (u,n) (v,m) =
  if n <= m then
    check_smaller g false u v
  else if n - m = 1 then
    check_smaller g true u v
  else false

let exists_bigger g ul l =
  Huniv.exists (fun ul' -> 
    check_smaller_expr g (Hunivelt.node ul) (Hunivelt.node ul')) l

let check_leq g u v =
  u == v ||
  match Universe.level u with
  | Some l when Level.is_prop l -> true
  | _ -> Huniv.for_all (fun ul -> exists_bigger g ul v) u

(** Enforcing new constraints : [setlt], [setleq], [merge], [merge_disc] *)

(* setlt : Level.t -> Level.t -> reason -> unit *)
(* forces u > v *)
(* this is normally an update of u in g rather than a creation. *)
let setlt g arcu arcv =
  let arcu' = {arcu with lt=arcv.univ::arcu.lt} in
  enter_arc arcu' g, arcu'

(* checks that non-redundant *)
let setlt_if (g,arcu) v =
  let arcv = repr g v in
  if is_lt g arcu arcv then g, arcu
  else setlt g arcu arcv

(* setleq : Level.t -> Level.t -> unit *)
(* forces u >= v *)
(* this is normally an update of u in g rather than a creation. *)
let setleq g arcu arcv =
  let arcu' = {arcu with le=arcv.univ::arcu.le} in
  enter_arc arcu' g, arcu'


(* checks that non-redundant *)
let setleq_if (g,arcu) v =
  let arcv = repr g v in
  if is_leq g arcu arcv then g, arcu
  else setleq g arcu arcv

(* merge : Level.t -> Level.t -> unit *)
(* we assume  compare(u,v) = LE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g arcu arcv =
  (* we find the arc with the biggest rank, and we redirect all others to it *)
  let arcu, g, v =
    let best_ranked (max_rank, old_max_rank, best_arc, rest) arc =
      if arc.rank >= max_rank
      then (arc.rank, max_rank, arc, best_arc::rest)
      else (max_rank, old_max_rank, best_arc, arc::rest)
    in
    match between g arcu arcv with
      | [] -> anomaly (str "Univ.between")
      | arc::rest ->
        let (max_rank, old_max_rank, best_arc, rest) =
          List.fold_left best_ranked (arc.rank, min_int, arc, []) rest in
        if max_rank > old_max_rank then best_arc, g, rest
        else begin
          (* one redirected node also has max_rank *)
          let arcu = {best_arc with rank = max_rank + 1} in
          arcu, enter_arc arcu g, rest
        end 
  in
  let redirect (g,w,w') arcv =
    let g' = enter_equiv_arc arcv.univ arcu.univ g in
    (g',List.unionq arcv.lt w,arcv.le@w')
  in
  let (g',w,w') = List.fold_left redirect (g,[],[]) v in
  let g_arcu = (g',arcu) in
  let g_arcu = List.fold_left setlt_if g_arcu w in
  let g_arcu = List.fold_left setleq_if g_arcu w' in
  fst g_arcu

(* merge_disc : Level.t -> Level.t -> unit *)
(* we assume  compare(u,v) = compare(v,u) = NLE *)
(* merge_disc u v  forces u ~ v with repr u as canonical repr *)
let merge_disc g arc1 arc2 =
  let arcu, arcv = if arc1.rank < arc2.rank then arc2, arc1 else arc1, arc2 in
  let arcu, g = 
    if not (Int.equal arc1.rank arc2.rank) then arcu, g
    else
      let arcu = {arcu with rank = succ arcu.rank} in 
      arcu, enter_arc arcu g
  in
  let g' = enter_equiv_arc arcv.univ arcu.univ g in
  let g_arcu = (g',arcu) in
  let g_arcu = List.fold_left setlt_if g_arcu arcv.lt in
  let g_arcu = List.fold_left setleq_if g_arcu arcv.le in
  fst g_arcu

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type univ_inconsistency = constraint_type * universe * universe * explanation

exception UniverseInconsistency of univ_inconsistency

let error_inconsistency o u v (p:explanation) =
  raise (UniverseInconsistency (o,make u,make v,p))

(* enforce_univ_leq : Level.t -> Level.t -> unit *)
(* enforce_univ_leq u v will force u<=v if possible, will fail otherwise *)
let enforce_univ_leq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  if is_leq g arcu arcv then g
  else match compare g arcv arcu with
    | LT p -> error_inconsistency Le u v (List.rev (Lazy.force p))
    | LE _ -> merge g arcv arcu
    | NLE -> fst (setleq g arcu arcv)
    | EQ -> anomaly (Pp.str "Univ.compare")

(* enforc_univ_eq : Level.t -> Level.t -> unit *)
(* enforc_univ_eq u v will force u=v if possible, will fail otherwise *)
let enforce_univ_eq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  match compare g arcu arcv with
    | EQ -> g
    | LT p -> error_inconsistency Eq v u (List.rev (Lazy.force p))
    | LE _ -> merge g arcu arcv
    | NLE ->
	(match compare g arcv arcu with
           | LT p -> error_inconsistency Eq u v (List.rev (Lazy.force p))
           | LE _ -> merge g arcv arcu
           | NLE -> merge_disc g arcu arcv
           | EQ -> anomaly (Pp.str "Univ.compare"))

(* enforce_univ_lt u v will force u<v if possible, will fail otherwise *)
let enforce_univ_lt u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  match compare g arcu arcv with
    | LT _ -> g
    | LE _ -> fst (setlt g arcu arcv)
    | EQ -> error_inconsistency Lt u v [(Eq,make v)]
    | NLE ->
      (match compare_neq false g arcv arcu with
	  NLE -> fst (setlt g arcu arcv)
	| EQ -> anomaly (Pp.str "Univ.compare")
	| (LE p|LT p) -> error_inconsistency Lt u v (List.rev (Lazy.force p)))

let empty_universes = LMap.empty
let initial_universes = enforce_univ_lt Level.prop Level.set LMap.empty
let is_initial_universes g = LMap.equal (==) g initial_universes

(* Constraints and sets of constraints. *)    

type univ_constraint = Level.t * constraint_type * Level.t

let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Le,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g

let pr_constraint_type op = 
  let op_str = match op with
    | Lt -> " < "
    | Le -> " <= "
    | Eq -> " = "
  in str op_str

module Constraint = 
struct 
  module S = Set.Make(
    struct
      type t = univ_constraint
      let compare (u,c,v) (u',c',v') =
	let i = constraint_type_ord c c' in
	  if not (Int.equal i 0) then i
	  else
	    let i' = Level.compare u u' in
	      if not (Int.equal i' 0) then i'
	      else Level.compare v v'
    end)
  include S

  let pr c =
    fold (fun (u1,op,u2) pp_std ->
      pp_std ++  Level.pr u1 ++ pr_constraint_type op ++
	Level.pr u2 ++ fnl () )  c (str "")

end

type constraints = Constraint.t

module Hconstraint =
  Hashcons.Make(
    struct
      type t = univ_constraint
      type u = universe_level -> universe_level
      let hashcons hul (l1,k,l2) = (hul l1, k, hul l2)
      let equal (l1,k,l2) (l1',k',l2') =
	l1 == l1' && k == k' && l2 == l2'
      let hash = Hashtbl.hash
    end)

module Hconstraints =
  Hashcons.Make(
    struct
      type t = constraints
      type u = univ_constraint -> univ_constraint
      let hashcons huc s =
	Constraint.fold (fun x -> Constraint.add (huc x)) s Constraint.empty
      let equal s s' =
	List.for_all2eq (==)
	  (Constraint.elements s)
	  (Constraint.elements s')
      let hash = Hashtbl.hash
    end)

let hcons_constraint = Hashcons.simple_hcons Hconstraint.generate Level.hcons
let hcons_constraints = Hashcons.simple_hcons Hconstraints.generate hcons_constraint

type universe_constraint_type = ULe | UEq | ULub

type universe_constraint = universe * universe_constraint_type * universe
module UniverseConstraints = struct
  module S = Set.Make(
  struct 
    type t = universe_constraint

    let compare_type c c' =
      match c, c' with
      | ULe, ULe -> 0
      | ULe, _ -> -1
      | _, ULe -> 1
      | UEq, UEq -> 0
      | UEq, _ -> -1
      | ULub, ULub -> 0
      | ULub, _ -> 1
      
    let compare (u,c,v) (u',c',v') =
      let i = compare_type c c' in
	if Int.equal i 0 then
	  let i' = Universe.compare u u' in
	    if Int.equal i' 0 then Universe.compare v v'
	    else 
	      if c != ULe && Universe.compare u v' = 0 && Universe.compare v u' = 0 then 0
	      else i'
	else i
  end)
  
  include S
  
  let add (l,d,r as cst) s = 
    if Universe.eq l r then s
    else add cst s

  let tr_dir = function
    | ULe -> Le
    | UEq -> Eq
    | ULub -> Eq

  let op_str = function ULe -> " <= " | UEq -> " = " | ULub -> " /\\ "

  let pr c =
    fold (fun (u1,op,u2) pp_std ->
	pp_std ++ Universe.pr u1 ++ str (op_str op) ++
	Universe.pr u2 ++ fnl ()) c (str "")

end

type universe_constraints = UniverseConstraints.t
type 'a universe_constrained = 'a * universe_constraints

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

let level_subst_of f = 
  fun l -> 
    try let u = f l in 
	  match Universe.level u with
	  | None -> l
	  | Some l -> l
    with Not_found -> l
     
module Instance = struct
  type t = Level.t array

  module HInstance =
    Hashcons.Make(
      struct
	type _t = t
	type t = _t
	type u = Level.t -> Level.t
	let hashcons huniv a = 
	  CArray.smartmap huniv a

	let equal t1 t2 =
	  t1 == t2 ||
	    (Int.equal (Array.length t1) (Array.length t2) &&
	       let rec aux i =
		 (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
	       in aux 0)

	let hash = Hashtbl.hash
    end)

  let hcons_instance = Hashcons.simple_hcons HInstance.generate Level.hcons

  let hcons = hcons_instance
  let empty = [||]
  let is_empty x = Int.equal (Array.length x) 0

  let eq t u = t == u || CArray.for_all2 Level.eq t u

  let of_array a = a
  let to_array a = a
    
  let eqeq t1 t2 =
    t1 == t2 ||
      (Int.equal (Array.length t1) (Array.length t2) &&
	 let rec aux i =
	   (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
	 in aux 0)

  let subst_fn fn t = CArray.smartmap fn t
  let subst s t = CArray.smartmap (fun x -> try LMap.find x s with Not_found -> x) t

  let levels x = LSet.of_array x

  let pr =
    prvect_with_sep spc Level.pr

  let append = Array.append

  let max_level i = 
    if Array.is_empty i then 0
    else
      let l = CArray.last i in
	match l with
	| Level.Level (i,_) -> i
	| _ -> assert false

  let check_eq g t1 t2 =
    t1 == t2 ||
      (Int.equal (Array.length t1) (Array.length t2) &&
	 let rec aux i =
	   (Int.equal i (Array.length t1)) || (check_eq_level g t1.(i) t2.(i) && aux (i + 1))
	 in aux 0)

end

type universe_instance = Instance.t

type 'a puniverses = 'a * Instance.t
let out_punivs (x, y) = x
let in_punivs x = (x, Instance.empty)

(** A context of universe levels with universe constraints,
    representiong local universe variables and constraints *)

module UContext =
struct
  type t = Instance.t constrained

  let make x = x

  (** Universe contexts (variables as a list) *)
  let empty = (Instance.empty, Constraint.empty)
  let is_empty (univs, cst) = Instance.is_empty univs && Constraint.is_empty cst

  let pr (univs, cst as ctx) =
    if is_empty ctx then mt() else
      Instance.pr univs ++ str " |= " ++ v 1 (Constraint.pr cst)

  let hcons (univs, cst) =
    (Instance.hcons univs, hcons_constraints cst)

  let instance (univs, cst) = univs
  let constraints (univs, cst) = cst

  let union (univs, cst) (univs', cst') =
    Instance.append univs univs', Constraint.union cst cst'
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

  let of_context (ctx,cst) =
    (Instance.levels ctx, cst)

  let of_set s = (s, Constraint.empty)
  let singleton l = of_set (LSet.singleton l)
  let of_instance i = of_set (Instance.levels i)

  let union (univs, cst) (univs', cst') =
    LSet.union univs univs', Constraint.union cst cst'

  let diff (univs, cst) (univs', cst') =
    LSet.diff univs univs', Constraint.diff cst cst'

  let add_constraints (univs, cst) cst' =
    univs, Constraint.union cst cst'

  let add_universes univs ctx =
    union (of_instance univs) ctx

  let to_context (ctx, cst) =
    (Array.of_list (LSet.elements ctx), cst)

  let of_context (ctx, cst) =
    (Instance.levels ctx, cst)

  let pr (univs, cst as ctx) =
    if is_empty ctx then mt() else
      LSet.pr univs ++ str " |= " ++ v 1 (Constraint.pr cst)

  let constraints (univs, cst) = cst
  let levels (univs, cst) = univs

end

type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

(** A universe level substitution, note that no algebraic universes are
    involved *)
type universe_level_subst = universe_level universe_map

(** A full substitution might involve algebraic universes *)
type universe_subst = universe universe_map

(** Pretty-printing *)
let pr_constraints = Constraint.pr

let pr_universe_context = UContext.pr

let pr_universe_context_set = ContextSet.pr

let pr_universe_subst = 
  LMap.pr (fun u -> str" := " ++ Universe.pr u ++ spc ())

let pr_universe_level_subst = 
  LMap.pr (fun u -> str" := " ++ Level.pr u ++ spc ())

let constraints_of (_, cst) = cst

let constraint_depend (l,d,r) u =
  Level.eq l u || Level.eq l r

let constraint_depend_list (l,d,r) us =
  List.mem l us || List.mem r us

let constraints_depend cstr us = 
  Constraint.exists (fun c -> constraint_depend_list c us) cstr

let remove_dangling_constraints dangling cst =
  Constraint.fold (fun (l,d,r as cstr) cst' -> 
    if List.mem l dangling || List.mem r dangling then cst'
    else
      (** Unnecessary constraints Prop <= u *)
      if Level.eq l Level.prop && d == Le then cst'
      else Constraint.add cstr cst') cst Constraint.empty
  
let check_context_subset (univs, cst) (univs', cst') =
  let newunivs, dangling = List.partition (fun u -> LSet.mem u univs) (Array.to_list univs') in
    (* Some universe variables that don't appear in the term 
       are still mentionned in the constraints. This is the 
       case for "fake" universe variables that correspond to +1s. *)
    (* if not (CList.is_empty dangling) then  *)
    (*   todo ("A non-empty set of inferred universes do not appear in the term or type"); *)
      (* (not (constraints_depend cst' dangling));*)
    (* TODO: check implication *)
  (** Remove local universes that do not appear in any constraint, they
      are really entirely parametric. *)
  (* let newunivs, dangling' = List.partition (fun u -> constraints_depend cst [u]) newunivs in *)
  let cst' = remove_dangling_constraints dangling cst in
    Array.of_list newunivs, cst'

(** Substitutions. *)

let make_universe_subst inst (ctx, csts) = 
  try Array.fold_left2 (fun acc c i -> LMap.add c (Universe.make i) acc)
        LMap.empty ctx inst
  with Invalid_argument _ -> 
    anomaly (Pp.str "Mismatched instance and context when building universe substitution")

let empty_subst = LMap.empty
let is_empty_subst = LMap.is_empty

let empty_level_subst = LMap.empty
let is_empty_level_subst = LMap.is_empty

(** Substitution functions *)

(** With level to level substitutions. *)
let subst_univs_level_level subst l =
  try LMap.find l subst
  with Not_found -> l

let rec normalize_univs_level_level subst l =
  try 
    let l' = LMap.find l subst in
      normalize_univs_level_level subst l'
  with Not_found -> l

let subst_univs_level_fail subst l =
  try match Universe.level (subst l) with 
  | Some l' -> l'
  | None -> l
  with Not_found -> l

let rec subst_univs_level_universe subst u =
  let u' = Universe.smartmap (Universe.Expr.map (subst_univs_level_level subst)) u in
    if u == u' then u
    else Universe.sort u'
	
let subst_univs_level_constraint subst (u,d,v) =
  let u' = subst_univs_level_level subst u 
  and v' = subst_univs_level_level subst v in
    if d != Lt && Level.eq u' v' then None
    else Some (u',d,v')

let subst_univs_level_constraints subst csts =
  Constraint.fold 
    (fun c -> Option.fold_right Constraint.add (subst_univs_level_constraint subst c))
    csts Constraint.empty 

(* let subst_univs_level_constraint_key = Profile.declare_profile "subst_univs_level_constraint";; *)
(* let subst_univs_level_constraint = *)
(*   Profile.profile2 subst_univs_level_constraint_key subst_univs_level_constraint *)

(** With level to universe substitutions. *)
type universe_subst_fn = universe_level -> universe

let make_subst subst = fun l -> LMap.find l subst

let subst_univs_level fn l = 
  try fn l
  with Not_found -> make l

let subst_univs_expr_opt fn (l,n) =
  try Some (Universe.addn n (fn l))
  with Not_found -> None

let subst_univs_universe fn ul =
  let subst, nosubst = 
    Universe.Huniv.fold (fun u (subst,nosubst) -> 
      match subst_univs_expr_opt fn (Hunivelt.node u) with
      | Some a' -> (a' :: subst, nosubst)
      | None -> (subst, u :: nosubst))
    ul ([], [])
  in 
    if CList.is_empty subst then ul
    else 
      let substs = 
	List.fold_left Universe.merge_univs Universe.empty subst
      in
	List.fold_left (fun acc u -> Universe.merge_univs acc (Universe.Huniv.tip u))
	  substs nosubst

let subst_univs_constraint fn (u,d,v) =
  let u' = subst_univs_level fn u and v' = subst_univs_level fn v in
    if d != Lt && Universe.eq u' v' then None
    else Some (u',d,v')

let subst_univs_universe_constraint fn (u,d,v) =
  let u' = subst_univs_universe fn u and v' = subst_univs_universe fn v in
    if Universe.eq u' v' then None
    else Some (u',d,v')

(** Constraint functions. *)

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

let constraint_add_leq v u c =
  (* We just discard trivial constraints like u<=u *)
  if Expr.eq v u then c
  else 
    match v, u with
    | (x,n), (y,m) -> 
    let j = m - n in
      if j = -1 (* n = m+1, v+1 <= u <-> v < u *) then
	Constraint.add (x,Lt,y) c
      else if j <= -1 (* n = m+k, v+k <= u <-> v+(k-1) < u *) then
	if Level.eq x y then (* u+(k+1) <= u *)
	  raise (UniverseInconsistency (Le, Universe.tip v, Universe.tip u, []))
	else anomaly (Pp.str"Unable to handle arbitrary u+k <= v constraints")
      else if j = 0 then
	Constraint.add (x,Le,y) c
      else (* j >= 1 *) (* m = n + k, u <= v+k *)
	if Level.eq x y then c (* u <= u+k, trivial *)
	else if Level.is_small x then c (* Prop,Set <= u+S k, trivial *)
	else anomaly (Pp.str"Unable to handle arbitrary u <= v+k constraints")
	  
let check_univ_eq u v = Universe.eq u v

let check_univ_leq_one u v = Universe.exists (Expr.leq u) v

let check_univ_leq u v = 
  Universe.for_all (fun u -> check_univ_leq_one u v) u

let enforce_leq u v c =
  match Huniv.node v with
  | Universe.Huniv.Cons (v, n) when Universe.is_empty n -> 
    Universe.Huniv.fold (fun u -> constraint_add_leq (Hunivelt.node u) (Hunivelt.node v)) u c
  | _ -> anomaly (Pp.str"A universe bound can only be a variable")

let enforce_leq u v c =
  if check_univ_leq u v then c
  else enforce_leq u v c

let enforce_eq_level u v c =
  (* We discard trivial constraints like u=u *)
  if Level.eq u v then c 
  else if (Level.is_prop u && Level.is_set v) || (Level.is_prop v && Level.is_set u) then
    error_inconsistency Eq u v []
  else Constraint.add (u,Eq,v) c

let enforce_eq u v c =
  match Universe.level u, Universe.level v with
    | Some u, Some v -> enforce_eq_level u v c
    | _ -> anomaly (Pp.str "A universe comparison can only happen between variables")

let enforce_eq u v c =
  if check_univ_eq u v then c
  else enforce_eq u v c

let enforce_leq_level u v c =
  if Level.eq u v then c else Constraint.add (u,Le,v) c

let enforce_eq_instances = CArray.fold_right2 enforce_eq_level 

type 'a universe_constraint_function = 'a -> 'a -> universe_constraints -> universe_constraints

let enforce_eq_instances_univs strict t1 t2 c = 
  let d = if strict then ULub else UEq in
    CArray.fold_right2 (fun x y -> UniverseConstraints.add (Universe.make x, d, Universe.make y))
      t1 t2 c

let merge_constraints c g =
  Constraint.fold enforce_constraint c g

(* let merge_constraints_key = Profile.declare_profile "merge_constraints";; *)
(* let merge_constraints = Profile.profile2 merge_constraints_key merge_constraints *)

let check_constraint g (l,d,r) =
  match d with
  | Eq -> check_equal g l r
  | Le -> check_smaller g false l r
  | Lt -> check_smaller g true l r

let check_constraints c g =
  Constraint.for_all (check_constraint g) c

(* let check_constraints_key = Profile.declare_profile "check_constraints";; *)
(* let check_constraints = *)
(*   Profile.profile2 check_constraints_key check_constraints *)

let enforce_univ_constraint (u,d,v) =
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v
  | Lt -> enforce_leq (super u) v

let subst_univs_constraints subst csts =
  Constraint.fold 
    (fun c -> Option.fold_right enforce_univ_constraint (subst_univs_constraint subst c))
    csts Constraint.empty 

(* let subst_univs_constraints_key = Profile.declare_profile "subst_univs_constraints";; *)
(* let subst_univs_constraints = *)
(*   Profile.profile2 subst_univs_constraints_key subst_univs_constraints *)

let subst_univs_universe_constraints subst csts =
  UniverseConstraints.fold 
    (fun c -> Option.fold_right UniverseConstraints.add (subst_univs_universe_constraint subst c))
    csts UniverseConstraints.empty 

(* let subst_univs_universe_constraints_key = Profile.declare_profile "subst_univs_universe_constraints";; *)
(* let subst_univs_universe_constraints = *)
(*   Profile.profile2 subst_univs_universe_constraints_key subst_univs_universe_constraints *)

(** Substitute instance inst for ctx in csts *)
let instantiate_univ_context subst (_, csts) = 
  subst_univs_constraints (make_subst subst) csts

let check_consistent_constraints (ctx,cstrs) cstrs' =
  (* TODO *) ()

let to_constraints g s = 
  let rec tr (x,d,y) acc =
    let add l d l' acc = Constraint.add (l,UniverseConstraints.tr_dir d,l') acc in
      match Universe.level x, d, Universe.level y with
      | Some l, (ULe | UEq | ULub), Some l' -> add l d l' acc
      | None, ULe, Some l' -> enforce_leq x y acc
      | _, ULub, _ -> acc
      | _, d, _ -> 
	let f = if d == ULe then check_leq else check_eq in
	  if f g x y then acc else 
	    raise (Invalid_argument 
		   "to_constraints: non-trivial algebraic constraint between universes")
  in UniverseConstraints.fold tr s Constraint.empty
     

(* Normalization *)

let lookup_level u g =
  try Some (LMap.find u g) with Not_found -> None

(** [normalize_universes g] returns a graph where all edges point
    directly to the canonical representent of their target. The output
    graph should be equivalent to the input graph from a logical point
    of view, but optimized. We maintain the invariant that the key of
    a [Canonical] element is its own name, by keeping [Equiv] edges
    (see the assertion)... I (Stéphane Glondu) am not sure if this
    plays a role in the rest of the module. *)
let normalize_universes g =
  let rec visit u arc cache = match lookup_level u cache with
    | Some x -> x, cache
    | None -> match Lazy.force arc with
    | None ->
      u, LMap.add u u cache
    | Some (Canonical {univ=v; lt=_; le=_}) ->
      v, LMap.add u v cache
    | Some (Equiv v) ->
      let v, cache = visit v (lazy (lookup_level v g)) cache in
      v, LMap.add u v cache
  in
  let cache = LMap.fold
    (fun u arc cache -> snd (visit u (Lazy.lazy_from_val (Some arc)) cache))
    g LMap.empty
  in
  let repr x = LMap.find x cache in
  let lrepr us = List.fold_left
    (fun e x -> LSet.add (repr x) e) LSet.empty us
  in
  let canonicalize u = function
    | Equiv _ -> Equiv (repr u)
    | Canonical {univ=v; lt=lt; le=le; rank=rank} ->
      assert (u == v);
      (* avoid duplicates and self-loops *)
      let lt = lrepr lt and le = lrepr le in
      let le = LSet.filter
        (fun x -> x != u && not (LSet.mem x lt)) le
      in
      LSet.iter (fun x -> assert (x != u)) lt;
      Canonical {
        univ = v;
        lt = LSet.elements lt;
        le = LSet.elements le;
	rank = rank
      }
  in
  LMap.mapi canonicalize g

(** [check_sorted g sorted]: [g] being a universe graph, [sorted]
    being a map to levels, checks that all constraints in [g] are
    satisfied in [sorted]. *)
let check_sorted g sorted =
  let get u = try LMap.find u sorted with
    | Not_found -> assert false
  in
  let iter u arc =
    let lu = get u in match arc with
    | Equiv v -> assert (Int.equal lu (get v))
    | Canonical {univ = u'; lt = lt; le = le} ->
      assert (u == u');
      List.iter (fun v -> assert (lu <= get v)) le;
      List.iter (fun v -> assert (lu < get v)) lt
  in
  LMap.iter iter g

(**
  Bellman-Ford algorithm with a few customizations:
    - [weight(eq|le) = 0], [weight(lt) = -1]
    - a [le] edge is initially added from [bottom] to all other
      vertices, and [bottom] is used as the source vertex
*)
let bellman_ford bottom g =
  let () = match lookup_level bottom g with
  | None -> ()
  | Some _ -> assert false
  in
  let ( << ) a b = match a, b with
    | _, None -> true
    | None, _ -> false
    | Some x, Some y -> x < y
  and ( ++ ) a y = match a with
    | None -> None
    | Some x -> Some (x-y)
  and push u x m = match x with
    | None -> m
    | Some y -> LMap.add u y m
  in
  let relax u v uv distances =
    let x = lookup_level u distances ++ uv in
    if x << lookup_level v distances then push v x distances
    else distances
  in
  let init = LMap.add bottom 0 LMap.empty in
  let vertices = LMap.fold (fun u arc res ->
    let res = LSet.add u res in
    match arc with
      | Equiv e -> LSet.add e res
      | Canonical {univ=univ; lt=lt; le=le} ->
        assert (u == univ);
        let add res v = LSet.add v res in
        let res = List.fold_left add res le in
        let res = List.fold_left add res lt in
        res) g LSet.empty
  in
  let g =
    let node = Canonical {
      univ = bottom;
      lt = [];
      le = LSet.elements vertices;
      rank = 0
    } in LMap.add bottom node g
  in
  let rec iter count accu =
    if count <= 0 then
      accu
    else
      let accu = LMap.fold (fun u arc res -> match arc with
        | Equiv e -> relax e u 0 (relax u e 0 res)
        | Canonical {univ=univ; lt=lt; le=le} ->
          assert (u == univ);
          let res = List.fold_left (fun res v -> relax u v 0 res) res le in
          let res = List.fold_left (fun res v -> relax u v 1 res) res lt in
          res) g accu
      in iter (count-1) accu
  in
  let distances = iter (LSet.cardinal vertices) init in
  let () = LMap.iter (fun u arc ->
    let lu = lookup_level u distances in match arc with
      | Equiv v ->
        let lv = lookup_level v distances in
        assert (not (lu << lv) && not (lv << lu))
      | Canonical {univ=univ; lt=lt; le=le} ->
        assert (u == univ);
        List.iter (fun v -> assert (not (lu ++ 0 << lookup_level v distances))) le;
        List.iter (fun v -> assert (not (lu ++ 1 << lookup_level v distances))) lt) g
  in distances

(** [sort_universes g] builds a map from universes in [g] to natural
    numbers. It outputs a graph containing equivalence edges from each
    level appearing in [g] to [Type.n], and [lt] edges between the
    [Type.n]s. The output graph should imply the input graph (and the
    implication will be strict most of the time), but is not
    necessarily minimal. Note: the result is unspecified if the input
    graph already contains [Type.n] nodes (calling a module Type is
    probably a bad idea anyway). *)
let sort_universes orig =
  let mp = Names.DirPath.make [Names.Id.of_string "Type"] in
  let rec make_level accu g i =
    let type0 = Level.make mp i in
    let distances = bellman_ford type0 g in
    let accu, continue = LMap.fold (fun u x (accu, continue) ->
      let continue = continue || x < 0 in
      let accu =
        if Int.equal x 0 && u != type0 then LMap.add u i accu
        else accu
      in accu, continue) distances (accu, false)
    in
    let filter x = not (LMap.mem x accu) in
    let push g u =
      if LMap.mem u g then g else LMap.add u (Equiv u) g
    in
    let g = LMap.fold (fun u arc res -> match arc with
      | Equiv v as x ->
        begin match filter u, filter v with
          | true, true -> LMap.add u x res
          | true, false -> push res u
          | false, true -> push res v
          | false, false -> res
        end
      | Canonical {univ=v; lt=lt; le=le; rank=r} ->
        assert (u == v);
        if filter u then
          let lt = List.filter filter lt in
          let le = List.filter filter le in
          LMap.add u (Canonical {univ=u; lt=lt; le=le; rank=r}) res
        else
          let res = List.fold_left (fun g u -> if filter u then push g u else g) res lt in
          let res = List.fold_left (fun g u -> if filter u then push g u else g) res le in
          res) g LMap.empty
    in
    if continue then make_level accu g (i+1) else i, accu
  in
  let max, levels = make_level LMap.empty orig 0 in
  (* defensively check that the result makes sense *)
  check_sorted orig levels;
  let types = Array.init (max+1) (fun x -> Level.make mp x) in
  let g = LMap.map (fun x -> Equiv types.(x)) levels in
  let g =
    let rec aux i g =
      if i < max then
        let u = types.(i) in
        let g = LMap.add u (Canonical {
          univ = u;
          le = [];
          lt = [types.(i+1)];
	  rank = 1
        }) g in aux (i+1) g
      else g
    in aux 0 g
  in g

(**********************************************************************)
(* Tools for sort-polymorphic inductive types                         *)

(* Miscellaneous functions to remove or test local univ assumed to
   occur only in the le constraints *)

let remove_large_constraint u v min = 
  match Universe.level v with
  | Some u' -> if Level.eq u u' then min else v
  | None -> Huniv.remove (Hunivelt.make (Universe.Expr.make u)) v

(* [is_direct_constraint u v] if level [u] is a member of universe [v] *)
let is_direct_constraint u v =
  match Universe.level v with
  | Some u' -> Level.eq u u'
  | None -> Huniv.mem (Hunivelt.make (Universe.Expr.make u)) v

(*
   Solve a system of universe constraint of the form

   u_s11, ..., u_s1p1, w1 <= u1
   ...
   u_sn1, ..., u_snpn, wn <= un

where

  - the ui (1 <= i <= n) are universe variables,
  - the sjk select subsets of the ui for each equations,
  - the wi are arbitrary complex universes that do not mention the ui.
*)

let is_direct_sort_constraint s v = match s with
  | Some u -> is_direct_constraint u v
  | None -> false

let solve_constraints_system levels level_bounds level_min =
  let levels =
    Array.map (Option.map (fun u -> match level u with Some u -> u | _ -> anomaly (Pp.str"expects Atom")))
      levels in
  let v = Array.copy level_bounds in
  let nind = Array.length v in
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && is_direct_sort_constraint levels.(j) v.(i) then
	(v.(i) <- Universe.sup v.(i) level_bounds.(j);
	 level_min.(i) <- Universe.sup level_min.(i) level_min.(j))
    done;
    for j=0 to nind-1 do
      match levels.(j) with
      | Some u -> v.(i) <- remove_large_constraint u v.(i) level_min.(i)
      | None -> ()
    done
  done;
  v

let subst_large_constraint u u' v =
  match level u with
  | Some u ->
      if is_direct_constraint u v then 
	Universe.sup u' (remove_large_constraint u v type0m_univ)
      else v
  | _ ->
      anomaly (Pp.str "expect a universe level")

let subst_large_constraints =
  List.fold_right (fun (u,u') -> subst_large_constraint u u')

let no_upper_constraints u cst =
  match level u with
  | Some u ->
    let test (u1, _, _) =
      not (Int.equal (Level.compare u1 u) 0) in
    Constraint.for_all test cst
  | _ -> anomaly (Pp.str "no_upper_constraints")

(* Is u mentionned in v (or equals to v) ? *)

let univ_depends u v =
  match atom u with
    | Some u -> Huniv.mem u v
    | _ -> anomaly (Pp.str"univ_depends given a non-atomic 1st arg")

let constraints_of_universes g =
  let constraints_of u v acc =
    match v with
    | Canonical {univ=u; lt=lt; le=le} ->
      let acc = List.fold_left (fun acc v -> Constraint.add (u,Lt,v) acc) acc lt in
      let acc = List.fold_left (fun acc v -> Constraint.add (u,Le,v) acc) acc le in
	acc
    | Equiv v -> Constraint.add (u,Eq,v) acc
  in
    LMap.fold constraints_of g Constraint.empty

(* Pretty-printing *)

let pr_arc = function
  | _, Canonical {univ=u; lt=[]; le=[]} ->
      mt ()
  | _, Canonical {univ=u; lt=lt; le=le} ->
      let opt_sep = match lt, le with
      | [], _ | _, [] -> mt ()
      | _ -> spc ()
      in
      Level.pr u ++ str " " ++
      v 0
        (pr_sequence (fun v -> str "< " ++ Level.pr v) lt ++
	 opt_sep ++
         pr_sequence (fun v -> str "<= " ++ Level.pr v) le) ++
      fnl ()
  | u, Equiv v ->
      Level.pr u  ++ str " = " ++ Level.pr v ++ fnl ()

let pr_universes g =
  let graph = LMap.fold (fun u a l -> (u,a)::l) g [] in
  prlist pr_arc graph

(* Dumping constraints to a file *)

let dump_universes output g =
  let dump_arc u = function
    | Canonical {univ=u; lt=lt; le=le} ->
	let u_str = Level.to_string u in
	List.iter (fun v -> output Lt u_str (Level.to_string v)) lt;
	List.iter (fun v -> output Le u_str (Level.to_string v)) le
    | Equiv v ->
      output Eq (Level.to_string u) (Level.to_string v)
  in
    LMap.iter dump_arc g

module Huniverse_set = 
  Hashcons.Make(
    struct
      type t = universe_set
      type u = universe_level -> universe_level
      let hashcons huc s =
	LSet.fold (fun x -> LSet.add (huc x)) s LSet.empty
      let equal s s' =
	LSet.equal s s'
      let hash = Hashtbl.hash
    end)

let hcons_universe_set = 
  Hashcons.simple_hcons Huniverse_set.generate Level.hcons

let hcons_universe_context_set (v, c) = 
  (hcons_universe_set v, hcons_constraints c)


let hcons_univlevel = Level.hcons
let hcons_univ x = x (* Universe.hcons (Huniv.node x) *)
let equal_universes = Universe.equal_universes

let explain_universe_inconsistency (o,u,v,p) =
    let pr_rel = function
      | Eq -> str"=" | Lt -> str"<" | Le -> str"<=" 
    in
    let reason = match p with
	[] -> mt()
      | _::_ ->
	str " because" ++ spc() ++ pr_uni v ++
	  prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ pr_uni v)
	  p ++
	  (if Universe.eq (snd (List.last p)) u then mt() else
	      (spc() ++ str "= " ++ pr_uni u)) 
    in
      str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
        pr_rel o ++ spc() ++ pr_uni v ++ reason ++ str")"
