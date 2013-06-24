(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* File initially created by G�rard Huet and Thierry Coquand in 1984 *)
(* Extension to inductive constructions by Christine Paulin for Coq V5.6 *)
(* Extension to mutual inductive constructions by Christine Paulin for
   Coq V5.10.2 *)
(* Extension to co-inductive constructions by Eduardo Gimenez *)
(* Optimization of substitution functions by Chet Murthy *)
(* Optimization of lifting functions by Bruno Barras, Mar 1997 *)
(* Hash-consing by Bruno Barras in Feb 1998 *)
(* Restructuration of Coq of the type-checking kernel by Jean-Christophe 
   Filli�tre, 1999 *)
(* Abstraction of the syntax of terms and iterators by Hugo Herbelin, 2000 *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)

(* This file defines the internal syntax of the Calculus of
   Inductive Constructions (CIC) terms together with constructors,
   destructors, iterators and basic functions *)

open Errors
open Util
open Pp
open Names
open Univ
open Esubst


type existential_key = int
type metavariable = int

(* This defines the strategy to use for verifiying a Cast *)
(* Warning: REVERTcast is not exported to vo-files; as of r14492, it has to *)
(* come after the vo-exported cast_kind so as to be compatible with coqchk *)
type cast_kind = VMcast | NATIVEcast | DEFAULTcast | REVERTcast

(* This defines Cases annotations *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
type case_printing =
  { ind_nargs : int; (* length of the arity of the inductive type *)
    style     : case_style }
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (* number of pattern vars of each constructor *)
    ci_pp_info    : case_printing (* not interpreted by the kernel *)
  }

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr array
type ('constr, 'types) prec_declaration =
    Name.t array * 'types array * 'constr array
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration
type 'a puniverses = 'a Univ.puniverses
type pconstant = constant puniverses
type pinductive = inductive puniverses
type pconstructor = constructor puniverses

(* [Var] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)
type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of Sorts.t
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of pconstant
  | Ind       of pinductive
  | Construct of pconstructor
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of constant * 'constr
(* constr is the fixpoint of the previous type. Requires option
   -rectypes of the Caml compiler to be set *)
type t = (t,t) kind_of_term
type constr = t

type existential = existential_key * constr array
type rec_declaration = Name.t array * constr array * constr array
type fixpoint = (int array * int) * rec_declaration
type cofixpoint = int * rec_declaration

type types = constr

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index with number n *)
let rels =
  [|Rel  1;Rel  2;Rel  3;Rel  4;Rel  5;Rel  6;Rel  7; Rel  8;
    Rel  9;Rel 10;Rel 11;Rel 12;Rel 13;Rel 14;Rel 15; Rel 16|]

let mkRel n = if 0<n & n<=16 then rels.(n-1) else Rel n

(* Construct a type *)
let mkProp   = Sort Sorts.prop
let mkSet    = Sort Sorts.set
let mkType u = Sort (Sorts.Type u)
let mkSort   = function
  | Sorts.Prop Sorts.Null -> mkProp (* Easy sharing *)
  | Sorts.Prop Sorts.Pos -> mkSet
  | s -> Sort s

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast (t1,k2,t2) =
  match t1 with
  | Cast (c,k1, _) when (k1 == VMcast || k1 == NATIVEcast) && k1 == k2 -> Cast (c,k1,t2)
  | _ -> Cast (t1,k2,t2)

(* Constructs the product (x:t1)t2 *)
let mkProd (x,t1,t2) = Prod (x,t1,t2)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda (x,t1,t2) = Lambda (x,t1,t2)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn (x,c1,t,c2) = LetIn (x,c1,t,c2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
(* We ensure applicative terms have at least one argument and the
   function is not itself an applicative term *)
let mkApp (f, a) =
  if Int.equal (Array.length a) 0 then f else
    match f with
      | App (g, cl) -> App (g, Array.append cl a)
      | _ -> App (f, a)

let out_punivs (a, _) = a
let map_puniverses f (x,u) = (f x, u)
let in_punivs a = (a, Instance.empty)

(* Constructs a constant *)
let mkConst c = Const (in_punivs c)
let mkConstU c = Const c

(* Constructs an applied projection *)
let mkProj (p,c) = Proj (p,c)

(* Constructs an existential variable *)
let mkEvar e = Evar e

(* Constructs the ith (co)inductive type of the block named kn *)
let mkInd m = Ind (in_punivs m)
let mkIndU m = Ind m

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. *)
let mkConstruct c = Construct (in_punivs c)
let mkConstructU c = Construct c
let mkConstructUi ((ind,u),i) = Construct ((ind,i),u)

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkCase (ci, p, c, ac) = Case (ci, p, c, ac)

(* If recindxs = [|i1,...in|]
      funnames = [|f1,...fn|]
      typarray = [|t1,...tn|]
      bodies   = [|b1,...bn|]
   then

      mkFix ((recindxs,i),(funnames,typarray,bodies))

   constructs the ith function of the block

    Fixpoint f1 [ctx1] : t1 := b1
    with     f2 [ctx2] : t2 := b2
    ...
    with     fn [ctxn] : tn := bn.

   where the length of the jth context is ij.
*)

let mkFix fix = Fix fix

(* If funnames = [|f1,...fn|]
      typarray = [|t1,...tn|]
      bodies   = [|b1,...bn|]
   then

      mkCoFix (i,(funnames,typsarray,bodies))

   constructs the ith function of the block

    CoFixpoint f1 : t1 := b1
    with       f2 : t2 := b2
    ...
    with       fn : tn := bn.
*)
let mkCoFix cofix= CoFix cofix

(* Constructs an existential variable named "?n" *)
let mkMeta  n =  Meta n

(* Constructs a Variable named id *)
let mkVar id = Var id


(************************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(************************************************************************)

(* User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

let kind c = c

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let fold f acc c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> acc
  | Cast (c,_,t) -> f (f acc c) t
  | Prod (_,t,c) -> f (f acc t) c
  | Lambda (_,t,c) -> f (f acc t) c
  | LetIn (_,b,t,c) -> f (f (f acc b) t) c
  | App (c,l) -> Array.fold_left f (f acc c) l
  | Proj (p,c) -> f acc c
  | Evar (_,l) -> Array.fold_left f acc l
  | Case (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let fd = Array.map3 (fun na t b -> (na,t,b)) lna tl bl in
      Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let fd = Array.map3 (fun na t b -> (na,t,b)) lna tl bl in
      Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd

(* [iter f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f c; f t
  | Prod (_,t,c) -> f t; f c
  | Lambda (_,t,c) -> f t; f c
  | LetIn (_,b,t,c) -> f b; f t; f c
  | App (c,l) -> f c; Array.iter f l
  | Proj (p,c) -> f c
  | Evar (_,l) -> Array.iter f l
  | Case (_,p,c,bl) -> f p; f c; Array.iter f bl
  | Fix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | CoFix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl

(* [iter_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_with_binders g f n c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (_,t,c) -> f n t; f (g n) c
  | Lambda (_,t,c) -> f n t; f (g n) c
  | LetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | App (c,l) -> f n c; Array.iter (f n) l
  | Proj (p,c) -> f n c
  | Evar (_,l) -> Array.iter (f n) l
  | Case (_,p,c,bl) -> f n p; f n c; Array.iter (f n) bl
  | Fix (_,(_,tl,bl)) ->
      Array.iter (f n) tl;
      Array.iter (f (iterate g (Array.length tl) n)) bl
  | CoFix (_,(_,tl,bl)) ->
      Array.iter (f n) tl;
      Array.iter (f (iterate g (Array.length tl) n)) bl

(* [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let map f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,k,t) -> mkCast (f c, k, f t)
  | Prod (na,t,c) -> mkProd (na, f t, f c)
  | Lambda (na,t,c) -> mkLambda (na, f t, f c)
  | LetIn (na,b,t,c) -> mkLetIn (na, f b, f t, f c)
  | App (c,l) -> mkApp (f c, Array.map f l)
  | Proj (p,c) -> mkProj (p, f c)
  | Evar (e,l) -> mkEvar (e, Array.map f l)
  | Case (ci,p,c,bl) -> mkCase (ci, f p, f c, Array.map f bl)
  | Fix (ln,(lna,tl,bl)) ->
      mkFix (ln,(lna,Array.map f tl,Array.map f bl))
  | CoFix(ln,(lna,tl,bl)) ->
      mkCoFix (ln,(lna,Array.map f tl,Array.map f bl))

(* [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_with_binders g f l c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (c,k,t) -> mkCast (f l c, k, f l t)
  | Prod (na,t,c) -> mkProd (na, f l t, f (g l) c)
  | Lambda (na,t,c) -> mkLambda (na, f l t, f (g l) c)
  | LetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g l) c)
  | App (c,al) -> mkApp (f l c, Array.map (f l) al)
  | Proj (p,c) -> mkProj (p, f l c)
  | Evar (e,al) -> mkEvar (e, Array.map (f l) al)
  | Case (ci,p,c,bl) -> mkCase (ci, f l p, f l c, Array.map (f l) bl)
  | Fix (ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | CoFix(ln,(lna,tl,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkCoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))

(* [compare_head_gen u s f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed, [u] to compare universe
   instances and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)

let compare_head_gen eq_universes eq_sorts f t1 t2 =
  match kind t1, kind t2 with
  | Rel n1, Rel n2 -> Int.equal n1 n2
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Sort s1, Sort s2 -> eq_sorts s1 s2
  | Cast (c1,_,_), _ -> f c1 t2
  | _, Cast (c2,_,_) -> f t1 c2
  | Prod (_,t1,c1), Prod (_,t2,c2) -> f t1 t2 && f c1 c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) -> f t1 t2 && f c1 c2
  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> f b1 b2 && f t1 t2 && f c1 c2
  | App (Cast(c1, _, _),l1), _ -> f (mkApp (c1,l1)) t2
  | _, App (Cast (c2, _, _),l2) -> f t1 (mkApp (c2,l2))
  | App (c1,l1), App (c2,l2) ->
    Int.equal (Array.length l1) (Array.length l2) &&
      f c1 c2 && Array.equal f l1 l2
  | Proj (p1,c1), Proj (p2,c2) -> eq_constant p1 p2 && f c1 c2
  | Evar (e1,l1), Evar (e2,l2) -> Int.equal e1 e2 && Array.equal f l1 l2
  | Const (c1,u1), Const (c2,u2) -> eq_constant c1 c2 && eq_universes true u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> eq_ind c1 c2 && eq_universes false u1 u2
  | Construct (c1,u1), Construct (c2,u2) -> eq_constructor c1 c2 && eq_universes false u1 u2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
      f p1 p2 & f c1 c2 && Array.equal f bl1 bl2
  | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) ->
      Int.equal i1 i2 && Array.equal Int.equal ln1 ln2
      && Array.equal f tl1 tl2 && Array.equal f bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      Int.equal ln1 ln2 && Array.equal f tl1 tl2 && Array.equal f bl1 bl2
  | _ -> false

let compare_head = compare_head_gen (fun _ -> Univ.Instance.eq) Sorts.equal

(* [compare_head_gen_leq u s sl eq leq c1 c2] compare [c1] and [c2] using [eq] to compare
   the immediate subterms of [c1] of [c2] for conversion if needed, [leq] for cumulativity,
   [u] to compare universe instances and [s] to compare sorts; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)

let compare_head_gen_leq eq_universes eq_sorts leq_sorts eq leq t1 t2 =
  match kind t1, kind t2 with
  | Rel n1, Rel n2 -> Int.equal n1 n2
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Int.equal (id_ord id1 id2) 0
  | Sort s1, Sort s2 -> leq_sorts s1 s2
  | Cast (c1,_,_), _ -> leq c1 t2
  | _, Cast (c2,_,_) -> leq t1 c2
  | Prod (_,t1,c1), Prod (_,t2,c2) -> eq t1 t2 && leq c1 c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) -> eq t1 t2 && eq c1 c2
  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> eq b1 b2 && eq t1 t2 && leq c1 c2
  | App (Cast(c1, _, _),l1), _ -> leq (mkApp (c1,l1)) t2
  | _, App (Cast (c2, _, _),l2) -> leq t1 (mkApp (c2,l2))
  | App (c1,l1), App (c2,l2) ->
    Int.equal (Array.length l1) (Array.length l2) &&
      eq c1 c2 && Array.equal eq l1 l2
  | Evar (e1,l1), Evar (e2,l2) -> Int.equal e1 e2 && Array.equal eq l1 l2
  | Const (c1,u1), Const (c2,u2) -> eq_constant c1 c2 && eq_universes true u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> eq_ind c1 c2 && eq_universes false u1 u2
  | Construct (c1,u1), Construct (c2,u2) -> eq_constructor c1 c2 && eq_universes false u1 u2
  | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
      eq p1 p2 & eq c1 c2 && Array.equal eq bl1 bl2
  | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) ->
      Int.equal i1 i2 && Array.equal Int.equal ln1 ln2
      && Array.equal eq tl1 tl2 && Array.equal eq bl1 bl2
  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      Int.equal ln1 ln2 && Array.equal eq tl1 tl2 && Array.equal eq bl1 bl2
  | _ -> false

(*******************************)
(*  alpha conversion functions *)
(*******************************)

(* alpha conversion : ignore print names and casts *)

let rec eq_constr m n =
  (m == n) || compare_head_gen (fun _ -> Instance.eq) Sorts.equal eq_constr m n

(** Strict equality of universe instances. *)
let compare_constr = compare_head_gen (fun _ -> Instance.eq) Sorts.equal

let equal m n = eq_constr m n (* to avoid tracing a recursive fun *)

let eq_constr_univs univs m n =
  if m == n then true
  else 
    let eq_universes _ = Univ.Instance.check_eq univs in
    let eq_sorts s1 s2 = Univ.check_eq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let rec eq_constr' m n = 
      m == n ||	compare_head_gen eq_universes eq_sorts eq_constr' m n
    in compare_head_gen eq_universes eq_sorts eq_constr' m n

let leq_constr_univs univs m n =
  if m == n then true
  else 
    let eq_universes _ = Univ.Instance.check_eq univs in
    let eq_sorts s1 s2 = Univ.check_eq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let leq_sorts s1 s2 = Univ.check_leq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let rec eq_constr' m n = 
      m == n ||	compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let rec compare_leq m n =
      compare_head_gen_leq eq_universes eq_sorts leq_sorts eq_constr' leq_constr' m n
    and leq_constr' m n = m == n || compare_leq m n in
      compare_leq m n

let eq_constr_universes m n =
  if m == n then true, UniverseConstraints.empty
  else 
    let cstrs = ref UniverseConstraints.empty in
    let eq_universes strict l l' = 
      cstrs := Univ.enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      cstrs := Univ.UniverseConstraints.add 
	(Sorts.univ_of_sort s1, Univ.UEq, Sorts.univ_of_sort s2) !cstrs;
      true
    in
    let rec eq_constr' m n = 
      m == n ||	compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let res = compare_head_gen eq_universes eq_sorts eq_constr' m n in
      res, !cstrs

let leq_constr_universes m n =
  if m == n then true, UniverseConstraints.empty
  else 
    let cstrs = ref UniverseConstraints.empty in
    let eq_universes strict l l' = 
      cstrs := Univ.enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      cstrs := Univ.UniverseConstraints.add 
	(Sorts.univ_of_sort s1,Univ.UEq,Sorts.univ_of_sort s2) !cstrs; true
    in
    let leq_sorts s1 s2 = 
      cstrs := Univ.UniverseConstraints.add 
	(Sorts.univ_of_sort s1,Univ.ULe,Sorts.univ_of_sort s2) !cstrs; true
    in
    let rec eq_constr' m n = 
      m == n ||	compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let rec compare_leq m n =
      compare_head_gen_leq eq_universes eq_sorts leq_sorts eq_constr' leq_constr' m n
    and leq_constr' m n = m == n || compare_leq m n in
    let res = compare_leq m n in
      res, !cstrs

let always_true _ _ = true

let rec eq_constr_nounivs m n =
  (m == n) || compare_head_gen (fun _ -> always_true) always_true eq_constr_nounivs m n

let constr_ord_int f t1 t2 =
  let (=?) f g i1 i2 j1 j2=
    let c = f i1 i2 in
    if Int.equal c 0 then g j1 j2 else c in
  let (==?) fg h i1 i2 j1 j2 k1 k2=
    let c=fg i1 i2 j1 j2 in
    if Int.equal c 0 then h k1 k2 else c in
  let fix_cmp (a1, i1) (a2, i2) =
    ((Array.compare Int.compare) =? Int.compare) a1 a2 i1 i2
  in
  match kind t1, kind t2 with
    | Rel n1, Rel n2 -> Int.compare n1 n2
    | Meta m1, Meta m2 -> Int.compare m1 m2
    | Var id1, Var id2 -> Id.compare id1 id2
    | Sort s1, Sort s2 -> Sorts.compare s1 s2
    | Cast (c1,_,_), _ -> f c1 t2
    | _, Cast (c2,_,_) -> f t1 c2
    | Prod (_,t1,c1), Prod (_,t2,c2)
    | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
        (f =? f) t1 t2 c1 c2
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) ->
        ((f =? f) ==? f) b1 b2 t1 t2 c1 c2
    | App (Cast(c1,_,_),l1), _ -> f (mkApp (c1,l1)) t2
    | _, App (Cast(c2, _,_),l2) -> f t1 (mkApp (c2,l2))
    | App (c1,l1), App (c2,l2) -> (f =? (Array.compare f)) c1 c2 l1 l2
    | Proj (p1,c1), Proj (p2,c2) -> (con_ord =? f) p1 p2 c1 c2
    | Evar (e1,l1), Evar (e2,l2) ->
        ((-) =? (Array.compare f)) e1 e2 l1 l2
    | Const (c1,u1), Const (c2,u2) -> con_ord c1 c2
    | Ind (ind1, u1), Ind (ind2, u2) -> ind_ord ind1 ind2
    | Construct (ct1,u1), Construct (ct2,u2) -> constructor_ord ct1 ct2
    | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
        ((f =? f) ==? (Array.compare f)) p1 p2 c1 c2 bl1 bl2
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
        ((fix_cmp =? (Array.compare f)) ==? (Array.compare f))
        ln1 ln2 tl1 tl2 bl1 bl2
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
        ((Int.compare =? (Array.compare f)) ==? (Array.compare f))
        ln1 ln2 tl1 tl2 bl1 bl2
    | t1, t2 -> Pervasives.compare t1 t2

let rec compare m n=
  constr_ord_int compare m n

(*******************)
(*  hash-consing   *)
(*******************)

(* Hash-consing of [constr] does not use the module [Hashcons] because
   [Hashcons] is not efficient on deep tree-like data
   structures. Indeed, [Hashcons] is based the (very efficient)
   generic hash function [Hashtbl.hash], which computes the hash key
   through a depth bounded traversal of the data structure to be
   hashed. As a consequence, for a deep [constr] like the natural
   number 1000 (S (S (... (S O)))), the same hash is assigned to all
   the sub [constr]s greater than the maximal depth handled by
   [Hashtbl.hash]. This entails a huge number of collisions in the
   hash table and leads to cubic hash-consing in this worst-case.

   In order to compute a hash key that is independent of the data
   structure depth while being constant-time, an incremental hashing
   function must be devised. A standard implementation creates a cache
   of the hashing function by decorating each node of the hash-consed
   data structure with its hash key. In that case, the hash function
   can deduce the hash key of a toplevel data structure by a local
   computation based on the cache held on its substructures.
   Unfortunately, this simple implementation introduces a space
   overhead that is damageable for the hash-consing of small [constr]s
   (the most common case). One can think of an heterogeneous
   distribution of caches on smartly chosen nodes, but this is forbidden
   by the use of generic equality in Coq source code. (Indeed, this forces
   each [constr] to have a unique canonical representation.)

   Given that hash-consing proceeds inductively, we can nonetheless
   computes the hash key incrementally during hash-consing by changing
   a little the signature of the hash-consing function: it now returns
   both the hash-consed term and its hash key. This simple solution is
   implemented in the following code: it does not introduce a space
   overhead in [constr], that's why the efficiency is unchanged for
   small [constr]s. Besides, it does handle deep [constr]s without
   introducing an unreasonable number of collisions in the hash table.
   Some benchmarks make us think that this implementation of
   hash-consing is linear in the size of the hash-consed data
   structure for our daily use of Coq.
*)

let array_eqeq t1 t2 =
  t1 == t2 ||
  (Int.equal (Array.length t1) (Array.length t2) &&
   let rec aux i =
     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
   in aux 0)

let hasheq t1 t2 =
  match t1, t2 with
    | Rel n1, Rel n2 -> n1 == n2
    | Meta m1, Meta m2 -> m1 == m2
    | Var id1, Var id2 -> id1 == id2
    | Sort s1, Sort s2 -> s1 == s2
    | Cast (c1,k1,t1), Cast (c2,k2,t2) -> c1 == c2 & k1 == k2 & t1 == t2
    | Prod (n1,t1,c1), Prod (n2,t2,c2) -> n1 == n2 & t1 == t2 & c1 == c2
    | Lambda (n1,t1,c1), Lambda (n2,t2,c2) -> n1 == n2 & t1 == t2 & c1 == c2
    | LetIn (n1,b1,t1,c1), LetIn (n2,b2,t2,c2) ->
      n1 == n2 & b1 == b2 & t1 == t2 & c1 == c2
    | App (c1,l1), App (c2,l2) -> c1 == c2 & array_eqeq l1 l2
    | Proj (p1,c1), Proj (p2,c2) -> p1 == p2 & c1 == c2
    | Evar (e1,l1), Evar (e2,l2) -> Int.equal e1 e2 & array_eqeq l1 l2
    | Const (c1,u1), Const (c2,u2) -> c1 == c2 && Univ.Instance.eqeq u1 u2
    | Ind ((sp1,i1),u1), Ind ((sp2,i2),u2) -> 
      sp1 == sp2 & Int.equal i1 i2 & Univ.Instance.eqeq u1 u2
    | Construct (((sp1,i1),j1),u1), Construct (((sp2,i2),j2),u2) ->
      sp1 == sp2 & Int.equal i1 i2 & Int.equal j1 j2 & Univ.Instance.eqeq u1 u2
    | Case (ci1,p1,c1,bl1), Case (ci2,p2,c2,bl2) ->
      ci1 == ci2 & p1 == p2 & c1 == c2 & array_eqeq bl1 bl2
    | Fix ((ln1, i1),(lna1,tl1,bl1)), Fix ((ln2, i2),(lna2,tl2,bl2)) ->
      Int.equal i1 i2
      && Array.equal Int.equal ln1 ln2
      && array_eqeq lna1 lna2
      && array_eqeq tl1 tl2
      && array_eqeq bl1 bl2
    | CoFix(ln1,(lna1,tl1,bl1)), CoFix(ln2,(lna2,tl2,bl2)) ->
      Int.equal ln1 ln2
      & array_eqeq lna1 lna2
      & array_eqeq tl1 tl2
      & array_eqeq bl1 bl2
    | _ -> false

(** Note that the following Make has the side effect of creating
    once and for all the table we'll use for hash-consing all constr *)

module HashsetTerm = Hashset.Make(struct type t = constr let equal = hasheq end)

let term_table = HashsetTerm.create 19991
(* The associative table to hashcons terms. *)

open Hashset.Combine

let hash_instance = Univ.Instance.hcons

(* [hashcons hash_consing_functions constr] computes an hash-consed
   representation for [constr] using [hash_consing_functions] on
   leaves. *)
let hashcons (sh_sort,sh_ci,sh_construct,sh_ind,sh_con,sh_na,sh_id) =

  (* Note : we hash-cons constr arrays *in place* *)

  let rec hash_term_array t =
    let accu = ref 0 in
    for i = 0 to Array.length t - 1 do
      let x, h = sh_rec t.(i) in
      accu := combine !accu h;
      t.(i) <- x
    done;
    !accu

  and hash_term t =
    match t with
      | Var i ->
	(Var (sh_id i), combinesmall 1 (Hashtbl.hash i))
      | Sort s ->
	(Sort (sh_sort s), combinesmall 2 (Hashtbl.hash s))
      | Cast (c, k, t) ->
	let c, hc = sh_rec c in
	let t, ht = sh_rec t in
	(Cast (c, k, t), combinesmall 3 (combine3 hc (Hashtbl.hash k) ht))
      | Prod (na,t,c) ->
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
	(Prod (sh_na na, t, c), combinesmall 4 (combine3 (Hashtbl.hash na) ht hc))
      | Lambda (na,t,c) ->
	let t, ht = sh_rec t
	and c, hc = sh_rec c in
	(Lambda (sh_na na, t, c), combinesmall 5 (combine3 (Hashtbl.hash na) ht hc))
      | LetIn (na,b,t,c) ->
	let b, hb = sh_rec b in
	let t, ht = sh_rec t in
	let c, hc = sh_rec c in
	(LetIn (sh_na na, b, t, c), combinesmall 6 (combine4 (Hashtbl.hash na) hb ht hc))
      | App (c,l) ->
	let c, hc = sh_rec c in
	let hl = hash_term_array l in
	(App (c, l), combinesmall 7 (combine hl hc))
      | Proj (p,c) ->
        let c, hc = sh_rec c in
	let p' = sh_con p in
	  (Proj (p', c), combinesmall 17 (Hashtbl.hash p'))
      | Evar (e,l) ->
	let hl = hash_term_array l in
	(* since the array have been hashed in place : *)
	(t, combinesmall 8 (combine (Hashtbl.hash e) hl))
      | Const (c,u) ->
	(Const (sh_con c, hash_instance u), combinesmall 9 (Hashtbl.hash c))
      | Ind ((kn,i) as ind,u) ->
	(Ind (sh_ind ind, hash_instance u), combinesmall 10 (combine (Hashtbl.hash kn) i))
      | Construct ((((kn,i),j) as c,u))->
	(Construct (sh_construct c, hash_instance u), 
	 combinesmall 11 (combine3 (Hashtbl.hash kn) i j))
      | Case (ci,p,c,bl) ->
	let p, hp = sh_rec p
	and c, hc = sh_rec c in
	let hbl = hash_term_array bl in
	let hbl = combine (combine hc hp) hbl in
	(Case (sh_ci ci, p, c, bl), combinesmall 12 hbl)
      | Fix (ln,(lna,tl,bl)) ->
	let hbl = hash_term_array  bl in
	let htl = hash_term_array  tl in
	Array.iteri (fun i x -> lna.(i) <- sh_na x) lna;
	(* since the three arrays have been hashed in place : *)
	(t, combinesmall 13 (combine (Hashtbl.hash lna) (combine hbl htl)))
      | CoFix(ln,(lna,tl,bl)) ->
	let hbl = hash_term_array bl in
	let htl = hash_term_array tl in
	Array.iteri (fun i x -> lna.(i) <- sh_na x) lna;
	(* since the three arrays have been hashed in place : *)
	(t, combinesmall 14 (combine (Hashtbl.hash lna) (combine hbl htl)))
      | Meta n ->
	(t, combinesmall 15 n)
      | Rel n ->
	(t, combinesmall 16 n)

  and sh_rec t =
    let (y, h) = hash_term t in
    (* [h] must be positive. *)
    let h = h land 0x3FFFFFFF in
    (HashsetTerm.repr h y term_table, h)

  in
  (* Make sure our statically allocated Rels (1 to 16) are considered
     as canonical, and hence hash-consed to themselves *)
  ignore (hash_term_array rels);

  fun t -> fst (sh_rec t)

(* Exported hashing fonction on constr, used mainly in plugins.
   Appears to have slight differences from [snd (hash_term t)] above ? *)

let rec hash t =
  match kind t with
    | Var i -> combinesmall 1 (Hashtbl.hash i)
    | Sort s -> combinesmall 2 (Hashtbl.hash s)
    | Cast (c, _, _) -> hash c
    | Prod (_, t, c) -> combinesmall 4 (combine (hash t) (hash c))
    | Lambda (_, t, c) -> combinesmall 5 (combine (hash t) (hash c))
    | LetIn (_, b, t, c) ->
      combinesmall 6 (combine3 (hash b) (hash t) (hash c))
    | App (Cast(c, _, _),l) -> hash (mkApp (c,l))
    | App (c,l) ->
      combinesmall 7 (combine (hash_term_array l) (hash c))
    | Proj (p,c) ->
      combinesmall 17 (combine (Hashtbl.hash p) (hash c))
    | Evar (e,l) ->
      combinesmall 8 (combine (Hashtbl.hash e) (hash_term_array l))
    | Const (c,u) ->
      combinesmall 9 (Hashtbl.hash c)	(* TODO: proper hash function for constants *)
    | Ind ((kn,i),u) ->
      combinesmall 10 (combine (Hashtbl.hash kn) i)
    | Construct (((kn,i),j),u) ->
      combinesmall 11 (combine3 (Hashtbl.hash kn) i j)
    | Case (_ , p, c, bl) ->
      combinesmall 12 (combine3 (hash c) (hash p) (hash_term_array bl))
    | Fix (ln ,(_, tl, bl)) ->
      combinesmall 13 (combine (hash_term_array bl) (hash_term_array tl))
    | CoFix(ln, (_, tl, bl)) ->
       combinesmall 14 (combine (hash_term_array bl) (hash_term_array tl))
    | Meta n -> combinesmall 15 n
    | Rel n -> combinesmall 16 n

and hash_term_array t =
  Array.fold_left (fun acc t -> combine (hash t) acc) 0 t

module Hsorts =
  Hashcons.Make(
    struct
      open Sorts

      type t = Sorts.t
      type u = universe -> universe
      let hashcons huniv = function
          Prop c -> Prop c
        | Type u -> Type (huniv u)
      let equal s1 s2 =
        match (s1,s2) with
            (Prop c1, Prop c2) -> c1 == c2
          | (Type u1, Type u2) -> u1 == u2
          |_ -> false
      let hash = Hashtbl.hash
    end)

module Hcaseinfo =
  Hashcons.Make(
    struct
      type t = case_info
      type u = inductive -> inductive
      let hashcons hind ci = { ci with ci_ind = hind ci.ci_ind }
      let pp_info_equal info1 info2 =
        Int.equal info1.ind_nargs info2.ind_nargs &&
        info1.style == info2.style
      let equal ci ci' =
	ci.ci_ind == ci'.ci_ind &&
	Int.equal ci.ci_npar ci'.ci_npar &&
	Array.equal Int.equal ci.ci_cstr_ndecls ci'.ci_cstr_ndecls && (* we use [Array.equal] on purpose *)
	pp_info_equal ci.ci_pp_info ci'.ci_pp_info  (* we use (=) on purpose *)
      let hash = Hashtbl.hash
    end)

let hcons_sorts = Hashcons.simple_hcons Hsorts.generate hcons_univ
let hcons_caseinfo = Hashcons.simple_hcons Hcaseinfo.generate hcons_ind

let hcons_pconstruct (c,u) = (hcons_construct c, Univ.Instance.hcons u)
let hcons_pind (i,u) = (hcons_ind i, Univ.Instance.hcons u)
let hcons_pcon (c,u) = (hcons_con c, Univ.Instance.hcons u)

let hcons =
  hashcons
    (Sorts.hcons,
     hcons_caseinfo,
     hcons_construct,
     hcons_ind,
     hcons_con,
     Name.hcons,
     Id.hcons)

(* let hcons_types = hcons_constr *)

(*******)
(* Type of abstract machine values *)
(** FIXME: nothing to do there *)
type values
