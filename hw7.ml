open List

(* identifiers and type identifiers *)
type ident = string
type tident = int
   
type exp = Var of ident | Fun of ident * exp | App of exp * exp
         | Num of int | Bool of bool | Add of exp * exp
         | Tuple of exp * exp | Fst of exp | Snd of exp
         | Inl of exp | Inr of exp | Match of exp * ident * exp * ident * exp

type typ = IntTy | BoolTy | ArrowTy of typ * typ (* ArrowTy (IntTy, BoolTy) represents int -> bool *)
         | TyVar of tident (* "unknown type" *)
         | TupleTy of typ * typ | SumTy of typ * typ


type context = ident -> typ option

let empty_context : context = fun _ -> None
let update g x t = fun y -> if y = x then Some t else g y
let lookup g x = g x

type constraints = (typ * typ) list (* (t1 = t2 -> t) represented as (t1, ArrowTy (t2, t)) *)

(* fresh tidents *)
let next : tident ref = ref 0
let fresh_tident () : tident = next := !next + 1; !next
let fresh_tyvar () : typ = TyVar (fresh_tident ())

(* constraint generation *)
let rec get_constraints (gamma : context) (e : exp) : (typ * constraints) =
  match e with
  | Num _ -> (IntTy, [])
  | Bool _ -> (BoolTy, [])
  | Var x -> (match lookup gamma x with Some t -> (t, []))

  | Fun (x, l) -> let t1 = fresh_tyvar () in
                  let (t2, s) = get_constraints (update gamma x t1) l in
                  (ArrowTy (t1, t2), s)

  | App (l1, l2) ->
     let (t1, s1) = get_constraints gamma l1 in
     let (t2, s2) = get_constraints gamma l2 in
     let t = fresh_tyvar () in
     (t, (t1, (ArrowTy (t2, t))) :: s1 @ s2)
     
  | Add (l1, l2) ->
    let (t1, s1) = get_constraints gamma l1 in
    let (t2, s2) = get_constraints gamma l2 in
    (IntTy, (t1, IntTy) :: (t2, IntTy) :: s1 @ s2)
  
  | Tuple (e1, e2) -> 
    let (t1, s1)  = get_constraints gamma e1 in
    let (t2, s2) = get_constraints gamma e2 in 
    (TupleTy (t1, t2), s1 @ s2)

  | Fst e1 -> 
    let (t, s)  = get_constraints gamma e1 in
    let t1 = fresh_tyvar() in 
    let t2 = fresh_tyvar() in
    (t1, (TupleTy (t1, t2), t) :: s)

  | Snd e2 -> 
    let (t, s)  = get_constraints gamma e2 in
    let t1 = fresh_tyvar() in 
    let t2 = fresh_tyvar() in 
    (t2, (TupleTy (t1, t2), t) :: s)

  | Inl e1 -> 
    let (t1, s) = get_constraints gamma e1 in
    let t2 = fresh_tyvar() in
    (SumTy(t1, t2), s)

  | Inr e1 -> 
    let (t2, s) = get_constraints gamma e1 in
    let t1 = fresh_tyvar() in
    (SumTy(t1, t2), s)

  | Match (e, x1, e1, x2, e2) -> 
    let (t, s) = get_constraints gamma e in
    let ta = fresh_tyvar() in
    let tb = fresh_tyvar() in
    let (t1, s1) = get_constraints (update gamma x1 ta) e1 in 
    let (t2, s2) = get_constraints (update gamma x2 tb) e2 in 
    (t1, (t, SumTy(ta, tb)) :: (t1,t2) :: s @ s1  @s2)


(* constraint solving *)
type subst = tident -> typ option
let empty_subst : subst = fun _ -> None

let rec apply_subst (s : subst) (t : typ) : typ =
  match t with
  | ArrowTy (t1, t2) -> ArrowTy (apply_subst s t1, apply_subst s t2)
  | TupleTy (t1, t2) -> TupleTy (apply_subst s t1, apply_subst s t2)
  | SumTy (t1, t2) -> SumTy (apply_subst s t1, apply_subst s t2)
  | TyVar v -> (match s v with Some t' -> t' | None -> TyVar v)
  | _ -> t

let apply_to_constraints (s : subst) (c : constraints) : constraints =
  List.map (fun (t1, t2) -> (apply_subst s t1, apply_subst s t2)) c

let compose (s1 : subst) (s2 : subst) : subst =
  fun v -> match s2 v with Some t -> Some (apply_subst s1 t) | None -> s1 v

let single_subst (x : tident) (t : typ) =
  fun v -> if v = x then Some t else None

let rec vars (t : typ) =
  match t with
  | TyVar v -> [v]
  | ArrowTy (t1, t2) -> vars t1 @ vars t2
  | _ -> []

let occurs v t = List.exists (fun x -> x = v) (vars t)

let rec unify (s : subst) (c : constraints) : subst option =
  match c with
  | [] -> Some s
  | (t1, t2) :: rest ->
    if t1 = t2 then unify s rest else
    match t1, t2 with
    | TyVar v, _ -> if occurs v t2 then None else let s1 = single_subst v t2 in
       unify (compose s1 s) (apply_to_constraints s1 rest)
    | _, TyVar v -> if occurs v t1 then None else let s1 = single_subst v t1 in
       unify (compose s1 s) (apply_to_constraints s1 rest)
    | ArrowTy (t1, t2), ArrowTy (t3, t4) -> unify s ((t1, t3) :: (t2, t4) :: rest)
    | TupleTy (t1, t2), TupleTy (t3, t4) -> unify s ((t1, t3) :: (t2, t4) :: rest)
    | SumTy (t1, t2), SumTy (t3, t4) -> unify s ((t1, t3) :: (t2, t4) :: rest)
    | _, _ -> None

let type_of (e : exp) : typ option =
  match get_constraints empty_context e with
  | (t, c) -> (match unify empty_subst c with
               | Some s -> Some (apply_subst s t)
               | None -> None)

let e1 = Fun ("x", Fun ("y", Tuple (Add (Var "x", Num 1), Add (Var "y", Num 1))))
let test1 = type_of e1 (* should return Some (ArrowTy (IntTy, ArrowTy (IntTy, TupleTy (IntTy, IntTy)))) *)

let e2 = Fun ("x", Add (Fst (Var "x"), Snd (Var "x")))
let test2 = type_of e2 (* should return Some (ArrowTy (TupleTy (IntTy, IntTy), IntTy)) *)

(* grad student problem *)
let e3 = Fun ("x", Match (Var "x", "a", Inr (Add (Var "a", Num 1)), "b", Inl (Add (Num 2, Var "b"))))
let test3 = type_of e3 (* should return Some (ArrowTy (SumTy (IntTy, IntTy), SumTy (IntTy, IntTy))) *)
