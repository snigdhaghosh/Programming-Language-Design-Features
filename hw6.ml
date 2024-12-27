open List

type ident = string

type exp = Var of ident | Fun of ident * exp | App of exp * exp
           | Int of int | Bool of bool | Add of exp * exp | Eq of exp * exp
           | If of exp * exp * exp
           | Inl of exp | Inr of exp
           | Match of exp * ident * exp * ident * exp
           (* problem 5 *)
           | Tuple of exp * exp
           | Fst of exp | Snd of exp

(* implementation of substitution *)
let rec vars (l : exp) : ident list =
    match l with
    | Var i -> [i]
    | Fun (x, b) -> x :: vars b
    | App (la, lb) -> vars la @ vars lb
    | Int _ | Bool _ -> []
    | Add (e1, e2) | Eq (e1, e2) -> vars e1 @ vars e2
    | If (e1, e2, e3) -> vars e1 @ vars e2 @ vars e3
    | Inl e | Inr e -> vars e
    | Match (e, x1, e1, x2, e2) -> x1 :: x2 :: vars e @ vars e1 @ vars e2
     (* problem 5 *)
    | Tuple (e1, e2) -> vars e1 @ vars e2
    | Fst (e) | Snd (e) -> vars e
    
let rec fresh_aux (l : ident list) (i : int): ident =
    let s = String.make 1 (Char.chr i) in
    match List.find_opt (fun t -> t = s) l with
    | Some _ -> let i' = i + 1 in let i'' = if i' > 122 then 97 else i' in fresh_aux l i''
    | None -> s
        
let fresh (l : exp) : ident = fresh_aux (vars l) 121
        
let rec subst (x : ident) (l2 : exp) (l : exp) : exp =
    match l with
    | Var y -> if y = x then l2 else Var y
    | App (la, lb) -> App (subst x l2 la, subst x l2 lb)
    | Fun (y, b) -> if y = x then Fun (y, b) else
        let (y', b') = avoid_capture x l2 y b in Fun (y', b')
    | Int _ | Bool _ -> l
    | Add (e1, e2) -> Add (subst x l2 e1, subst x l2 e2)
    | Eq (e1, e2) -> Eq (subst x l2 e1, subst x l2 e2)
    | If (e, e1, e2) -> If (subst x l2 e, subst x l2 e1, subst x l2 e2)
    | Inl e -> Inl (subst x l2 e)
    | Inr e -> Inr (subst x l2 e)
    | Match (e, x1, e1, x2, e2) ->
        let (x1', e1') = avoid_capture x l2 x1 e1 in
        let (x2', e2') = avoid_capture x l2 x2 e2 in
        Match (subst x l2 e, x1', e1', x2', e2')
    (* problem 5 *)
    | Tuple (e1, e2) -> Tuple(subst x l2 e1, subst x l2 e1)
    | Fst (e) -> Fst(subst x l2 e)
    | Snd (e) -> Snd(subst x l2 e)
    
and avoid_capture x l2 y b =
    if y = x then (y, b) else
    let z = fresh (Fun (x, l2)) in
    (z, subst x l2 (subst y (Var z) b))
(* end substitution *)
             
let rec eval (e : exp) : exp option =
   match e with
   | Var _ | Int _ | Bool _ | Fun _ -> Some e
   | App (la, lb) ->
       (match eval la, eval lb with
        | Some (Fun (x, b)), Some v -> eval (subst x v b)
        | _ -> None)
   | Add (e1, e2) ->
       (match eval e1, eval e2 with
        | Some (Int i1), Some (Int i2) -> Some (Int (i1 + i2))
        | _, _ -> None)
   | Eq (e1, e2) ->
       (match eval e1, eval e2 with
        | Some v1, Some v2 -> Some (Bool (v1 = v2))
        | _, _ -> None)
   | If (e, e1, e2) ->
       (match eval e with
        | Some (Bool b) -> eval (if b then e1 else e2)
        | _ -> None)
   (* problems 3-5 *)
   | Inl (e) -> 
        (match eval e with
        | Some v -> Some (Inl v)
        | _ -> None)
   | Inr (e) -> 
        (match eval e with
        | Some v -> Some (Inr v)
        | _ -> None)
   | Match (e, x1, e1, x2, e2) -> (
        match eval e with
        | Some v -> (
            match v with
            | Inl x -> eval (subst x1 x e1)
            | Inr x -> eval (subst x2 x e2)
            | _ -> None
            )
        | _ -> None)
   (* problem 5 *)
   | Tuple (e1, e2) -> (
        match eval e1, eval e2 with
        | Some v1, Some v2 -> Some(Tuple(v1, v2))
        | _ -> None 
   ) 
   | Fst e -> (
        match eval e with
        | Some Tuple(v1,v2) -> Some v1
        | _ -> None
   )
   | Snd e -> (
        match eval e with
        | Some Tuple(v1,v2) -> Some v2
        | _ -> None
   )
   | _ -> None

(*
problem 1
  (λx. x) y evaluates to y
  (λx. (λy. x)) z evaluates to λy.z
  (λx. (λy. y) x) (λz. z) evaluates to λz.z
*)

(* problem 2 *)
let lam1 = Fun ("x", Fun ("y", App (Var "x", Var "y")))     (* λx. (λy. x y) *)
let expa : exp = App(Fun("x", Var "x"), Var "y")
let expb : exp = App(Fun("x", Fun("y", Var "x")), Var "z")
let expc : exp = App(Fun ("x", App(Fun ("y", Var "y"), Var "x")), Fun ("z", Var "z"))

let resa = eval(expa)
let resb = eval(expb)
let resc = eval(expc)

let test1 : exp option = eval (App (Fun ("a", Add (Var "a", Int 1)), Int 5))

let test2 : exp option = eval (Inr (Add (Int 3, Int 4)))    (* Some (Inr (Int 7)) *)

let test3 : exp option = eval (Match (Inr (Bool false), "i", Var "i", "b", If (Var "b", Int 1, Int 0))) (* Some (IntVal 0) *)

let test4 : exp option = eval (App (Fun ("y", Match (Var "y", "a", Var "a", "b", Add (Var "b", Int 2))), Inr (Int 5))) (* should return Some (Int 7) *)

let test5 : exp option = eval (Tuple (Snd (Tuple (Int 5, Bool true)), Fst (Tuple (Int 5, Bool true)))) (* Some (Tuple (Bool true, Int 5)) *)
