type label = int (* what is label *)
type const = int (*Constants , machine integer *)
type var = int

type bop = Badd | Bsub | Bmul
type rel = Cinfeq | Csup (*big or small*)

type expr =
| Ecst of const (*n // Constant Expression*)
| Evar of var (*x // variable Expression*)
| Ebop of bop * expr * expr (* E . E //binary operator to a pair of expressions*)

type cond = (*Boolean Expression*)
rel * var * const

type command =
| Cskip (*skip*)
| Cseq of com * com (*C; C*)
| Cassign of var * expr (* x:=E *)
| Cinput of var (* input(x) *) 
| Cif of cond * com * com (* if(B) {C} else {C} *)
| Cwhile of cond * com (* while(B) {} *)
and com = 
label * command

type mem = const array (*read: var -> mem -> const*) 
let read x m = m.(x) 
let write Array x n m = (*wrtie: var -> const -> mem -> mem*)
    let nm = Array.copy m in
    nm.(x) <- n;
    nm

type state = label * mem (*label is int*)

let rec sem_expr e m = (*sem_expr : expr -> mem -> const*)
    match e with
    | Ecst n -> n
    | Evar x -> read x m (*read is  ' let read x m = m.(x) '*)
    | Ebop (o, e0, e1) ->
        binop o
        (sem_expr e0 m)
        (sem_expr e1 m)

let relop c v0 v1 = (*semantics of test ... relop : rel -> const -> const -> bool*) 
    match c with (*c is rel ... ' type rel = Cinfeq | Csup (*big or small*) ' *)
    | Cinfeq -> v0 <= v1
    | Csup -> v0 > v1
    (* sem_cond:
     *  (rel * var * const)
     *  -> mem -> bool *)

let sem_cond (c, x, n) m =
    relop c (read x m) 

let rec sem_com (1, c) m = (*val sem_com : ccom -> mem -> mem*)
    match c with
    | Cskip -> m
    | Cseq (c0, c1) -> sem_com c1 (sem_com c0 m)
    | Cassign (x, e) -> write x (sem_expr e m) m
    | Cinput x -> write x (input()) m
    | Cif (b, c0, c1) ->
        if sem_cond b m then sem_com c0 m
        else sem_com c1 m
    | Cwhile (b, c) ->
        if sem_cond b m then
            sem_com (1, Cwhile (b, c)) (sem_com c m)
        else m

let step p (1, m) = (*step : prog -> state -> state*)
    match find p 1 with
    | Cskip -> (next p 1, m)
    | Cassgin (x, e) -> (next p 1, write x (sem_expr e m) m)
    | Cinput x -> (next p 1, write x (input()) m)
    | C if (b, c0, c1) ->
        if sem_cond b m then (fst c0, m)
        else                 (fst c1, m)
    | Cwhile (b, c) ->
        if sem_cond b m then (fst c, m)
        else                 (next p 1, m)


(*=======================================================================================*)

type val_abs = 
    | Abot   (*ㅗ*)
    | Atop   (*ㅜ*)
    | Apos   (*>=0*)
    | Aneg   (*<=0*)
type nr_abs = val_abs array (*non-relational abstract domain*)


let val_bot = Abot  (*val_bot : val_abs*)
let val_top = Atop  (*val_top : val_abs*)
let val_incl a0 a1 = a0 = Abot || a1 = Atop || a0 = a1  (*val_incl a0 a1 = a0 = Abot || a1 = Atop || a0 = a1 // decides whether the abstract ordering relation holds for a pair of abstract elements*)
let val_cst n = if n < 0 then Aneg else Apos  (*val_cst n = if n < 0 then Aneg else Apos // implements the ? operation, which maps a constant to an abstract element that over-approximates it*)
let val_sat o n v =  (*val_sat: rel -> int -> val_abs -> val_abs // which over-approximates the effect of condition tests*)
    if v = Abot then Abot
    else if o = Cinfeq && n < 0 then
        if v = Apos then Abot else Aneg
    else if o = Csup && n >= 0 then
        if v = Aneg then Abot else Apos
    else v1

let val_join a0 a1 =  (*val_join: val_abs -> val_abs -> val_abs // over-approximates concrete unions*)
    match a0, a1 with
    | Abot , a | a, Abot -> a
    | Atop , _ | _, Atop | Apos, Aneg | Aneg, Apos -> Atop
    | Apos , Apos -> Apos
    | Aneg m Aneg -> Aneg

let val_binop o v0 v1 =  (*val_binop: bop -> val_abs -> val_abs -> val_abs // which implements the computation of ? for each operator ? of the language*)
    match o, v0, v1 with
    | _, Abot, _ | _, _, Abot -> Abot
    | Badd, Apos, Apos -> Apos
    | Badd, Aneg, Aneg -> Aneg
    |Badd, _, _ -> Apos

let nr_bot aenv = Array.map (fun _ -> Abot) aenv  (*nr_bot: nr_abs -> nr_abs // inputs an abstract element and returns an element describing the empty set of stores*)

let nr_is_bot aenv = (*nr_is_bot: nr_abs -> bool // checks whether an abstract element describes exactly the empty set of memory states*)
Array.exists (fun a -> a = val_bot) aenv

let nr_is_le aenv0 aenv1 = (*nr_is_le: nr_abs -> nr_abs -> bool // decides abstract ordering by checking that inclusion holds for each variable*) 
    let r = ref true in
    Array.iteri
        (fun x a0 -> r := !r && val_incl a0 (read x aenv1))
        aenv0;
    !r

let nr_join aenv0 aenv1 = (*nr_join: nr_abs -> nr_abs -> nr_abs // computes and over-approximation for the union of sets of stores and also proceeds component per componet*)
    Array.mapi
        (fun x a0 -> val_join a0 (read x aenv1))
        aenv0


(*=======================================================================================*)


type val_cst = Abot | Acst of int | Atop
let val_bot = Abot
let val_top = Atop
let val_incl a0 a1 = Abot || a1 = Atop || a0 = a1
let val_cst n = Acst n
let val_sat o n v =
    match o, v with
    | _, Abot -> Abot
    | Cinfeq, Acst i -> if i > n then Abot else v
    | Csup, Acst i -> if i <= n then Abot else v
    | _, _ -> v

let val_join a0 a1 =
    match a0, a1 with
    | Abot, a | a, Abot -> a
    | Atop, _ | _, Atop -> Atop
    | Acst _ , Acst _ -> if a0 = a1 then a0 else Atop

let val_binop o v0 v1 =
    match o, v0, v1 with
    | _, Abot, _ | _, _, Abot -> Abot
    | Badd, Atop, _ | Badd, _, Atop -> Atop
    | Badd, Acst i0, Acst i1 -> Acst (i0+i1)
    | ...

let rec ai_expr e aenv = (*Code of the abstract interpreter for scalar expressions*)
    match e with
    | Ecst n -> val_cst n
    | Evar x -> read x aenv
    | Ebop (o, e0, e1) -> val_binop o (ai_expr e0 aenv) (ai_expr e1 aenv)

let ai_cond (r, x, n) aenv = (*ai_cond: cond -> nr_abs -> nr_abs*)
    let av = val_sat r n (read x aenv) in
    if av = val_bot then nr_bot aenv
    else write x av aenv
