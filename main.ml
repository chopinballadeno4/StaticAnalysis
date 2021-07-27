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
    | Abot
    | Atop
    | Apos
    | Aneg
type nr_abs = val_abs array

