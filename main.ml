type label = int 
type const = int 
type var = int 

type bop = Badd | Bsub | Bmul 
type rel = Cinfeq | Csup 

type expr = 
| Ecst of const 
| Evar of var 
| Ebop of bop * expr * expr 

type cond = 
rel * var * const

type command =
| Cskip 
| Cseq of com * com 
| Cassign of var * expr 
| Cinput of var  
| Cif of cond * com * com 
| Cwhile of cond * com 
and com = 
label * command

type mem = const array  

(*메모리 m 에서 변수 x값 읽어오기 !!!!! return -> n *)
let read x m = m.(x) 

(*메모리 m 에 변수 x의 값을 n으로 주고 !!!!! return -> Memory*)
let write x n m = 
    let nm = Array.copy m in
    nm.(x) <- n;
    nm

type state = label * mem 

(*expr 값을 구분하여 n 값 일 경우 n을 , x 값 일 경우 메모리에서 찾고 , 연산일 경우 각각 expression을 연산한다 !!!!! return -> const(n)*)
let rec sem_expr e m = 
    match e with
    | Ecst n -> n 
    | Evar x -> read x m 
    | Ebop (o, e0, e1) -> 
        binop o
        (sem_expr e0 m)
        (sem_expr e1 m)

(*각각 크기를 비교 !!!!! return -> bool*)
let relop c v0 v1 =  
    match c with 
    | Cinfeq -> v0 <= v1
    | Csup -> v0 > v1
    
(*메모리 m 에서 x 값을 찾고 relop 함수 호출 !!!!! return -> relop(함수)*)
let sem_cond (c, x, n) m =
    relop c (read x m) n

(*command 각종 명령 처리 !!!!! return -> memory*)
let rec sem_com (l, c) m = 
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
            sem_com (l, Cwhile (b, c)) (sem_com c m)
        else m

(*프로그램과 label...? 을 통해 command를 구분하고 각 command 에 맞는 수행 !!!!! return -> (label, memory) *)
let step p (l, m) = (* next : prog -> label -> label        find : prog -> label -> com *) 
    match find p l with
    | Cskip -> (next p l, m)
    | Cassgin (x, e) -> (next p l, write x (sem_expr e m) m)
    | Cinput x -> (next p l, write x (input()) m)
    | C if (b, c0, c1) ->
        if sem_cond b m then (fst c0, m)
        else                 (fst c1, m)
    | Cwhile (b, c) ->
        if sem_cond b m then (fst c, m)
        else                 (next p l, m)


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
let val_incl a0 a1 = a0 = Abot || a1 = Atop || a0 = a1
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



(*=======================================================================================*)

(*
let rec postlfp f a = (*postlfp : (nr_abs -> nr_abs) -> nr_abs -> nr_abs*)
    let anext = f a in
    if nr_is_le anext a then a
    else postlfp f (nr_join a anext)
    (*ai_com : com -> nr_abs -> nr_abs*)
*)

let postlfp f a = (*improved the anaysis !!*)
    let rec aux acc n a =
        let anext = f a in
        if n < 2 then
            aux (nr_join a anext) (n+1) anext
        else if nr_is_le anext a then nr_join acc a
        else aux acc (n+1) (nr_join a anext) in
    aux a 0 a

let rec ai_com (1, c) aenv =
    if nr_is_bot aenv then aenv
    else
        match c with
        | Cskip -> aenv
        | Cseq (c0, c1) -> ai_com c1 (ai_com c0 aenv)
        | Cassign (x, e) -> write x (ai_expr e aenv) aenv
        | Cinput x -> write x val_top aenv
        | Cif (b, c0, c1) ->
            nr_join
                (ai_com c0 (ai_cond b aenv))
                (ai_com c1 (ai_cond (cneg b) aenv))
        | Cwhile (b, c) ->
            let f_loop = fun a -> ai_com c (ai_cond b a) in
            ai_cond (cneg b) (postlfp f_loop aenv)


(*=======================================================================================*)

(* ai_step : com -> label -> nr_abs
*            -> (label * nr_abs) list *)

let rec ai_step (1, c) lnext aenv = 
    match c with
    | Cskip ->
        [(lnext, aenv)]
    | Cseq (c0, c1) ->
        ai_step c0 (fst c1) aenv
    | Cassign (x, e) ->
        [(lnext, write x (ai_expr e aenv) aenv)]
    | Cinput x ->
        [(lnext, write x val_tip aenv)]
    | Cif (b, c0, c1) ->
        [(fst c0, ai_cond b aenv);
         (fst c1, ai_cond (cneg b) aenv)]
    | Cwhile (b, c) ->
        [(fst c, ai_cond b aenv);
         (lnext, ai_cond (cneg b) aenv)]


(*ai_iter: prog -> nr_abs ->unit*)
let ai_iter p aenv =
    let (1, c) = first p in
    invs := I.add l aenv I.empty;
    let wlist = T.create () in
    T.add l wlist;
    while not (T.is_empty wlist) do
        let l = T.pop wlist in
        let c = find p l in
        let lnext = next p l in
        let aenv = I.find l !invs in
        let aposts = ai_step (1,c) lnext aenv in
        List.iter
        (fun (lnext, apost)->
            let old_apost = storage_find lnext in
            if not (nr_is_le apost old_apost) then
            let new_apost = nr_join old_apost apost in
            invs := I.add lnext new_apost !invs;
            T.add lnext wlist
        ) aposts
done