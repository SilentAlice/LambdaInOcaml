(*
115037910081 Yuming Wu
Lambda Calculus Implementation
*)

(* Term Definition
Term:
t ::=
        | x     <-- variable is a term
        | (lam(x).t (noted as \x.t) is a term
        | (t1 t2)   is a term
*)

type var = string (*variable is string*)
type term =
        | TmVar of var
        | TmAbs of var * term
        | TmApp of term * term

(* Used for test *)
(*
let x = "x"
let vx = TmVar x
let y = "y"
let vy = TmVar y
let ex_abs = TmAbs(x, TmApp(vx, vy))
let ex_app = TmApp(ex_abs, vy)
*)

(* Translate term into string *)

let rec term_to_string = function
        | TmVar x -> x
        | TmAbs(x, t) -> "(\\" ^ x ^ "." ^ (term_to_string t) ^ ")"
        | TmApp(t1, t2) -> "(" ^ (term_to_string t1) ^ " " ^ (term_to_string t2) ^ ")"


(* Print Terms as string *)

let pterm = fun x -> print_endline(term_to_string x)


(* find free variables *)

let rec free_vars = function
        | TmVar x -> [x]
        | TmAbs(x, t) -> List.filter(fun y -> y <> x)(free_vars t)
(* Find free variables in term2 and not in term 1 *)
(* append new terms to free variables in term1 *)
        | TmApp(t1, t2) ->
            let f_t1 = free_vars t1 in
            let f_t2 = free_vars t2 in
              List.append f_t1 (List.filter (fun y -> not (List.mem y f_t1)) f_t2)


(* Rename variable *)

let rec rename_var v l =
        if List.mem v l then
            rename_var (v ^ "'") l
        else 
            v


(* Subsitution : replace v with term in TERM *)

let rec substitute v term = function
        | TmVar x -> if ( x = v ) then term else TmVar(x)
        | TmAbs(x, t) -> 
            let f_t = free_vars t in
            let f_term = free_vars term in
              if ( x = v ) then
(*               x is rebound, cant be replaced *)
                  TmAbs(x, t)
(*                     t doesnt include v , do nothing *)
              else if ( not ( List.mem v (f_t) ) ) then
                  TmAbs(x, t)
(*                       x has the same name with term, Rename *)
              else if ( List.mem x (f_term) ) then
(*                       rename x *)
                  let newvar = rename_var x ( List.append(f_t)(f_term) ) in
(*                       Then do normal subsitution *)
                  TmAbs(newvar, substitute x term t)
              else 
(*                       Normal sustitituion  *)
                  TmAbs(x, substitute x term t)
        | TmApp(t1, t2) -> TmApp(substitute v term t1, substitute v term t2)


(*  Beta Reduce Rule *)

let beta = function
        | TmApp(TmAbs(x, t), s) -> substitute x s t
        | _ -> failwith "Is Not A redex !"

let is_redex = function
        | TmApp(TmAbs(x,t),s) -> true
        | _ -> false
(*
 * One Step Reduction
  t1 -> t1'         t2->t2'        
--------------  --------------  Beta-reduction
t1t2 -> t1't2    v1t2 -> v1t2'
*)

let rec normal_step t = 
        if is_redex t then
                beta t
        else 
                match t with
                | TmVar x -> TmVar x
                | TmAbs(x, t) -> TmAbs(x, normal_step t)
                | TmApp(t1, t2) ->
                                (* left one has no redex *)
                                if normal_step t1 = t1 then TmApp(t1, normal_step t2)
                                (* Reduce left one first *)
                                else TmApp(normal_step t1, t2)


let rec normalize t =
        if normal_step t = t then t (* Finish *)
        else normal_step (normal_step t)

(* Define Church Numerals *)
(* We can write plus, succ directly *)
(*
let s = "s"
let vs = TmVar s
let z = "z"
let vz = TmVar z
let zero = TmAbs(s, TmAbs(z, vz))
let one = TmAbs(s, TmAbs(z, TmApp(vs, vz)))
*)

(* De Bruijin Terms *)

(* Define De Bruijin Terms *)
type debru = 
        | DeVar of int
        | DeAbs of debru
        | DeApp of debru * debru

let debruijinize t =
    let rec db indices =
            (* Plus i with 1*)
        let plus1 = function(x, i) -> (x, i+1) in
            function
                | TmVar(x) -> (* This term has an index *)
                        if List.mem_assoc x indices then 
                            (* Find index of this name *)
                            DeVar(List.assoc x indices)
                        else 
                            (* Error *)
                            raise(Invalid_argument ("debruijinize: " ^ x ))
                | TmAbs(x, t) ->
                        (* Add x to namespace and increase other index *)
                        let l = List.map plus1(List.remove_assoc x indices) in
                          DeAbs(db((x, 0) :: l) t)
                | TmApp(t1, t2) ->
                        DeApp(db indices t1, db indices t2)
    in
    (* Naming free variables with numbers, so that they can find a corresponding index in TmVar case *)
    let free =
        let rec generate n =
            if n = 0 then
                []
            else
                n :: (generate (n-1))
        in
        List.combine(free_vars t)(generate (List.length (free_vars t)))
    in
    db free t

(* We have debruijinized representation now *)

let rec de_to_string = function
        | DeVar(i)  -> string_of_int i
        | DeAbs(t)  -> "\\." ^ (de_to_string t)
        | DeApp(t1,t2) ->
                        "(" ^ (de_to_string t1) ^ ") ("
                        ^ (de_to_string t2) ^ ")"

(* Shifting *)
let tmmap onvar c t = 
    let rec walk c t = match t with
         DeVar(x) -> onvar c x
       | DeAbs(t) -> DeAbs(walk (c+1) t)
       | DeApp(t1, t2) -> DeApp(walk c t1, walk c t2)
    in walk c t

let termShiftAbove d c t =
        tmmap
        (fun c x -> if x >= c then DeVar(x+d) else DeVar(x))
        c t

let termShift d t = termShiftAbove d 0 t

(* Substitution *)
let termSubst j s t =
        tmmap
        ( fun c x -> if x=j+c then termShift c s else DeVar(x))
        0
        t

let termSubstTop s t =
        termShift (-1) (termSubst 0 (termShift 1 s) t)

(* *****************Evaluation******************** *)
let rec isval ctx t = match t with
      DeAbs(t) -> true
    | _ -> false

let rec eval ctx t = match t with
(* Beta Reduction *)
    | DeApp(DeAbs(t12), v2) when isval ctx v2 ->
                    termSubstTop v2 t12
    | DeApp(v1, t2) when isval ctx v1 ->
                    let t2' = eval ctx t2 in
                    DeApp(v1, t2')
    | DeApp(t1, t2) ->
                    let t1' = eval ctx t1 in
                    DeApp(t1', t2)
