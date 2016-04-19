open Format
open Syntax
open Support.Error
open Support.Pervasive

(* ------------------------   EVALUATION  RULES  ------------------------ *)

exception NoRuleApplies

(* Judge if the term is numerical *)
let rec isnumber ctx t = match t with
    | TmZero(_) -> true
    | TmSucc(_,t1) -> isnumber ctx t1
    | _ -> false

let rec isval ctx t = match t with
    | TmTrue(_)  -> true
    | TmFalse(_) -> true
    | t when isnumber ctx t  -> true
    | TmAbs(_,_,_) -> true
    | _ -> false

let rec eval1 ctx t = match t with
      (* E-IF TRUE, FLASE, IF *)
    | TmIf(_,TmTrue(_),t2,t3) -> t2
    | TmIf(_,TmFalse(_),t2,t3) -> t3
    | TmIf(fi,t1,t2,t3) ->
        let t1' = eval1 ctx t1 in
        TmIf(fi, t1', t2, t3)
    | TmSucc(fi,t1) ->
        let t1' = eval1 ctx t1 in
        TmSucc(fi, t1')
    | TmPred(_,TmZero(_)) ->
        TmZero(dummyinfo)
    | TmPred(_,TmSucc(_,nv1)) when (isnumber ctx nv1) ->
        nv1
    | TmPred(fi,t1) ->
        let t1' = eval1 ctx t1 in
        TmPred(fi, t1')
    | TmIsZero(_,TmZero(_)) ->
        TmTrue(dummyinfo)
    | TmIsZero(_,TmSucc(_,nv1)) when (isnumber ctx nv1) ->
        TmFalse(dummyinfo)
    | TmIsZero(fi,t1) ->
        let t1' = eval1 ctx t1 in
        TmIsZero(fi, t1')
    | TmVar(fi,n,_) ->
        (match getbinding fi ctx n with
            TmAbbBind(t) -> t 
          | _ -> raise NoRuleApplies)
    
    | TmApp(fi,TmAbs(_,x,t12),v2) when isval ctx v2 ->
        termSubstTop v2 t12
    | TmApp(fi,v1,t2) when isval ctx v1 ->
        let t2' = eval1 ctx t2 in
        TmApp(fi, v1, t2')
    | TmApp(fi,t1,t2) ->
        let t1' = eval1 ctx t1 in
        TmApp(fi, t1', t2)

    | _ -> 
        raise NoRuleApplies

let rec eval ctx t =
    try let t' = eval1 ctx t
        in eval ctx t'
    with NoRuleApplies -> t

let evalbinding ctx b = match b with
    TmAbbBind(t) ->
        let t' = eval ctx t in 
        TmAbbBind(t')
    | bind -> bind
