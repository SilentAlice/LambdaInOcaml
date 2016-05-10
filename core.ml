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
    | TmAbs(_,_,_,_) -> true
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
            TmAbbBind(t, _) -> t 
          | _ -> raise NoRuleApplies)
    
    | TmApp(fi,TmAbs(_,x,tyT11,t12),v2) when isval ctx v2 ->
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
    TmAbbBind(t, tyT) ->
        let t' = eval ctx t in 
        TmAbbBind(t', tyT)
    | bind -> bind

(*************************************** Type ************************************)
let istyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> true
  | _ -> false

let gettyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> tyT
  | _ -> raise NoRuleApplies

let rec computety ctx tyT = match tyT with
    TyVar(i,_) when istyabb ctx i -> gettyabb ctx i
  | _ -> raise NoRuleApplies

let rec simplifyty ctx tyT =
  try
    let tyT' = computety ctx tyT in
    simplifyty ctx tyT' 
  with NoRuleApplies -> tyT

let rec tyeqv ctx tyS tyT =
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
  | (TyId(b1),TyId(b2)) -> b1=b2
  | (TyVar(i,_), _) when istyabb ctx i ->
      tyeqv ctx (gettyabb ctx i) tyT
  | (_, TyVar(i,_)) when istyabb ctx i ->
      tyeqv ctx tyS (gettyabb ctx i)
  | (TyVar(i,_),TyVar(j,_)) -> i=j
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyBool,TyBool) -> true
  | (TyNat,TyNat) -> true
  | _ -> false

let rec typeof ctx t =
  match t with
  | TmTrue(fi) -> 
      TyBool
  | TmFalse(fi) -> 
      TyBool
  | TmIf(fi,t1,t2,t3) ->
     if tyeqv ctx (typeof ctx t1) TyBool then
       let tyT2 = typeof ctx t2 in
       if tyeqv ctx tyT2 (typeof ctx t3) then tyT2
       else error fi "typeof:TmIf t2 != t3"
     else error fi "typeof:TmIf t1 is not bool"
  | TmVar(fi,i,_) -> getTypeFromContext fi ctx i
  | TmAbs(fi,x,tyT1,t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, typeShift (-1) tyT2)
  | TmApp(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match simplifyty ctx tyT1 with
          TyArr(tyT11,tyT12) ->
            if tyeqv ctx tyT2 tyT11 then tyT12
            else error fi "typeof:TmApp type mismatch"
        | _ -> error fi "typeof:TmApp Arrow type expected")
  | TmZero(fi) ->
      TyNat
  | TmSucc(fi,t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyNat
      else error fi "typeof: TmSucc: Nat expected"
  | TmPred(fi,t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyNat
      else error fi "typeof: TmPred: Nat expected"
  | TmIsZero(fi,t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyBool
      else error fi "typeof: TmIsZero: Nat expected"
