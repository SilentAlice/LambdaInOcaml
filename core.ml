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
    | TmRecord(_,fields) -> List.for_all (fun (l,ti) -> isval ctx ti) fields
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
    | TmRecord(fi,fields) ->
      let rec evalafield l = match l with 
        [] -> raise NoRuleApplies
      | (l,vi)::rest when isval ctx vi -> 
          let rest' = evalafield rest in
          (l,vi)::rest'
      | (l,ti)::rest -> 
          let ti' = eval1 ctx ti in
          (l, ti')::rest
      in let fields' = evalafield fields in
      TmRecord(fi, fields')

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
(*************************** Subtyping *************************)
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
  | (TyTop,TyTop) -> true
  | (TyNat,TyNat) -> true
  | (TyRecord(fields1),TyRecord(fields2)) -> 
       List.length fields1 = List.length fields2
       &&                                         
       List.for_all 
         (fun (li2,tyTi2) ->
            try let (tyTi1) = List.assoc li2 fields1 in
                tyeqv ctx tyTi1 tyTi2
            with Not_found -> false)
         fields2

  | _ -> false

let rec subtype ctx tyS tyT =
   tyeqv ctx tyS tyT ||
   let tyS = simplifyty ctx tyS in
   let tyT = simplifyty ctx tyT in
   match (tyS,tyT) with
     (_,TyTop) -> 
       true
   | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (subtype ctx tyT1 tyS1) && (subtype ctx tyS2 tyT2)
   | (TyRecord(fS), TyRecord(fT)) ->
       List.for_all
         (fun (li,tyTi) -> 
            try let tySi = List.assoc li fS in
                subtype ctx tySi tyTi
            with Not_found -> false)
         fT

   | (_,_) -> 
       false

let rec join ctx tyS tyT =
  if subtype ctx tyS tyT then tyT else 
  if subtype ctx tyT tyS then tyS else
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let commonLabels = 
        List.find_all (fun l -> List.mem l labelsT) labelsS in
      let commonFields = 
        List.map (fun li -> 
                    let tySi = List.assoc li fS in
                    let tyTi = List.assoc li fT in
                    (li, join ctx tySi tyTi))
                 commonLabels in
      TyRecord(commonFields)
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      (try TyArr(meet ctx tyS1 tyT1, join ctx tyS2 tyT2)
        with Not_found -> TyTop)
  | _ -> 
      TyTop

and meet ctx tyS tyT =
  if subtype ctx tyS tyT then tyS else 
  if subtype ctx tyT tyS then tyT else 
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let allLabels = 
        List.append
          labelsS 
          (List.find_all 
            (fun l -> not (List.mem l labelsS)) labelsT) in
      let allFields = 
        List.map (fun li -> 
                    if List.mem li allLabels then
                      let tySi = List.assoc li fS in
                      let tyTi = List.assoc li fT in
                      (li, meet ctx tySi tyTi)
                    else if List.mem li labelsS then
                      (li, List.assoc li fS)
                    else
                      (li, List.assoc li fT))
                 allLabels in
      TyRecord(allFields)

  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      TyArr(join ctx tyS1 tyT1, meet ctx tyS2 tyT2)
  | _ -> 
      raise Not_found

(*************************************** Type ************************************)



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
            if subtype ctx tyT2 tyT11 then tyT12
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
  | TmRecord(fi, fields) ->
      let fieldtys = 
        List.map (fun (li,ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)


