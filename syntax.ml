open Format
open Support.Error
open Support.Pervasive

(* ---------------------------------------------------------------------- *)
(* Datatypes, extended with app TmApp TmAbs TmVar *)

type term =
    | TmTrue of info
    | TmFalse of info
    | TmIf of info * term * term * term
    | TmZero of info
    | TmSucc of info * term
    | TmPred of info * term
    | TmIsZero of info * term
    (* Extended *)
    | TmVar of info * int * int
    | TmAbs of info * string * term
    | TmApp of info * term * term

(* var should be bound a value *)
type binding =
    | NameBind 
    | TmAbbBind of term

type context = (string * binding) list

type command =
    | Eval of info * term
    | Bind of info * string * binding

(* ---------------------------------------------------------------------- *)
(* Context management *)

let emptycontext = []

let ctxlength ctx = List.length ctx

let addbinding ctx x bind = (x,bind)::ctx

let addname ctx x = addbinding ctx x NameBind

(* Every x should has a name *)
let rec isnamebound ctx x =
    match ctx with
       [] -> false
    | (y,_)::rest ->
        if y=x then true
        else isnamebound rest x

let rec pickfreshname ctx x =
    (* If has x, then change x to x' *)
  if isnamebound ctx x then pickfreshname ctx ( x ^ "'" )
  else ((x,NameBind)::ctx), x

let index2name fi ctx x =
  try
    let (xn,_) = List.nth ctx x in
    xn
  with Failure _ ->
    let msg =
      Printf.sprintf "Index2name: Can't find x: offset: %d, ctx size: %d" in
    error fi (msg x (List.length ctx))

let rec name2index fi ctx x =
  match ctx with
      [] -> error fi ("name2Index: " ^ x ^ " is unbound")
    | (y,_)::rest ->
        if y=x then 0
        else 1 + (name2index fi rest x)

(* ---------------------------------------------------------------------- *)
(* Shifting *)

let tmmap onvar c t = 
  let rec walk c t = match t with
    (* n is used to indentify the length of var *)
  | TmVar(fi,x,n) -> onvar fi c x n
  | TmAbs(fi,x,t2) -> TmAbs(fi,x,walk (c+1) t2)
  | TmApp(fi,t1,t2) -> TmApp(fi,walk c t1,walk c t2)
  | TmZero(fi)      -> TmZero(fi)
  | TmSucc(fi,t1)   -> TmSucc(fi, walk c t1)
  | TmPred(fi,t1)   -> TmPred(fi, walk c t1)
  | TmIsZero(fi,t1) -> TmIsZero(fi, walk c t1)
  | TmTrue(fi) as t -> t
  | TmFalse(fi) as t -> t
  | TmIf(fi,t1,t2,t3) -> TmIf(fi,walk c t1,walk c t2,walk c t3)
  in walk c t

(* n means length of var, for checking *)
let termShiftAbove d c t =
  tmmap
    (fun fi c x n -> if x>=c then TmVar(fi,x+d,n+d) else TmVar(fi,x,n+d))
    c t

let termShift d t = termShiftAbove d 0 t

let bindingshift d bind =
  match bind with
    NameBind -> NameBind
  | TmAbbBind(t) -> TmAbbBind(termShift d t)

(* ---------------------------------------------------------------------- *)
(* Substitution *)

let termSubst j s t =
  tmmap
    (fun fi c x n -> if x=j+c then termShift c s else TmVar(fi,x,n))
    0
    t

let termSubstTop s t = 
  termShift (-1) (termSubst 0 (termShift 1 s) t)

(* ---------------------------------------------------------------------- *)
(* Context management (continued) *)

let rec getbinding fi ctx i =
  try
    let (_,bind) = List.nth ctx i in
    bindingshift (i+1) bind 
  with Failure _ ->
    let msg =
      Printf.sprintf "Variable lookup failure: offset: %d, ctx size: %d" in
    error fi (msg i (List.length ctx))
 
(* ---------------------------------------------------------------------- *)
(* Extracting file info *)

let tmInfo t = match t with
  | TmTrue(fi) -> fi
  | TmFalse(fi) -> fi
  | TmIf(fi,_,_,_) -> fi
  | TmVar(fi,_,_) -> fi
  | TmAbs(fi,_,_) -> fi
  | TmApp(fi, _, _) -> fi
  | TmZero(fi) -> fi
  | TmSucc(fi,_) -> fi
  | TmPred(fi,_) -> fi
  | TmIsZero(fi,_) -> fi

(* ---------------------------------------------------------------------- *)
(* Printing *)

(* The printing functions call these utility functions to insert grouping
  information and line-breaking hints for the pretty-printing library:
     obox   Open a "box" whose contents will be indented by two spaces if
            the whole box cannot fit on the current line
     obox0  Same but indent continuation lines to the same column as the
            beginning of the box rather than 2 more columns to the right
     cbox   Close the current box
     break  Insert a breakpoint indicating where the line maybe broken if
            necessary.
  See the documentation for the Format module in the OCaml library for
  more details. 
*)

let obox0() = open_hvbox 0
let obox() = open_hvbox 2
let cbox() = close_box()
let break() = print_break 0 0

let small t = 
  match t with
    TmVar(_,_,_) -> true
  | _ -> false

let rec printtm_Term outer ctx t = match t with
    TmIf(fi, t1, t2, t3) ->
       obox0();
       pr "if ";
       printtm_Term false ctx t1;
       print_space();
       pr "then ";
       printtm_Term false ctx t2;
       print_space();
       pr "else ";
       printtm_Term false ctx t3;
       cbox()
    | TmAbs(fi,x,t2) ->
      (let (ctx',x') = (pickfreshname ctx x) in
            obox(); pr "lambda "; pr x'; pr ".";
            if (small t2) && not outer then break() else print_space();
            printtm_Term outer ctx' t2;
            cbox())

    | t -> printtm_AppTerm outer ctx t

and printtm_AppTerm outer ctx t = match t with
    TmApp(fi, t1, t2) ->
      obox0();
      printtm_AppTerm false ctx t1;
      print_space();
      printtm_ATerm false ctx t2;
      cbox()
  | TmPred(_,t1) ->
       pr "pred "; printtm_ATerm false ctx t1
  | TmIsZero(_,t1) ->
       pr "iszero "; printtm_ATerm false ctx t1
  | t -> printtm_PathTerm outer ctx t

and printtm_PathTerm outer ctx t = match t with
    t -> printtm_ATerm outer ctx t

and printtm_ATerm outer ctx t = match t with
  | TmTrue(_) -> pr "true"
  | TmFalse(_) -> pr "false"
  | TmZero(fi) ->
       pr "0"
  | TmSucc(_,t1) ->
     let rec f n t = match t with
         TmZero(_) -> pr (string_of_int n)
       | TmSucc(_,s) -> f (n+1) s
       | _ -> (pr "(succ "; printtm_ATerm false ctx t1; pr ")")
     in f 1 t1
  | TmVar(fi,x,n) ->
      if ctxlength ctx = n then
        pr (index2name fi ctx x)
      else
        pr ("[bad index: " ^ (string_of_int x) ^ "/" ^ (string_of_int n)
            ^ " in {"
            ^ (List.fold_left (fun s (x,_) -> s ^ " " ^ x) "" ctx)
            ^ " }]")
  | t -> pr "("; printtm_Term outer ctx t; pr ")"

let printtm ctx t = printtm_Term true ctx t 

let prbinding ctx b = match b with
    NameBind -> ()
  | TmAbbBind(t) -> pr "= "; printtm ctx t 


