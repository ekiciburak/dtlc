Require Import Relations Morphisms.
Require Import Program Coq.Setoids.Setoid.
Require Import Coq.ZArith.BinInt.
Require Import List.

Require Import ZArith.
Open Scope Z_scope.

Require Import Arith.
Require Import Ascii.
Require Import String.
Require Import BinInt.
Require Setoid.
Require Import Le Gt Minus Bool.

Set Implicit Arguments.
Open Scope list_scope.

Delimit Scope Int_scope with I.
Local Open Scope Int_scope.

Delimit Scope string_scope with string.
Local Open Scope string_scope.

Local Open Scope list_scope.

Require prereqs.

Module Make(Import M: prereqs.T).

Inductive variable: Type :=
  | Str: string -> variable
  | Gensym: string * nat -> variable.
Check variable.

Inductive expr: Type :=
  | Var: variable -> expr
  | Universe: nat -> expr
  | Pi: variable * expr * expr  -> expr
  | Lambda: variable * expr * expr  -> expr
  | App: expr * expr -> expr.
Check expr.

(*Check Lambda ((Str("x"), Universe 0, (Var (Str "x+5")) )).*)

Definition context := list (variable * (expr * option expr)).
Check context.


Fixpoint assoc_opt (x: variable) (ctx: list (variable * expr)) {struct ctx}: option expr :=
  match ctx with
    | nil => None
    | ((v, a) :: ctx') => 
    (match v, x with
      | Str v1, Str x1 => 
      (match (string_compare v1 x1) with
        | 0 => Some a
        | _ => assoc_opt x ctx'
      end)
      | (Gensym (v1, t1)), Gensym (v2, t2) => 
      (match (string_compare v1 v2) with
        | 0 => 
        (match nat_compare t1 t2 with
          | 0 => Some a
          | _ => assoc_opt x ctx'
        end)
        | _ => assoc_opt x ctx'
        end)
      | _, _ => assoc_opt x ctx'
      end)
  end.
Check assoc_opt.

(*
Definition l := ((Str "c", (Universe 5%nat, None)) :: ((Gensym ("b", 2%nat)), (Universe 0%nat, Some (Var (Str "xyx")))) :: 
  (Str "a", (Universe 10%nat, None)):: ((Gensym ("d", 20%nat)), (Universe 21%nat, None)) :: nil).
Eval compute in assoc_opt2 (Str "c") l.
Eval compute in assoc_opt2 (Gensym ("b", 2%nat)) l.
Eval compute in assoc_opt1 (Gensym ("d", 20%nat)) l.
Eval compute in assoc_opt2 (Str "a") l.
*)

(*
Definition l := ((Str "c", (Universe 5%nat, None)) :: ((Gensym ("b", 2%nat)), (Universe 0%nat, Some (Var (Str "xyx")))) :: 
  (Str "a", (Universe 10%nat, None)):: ((Gensym ("d", 20%nat)), (Universe 21%nat, None)) :: nil).
Eval compute in lookup_ty_opt (Str "c") l.
Eval compute in lookup_val_opt (Str "c") l.
Eval compute in lookup_val_opt (Gensym ("b", 2%nat)) l.
Eval compute in lookup_val_opt (Gensym ("b", 3%nat)) l.
Eval compute in lookup_ty_opt (Gensym ("b", 3%nat)) l.
Eval compute in lookup_ty_opt (Gensym ("b", 2%nat)) l.
*)

Definition extend (x: variable) (t: expr) (t': option expr) (ctx: context) := (x, (t, t')) :: ctx.
Check extend.

(*
Definition l := ((Str "c", (Universe 5%nat, None)) :: ((Gensym ("b", 2%nat)), (Universe 0%nat, Some (Var (Str "xyx")))) :: 
  (Str "a", (Universe 10%nat, None)):: ((Gensym ("d", 20%nat)), (Universe 21%nat, None)) :: nil).
Eval compute in extend (Str "a") (Universe 10) None l.
Eval compute in extend (Str "u") (Lambda ((Gensym ("d", 20%nat)), (Universe 21), (Var (Str "burak"))))
(Some ((Pi ((Str("a"), Universe 0, (Var (Str "a+325")) ))))) l.
*)

Definition incr (n: nat) := S n.

Definition refresh (v: variable) := 
  let k := 0%nat in
    match v with
      | Str x => Gensym (x, incr k)
      | Gensym (x, _) =>  Gensym (x, incr k)
   end.

Fixpoint subst (s: list (variable * expr)) (e: expr) {struct e}: expr :=
    match e with
      | Var x                  => 
      (match assoc_opt x s with
        | None => Var x
        | Some a => a
      end)
      | Universe k       => Universe k
      | Pi (x, t, e)     => Pi (let x' := refresh x in (x', subst s t, subst ((x, Var x') :: s) e))
      | Lambda (x, t, e) => Lambda (let x' := refresh x in (x', subst s t, subst ((x, Var x') :: s) e))
      | App (e1, e2)     => App (subst s e1, subst s e2)
    end.
Check subst.


(*
Definition l := ((Str "c", (Universe 5%nat, Some ((Lambda ((Str("a"), Universe 0, Var (Gensym ("b", 2%nat)) )))) ))
:: ((Gensym ("b", 2%nat)), (Universe 0%nat, Some (Var (Str "xyx")))) 
:: (Str "a", (Universe 10%nat, None)):: ((Gensym ("d", 20%nat)), (Universe 21%nat, None)) :: nil).
Check l.

Definition l2 := ((Lambda ((Str("a"), Universe 0, (Var (Str "a+325")) )))).
Check l2.

Eval compute in subst [(Str ("a+325"), ((Var (Gensym ("c", 2%nat)))))] l2.
*)

Fixpoint assoc_ctx_opt (x: variable) (ctx: context) {struct ctx}: (expr * option expr) :=
  match ctx with
    | nil => ((Var x), None)
    | ((v, (a, b)) :: ctx') => 
    (match v, x with
      | Str v1, Str x1 => 
      (match (string_compare v1 x1) with
        | 0 => (a , b)
        | _ => assoc_ctx_opt x ctx'
      end)
      | (Gensym (v1, t1)), Gensym (v2, t2) => 
      (match (string_compare v1 v2) with
        | 0 => 
        (match nat_compare t1 t2 with
          | 0 => (a, b)
          | _ => assoc_ctx_opt x ctx'
        end)
        | _ => assoc_ctx_opt x ctx'
        end)
      | _, _ => assoc_ctx_opt x ctx'
      end)
  end.
Check assoc_opt.

Definition lookup_ty_opt (x: variable) (ctx: context) := fst (assoc_ctx_opt x ctx).
Check lookup_ty_opt.

Definition lookup_val_opt (x: variable) (ctx: context) := snd (assoc_ctx_opt x ctx).
Check lookup_val_opt.

Fixpoint normalize (ctx: context) (e: expr) {struct e}: expr :=
  match e with
    | Var x => 
      (match lookup_val_opt x ctx with
        | None    => Var x
        | Some e' => e' (* normalize ctx e' *)
     end)
    | App (e1, e2) =>
      let u2 := normalize ctx e2 in
      let u1 := normalize ctx e1 in
    	(match u1 with
         | Lambda (x, _, e1') => (subst [(x,u2)] e1') (*normalize (subst [(x,u2)] e1')*)
         | e1 => App (e1, u2)
        end)
    | Universe k       => Universe k
    | Pi (x, t, e)     => Pi (let t' := normalize ctx t in (x, t', (normalize (extend x t' None ctx) e)))
    | Lambda (x, t, e) => Lambda (let t' := normalize ctx t in (x, t', (normalize (extend x t' None ctx) e)))
 end.
Check normalize.

(*
Definition l := ((Str "c", (Universe 0%nat, None)) :: (Str "f", (Universe 0%nat, Some (Var (Str "cagin")))) ::
  ((Gensym ("b", 2%nat)), (Universe 0%nat, None)) :: 
  (Str "a", (Universe 0%nat, Some (Var (Str "Cagin ekici")))):: ((Gensym ("d", 0%nat)), (Universe 0%nat, None)) :: 
  (Str "a+325", (Universe 0%nat, (Some (Var (Str "ekici"))))) :: nil).
Eval compute in normalize l (Var (Str "a+325")).
Eval compute in normalize l (App ((Lambda ((Str("x"), Universe 0, (Var (Str "a")) ))), (Var (Str "f")))).
Eval compute in lookup_val_opt (Str "f") l.
*)

Fixpoint equal (ctx: context) (e1 e2: expr): bool :=
  match e1, e2 with
    | Var x1, Var x2 => 
    (match x1, x2 with
      | Str s1, Str s2 => string_compare_b s1 s2
      | Gensym (v1, t1), Gensym (v2, t2) =>
      (match string_compare_b v1 v2 with
        | true => nat_compare_b t1 t2
        | _ => false
      end)
      | _, _ => false
    end)
    | App (e11, e12), App (e21, e22) => equal ctx e11 e21 && equal ctx e12 e22
    | Universe k1, Universe k2 => nat_compare_b k1 k2
    | Pi (x, t1, e1), Pi (y, t2, e2) =>  equal ctx t1 t2 && (equal ctx e1 (subst [(y, Var x)] e2))
    | Lambda (x, t1, e1), Lambda (y, t2, e2) => equal ctx t1 t2 && (equal ctx e1 (subst [(y, Var x)] e2))
    | (Var _ | App _ | Universe _ | Pi _ | Lambda _), _ => false
  end.
Check equal.
(*
Definition l := ((Str "c", Universe 5%nat) :: ((Gensym ("b", 2%nat)), Universe 0%nat) :: 
  (Str "a", Universe 10%nat):: ((Gensym ("d", 20%nat)), Universe 21%nat) :: (Str "a+325", Universe 0) :: nil).
Eval compute in equal l (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a+3250")) ))), 
  (Var (Str "x")))) (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a+3250")) ))), (Var (Str "x")))). 
Eval compute in equal l (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a")) ))), (Lambda ((Str("b"), Universe 2, (Var (Str "a+5")) )))))
 (Lambda ((Str("b"), Universe 2, (Var (Str "a+5")) ))).
*)

Definition compare_universe (e1 e2: option expr): option expr :=
  match e1, e2 with
    | Some (Universe k1), Some (Universe k2) => 
    (match (nat_compare k1 k2) with
      | 0 => Some (Universe k1)
      | 1 => Some (Universe k1)
      | _ => Some (Universe k2)
    end)
    | _, _ => None
  end.
Check compare_universe.
(* Eval compute in compare_universe (Some (Universe 210)) (Some (Universe 11)). *)

Fixpoint infer_type_opt (ctx: context) (e: expr) :=
  match e with 
    | Var x => Some (lookup_ty_opt x ctx)
    | Universe k => Some (Universe (k + 1))
    | Pi (x, t1, t2) =>
      let k1 := infer_type_opt ctx t1 in
      let k2 := infer_type_opt (extend x t1 (None) ctx) t2 in
        (compare_universe k1 k2) (* Universe (max k1 k2) *)
    | Lambda (x, t, e) => 
      let k := infer_type_opt ctx t in
        let ctx' := (extend x t (None) ctx) in
          let te := infer_type_opt ctx' e in
          (match te with
            | Some a => Some (Pi (x, t, a))
            | _      => None
          end)
    | App (e1, e2) => 
        let t1 := infer_type_opt ctx e1 in
          (match t1 with
            | Some (Pi (x, t, e)) => 
            (let t2 := infer_type_opt ctx e2 in
              (match t2 with
                | Some b => 
                (match (equal ctx t b) with
                  | true => Some (subst [(x, e2)] e)
                  | false => None
                end) 
                | _ => None
              end))
            | _ => None
           end)
   end.
Check infer_type_opt.

(*
Definition l := ((Str "c", (Universe 0%nat, None)) :: (Str "f", (Universe 0%nat, Some (Var (Str "cagin")))) ::
  ((Gensym ("b", 2%nat)), (Universe 0%nat, None)) :: 
  (Str "a", (Universe 0%nat, Some (Var (Str "Cagin ekici")))):: ((Gensym ("d", 0%nat)), (Universe 0%nat, None)) :: 
  (Str "a+325", (Universe 0%nat, (Some (Var (Str "ekici"))))) :: nil).
Eval compute in infer_type_opt l ((Lambda ((Str("a"), Universe 0, (Var (Str "a+325")) )))).
Eval compute in infer_type_opt l ((Pi ((Str("a"), Universe 0, (Var (Str "a+325")) )))).
Eval compute in infer_type_opt l (Universe 10).
Eval compute in infer_type_opt l  (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a+325")) ))),  (Var (Str "c")))).
*)

End Make.

