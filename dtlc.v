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

Module Type T.

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

Check Lambda ((Str("x"), Universe 0, (Var (Str "x+5")) )).

Definition context := list (variable * expr).
Check context.

Fixpoint nat_compare_b (n m: nat) : bool :=
  match n with
    | 0%nat  => 
    match m with
      | 0%nat => true
      | _ => false
    end
    | S x => 
    match m with
      | 0%nat => false
      | S y => nat_compare_b x y
    end
  end.

Fixpoint string_compare_b (s1 s2: string): bool :=
  match s1, s2 with
    | EmptyString,  EmptyString  => true
    | EmptyString,  String a s2' => false
    | String a s1', EmptyString  => false
    | String a s1', String b s2' =>
    match ascii_dec a b with
      | left _  => string_compare_b s1' s2'
      | right _ =>  nat_compare_b (nat_of_ascii a) (nat_of_ascii b)
    end
  end.

Fixpoint nat_compare (n m: nat) : Z :=
  match n with
    | 0%nat  => 
    match m with
      | 0%nat => 0
      | _ => -1
    end
    | S x => 
    match m with
      | 0%nat => 1
      | S y => nat_compare x y
    end
  end.

Fixpoint string_compare (s1 s2: string): Z :=
  match s1, s2 with
    | EmptyString,  EmptyString  => 0
    | EmptyString,  String a s2' => -1
    | String a s1', EmptyString  => 1
    | String a s1', String b s2' =>
    match ascii_dec a b with
      | left _  => string_compare s1' s2'
      | right _ =>  nat_compare (nat_of_ascii a) (nat_of_ascii b)
    end
  end.

Fixpoint assoc (x: variable) (ctx: context) {struct ctx}: option expr :=
  match ctx with
    | nil => None
    | ((v, a) :: ctx') => 
    (match v, x with
      | Str v1, Str x1 => 
      (match (string_compare v1 x1) with
        | 0 => Some a
        | _ => assoc x ctx'
      end)
      | Gensym (v1, t1), Gensym (v2, t2) => 
      (match (string_compare v1 v2) with
        | 0 => 
        (match nat_compare t1 t2 with
          | 0 => Some a
          | _ => assoc x ctx'
        end)
        | _ => assoc x ctx'
        end)
      | _, _ => assoc x ctx'
      end)
  end.

(** [lookup_ty x ctx] returns the type of [x] in context [ctx]. *)
Definition lookup_ty (x: variable) (ctx: context) := (assoc x ctx).

(*
Definition l := ((Str "c", Universe 5%nat) :: ((Gensym ("b", 2%nat)), Universe 0%nat) :: 
  (Str "a", Universe 10%nat):: ((Gensym ("d", 20%nat)), Universe 21%nat) :: nil).
Eval compute in assoc (Str "c") l.
Eval compute in assoc (Gensym ("b", 2%nat)) l.
Eval compute in assoc (Gensym ("d", 20%nat)) l.
Eval compute in assoc (Str "a") l.
*)

Definition extend (x: variable) (t: expr) (ctx: context) := (x, t) :: ctx.

(*
Definition l := ((Str "c", Universe 5%nat) :: ((Gensym ("b", 2%nat)), Universe 0%nat) :: 
  (Str "a", Universe 10%nat):: ((Gensym ("d", 20%nat)), Universe 21%nat) :: nil).
Eval compute in extend (Str "a") (Universe 10) l.
Eval compute in extend (Gensym ("d", 20%nat)) (Universe 21) l. 
*)

Definition incr (n: nat) := S n.

(** [refresh x] generates a fresh variable name whose preferred form is [x]. *)
Definition refresh (v: variable) := 
  let k := 0%nat in
    match v with
      | Str x => Gensym (x, incr k)
      | Gensym (x, _) =>  Gensym (x, incr k)
   end.

Fixpoint subst (s: list (variable * expr)) (e: expr) {struct e}: expr :=
    match e with
      | Var x                  => 
      (match assoc x s with
        | None => Var x
        | Some a => a
      end)
      | Universe k       => Universe k
      | Pi (x, t, e)     => Pi (let x' := refresh x in (x', subst s t, subst ((x, Var x') :: s) e))
      | Lambda (x, t, e) => Lambda (let x' := refresh x in (x', subst s t, subst ((x, Var x') :: s) e))
      | App (e1, e2)     => App (subst s e1, subst s e2)
    end.

(*
Definition l := ((Str "c", Universe 5%nat) :: ((Gensym ("b", 2%nat)), Universe 0%nat) :: 
  (Str "a", Universe 10%nat):: ((Gensym ("d", 20%nat)), Universe 21%nat) :: nil).
Eval compute in subst l (Lambda ((Str("a"), Universe 0, (Var (Str "a+5")) ))).
Eval compute in subst l (Pi ((Str("a"), Universe 0, (Var (Str "a+5")) ))).
Eval compute in subst l (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a")) ))), (Lambda ((Str("b"), Universe 2, (Var (Str "a+5")) ))))).
*)

Fixpoint normalize (ctx: context) (e: expr) {struct e}: expr :=
  match e with
    | Var x => 
      (match lookup_ty x ctx with
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
    | Pi (x, t, e)     => Pi (let t := normalize ctx t in (x, t, (normalize (extend x t ctx) e)))
    | Lambda (x, t, e) => Lambda (let t := normalize ctx t in (x, t, (normalize (extend x t ctx) e)))
 end.

(*
Definition l := ((Str "c", Universe 5%nat) :: ((Gensym ("b", 2%nat)), Universe 0%nat) :: 
  (Str "a", Universe 10%nat):: ((Gensym ("d", 20%nat)), Universe 21%nat) :: (Str "a+325", Universe 0) :: nil).
Eval compute in normalize l (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a+3250")) ))), (Var (Str "x")))). 
Eval compute in normalize l (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a")) ))), (Lambda ((Str("b"), Universe 2, (Var (Str "a+5")) ))))).
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

Eval compute in compare_universe (Some (Universe 210)) (Some (Universe 11)).

Fixpoint infer_type_opt (ctx: context) (e: expr) :=
  match e with 
    | Var x => lookup_ty x ctx
    | Universe k => Some (Universe (k + 1))
    | Pi (x, t1, t2) =>
      let k1 := infer_type_opt ctx t1 in
      let k2 := infer_type_opt (extend x t1 ctx) t2 in
        (compare_universe k1 k2) (* Universe (max k1 k2) *)
    | Lambda (x, t, e) => 
      let k := infer_type_opt ctx t in
        let ctx' := (extend x t ctx) in
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

(*
Definition l := ((Str "c", Universe 0%nat) :: ((Gensym ("b", 2%nat)), Universe 0%nat) :: 
  (Str "a", Universe 10%nat):: ((Gensym ("d", 20%nat)), Universe 21%nat) :: (Str "a+325", Universe 200) :: nil).
Eval compute in infer_type_opt l ((Lambda ((Str("a"), Universe 0, (Var (Str "a+325")) )))).
Eval compute in infer_type_opt l ((Pi ((Str("a"), Universe 0, (Var (Str "a+325")) )))).
Eval compute in infer_type_opt l  (App ((Lambda ((Str("a"), Universe 0, (Var (Str "a+325")) ))),  (Var (Str "c")))).
*)

End T.













