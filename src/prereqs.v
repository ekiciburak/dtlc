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

End T.