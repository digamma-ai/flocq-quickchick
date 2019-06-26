Require Import Generators.
Require Import ZArith PArith Bool.BoolEq List.
Require Import Flocq.IEEE754.Binary.
Import ListNotations.
From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

Theorem nan1 : nan_pl 24 1 = true.
Proof. auto. Qed.

(* Let's define our own equality on binary_float's *)
Definition binary_eqb {prec emax : Z} 
           (b1 b2 : binary_float prec emax) : bool :=
  match b1, b2 with
    | B754_zero s1, B754_zero s2 => eqb s1 s2
    | B754_infinity s1, B754_infinity s2 => eqb s1 s2
    | B754_nan s1 pl1 _, B754_nan s2 pl2 _ => 
      ((eqb s1 s2) && (Pos.eqb pl1 pl2))%bool
    | B754_finite s1 m1 e1 _, B754_finite s2 m2 e2 _ => 
      ((eqb s1 s2) && (Pos.eqb m1 m2) && (Z.eqb e1 e2))%bool
    | _, _ => false
  end.

(* Then we formulate a false theorem on our new equality basis *)
Theorem example1 (b1 b2 : binary32) : binary_eqb b1 b2 = true.
Admitted.

(* To test it we need to make a custom generator like this *)
Definition binary_pair_generator (pl : positive) 
           (nan_p : nan_pl 24 pl = true) : G (binary32 * binary32) :=
  bindGen (binary32_gen 1 nan1) (fun b1 => 
    bindGen (binary32_gen 1 nan1) (fun b2 =>
      returnGen (b1, b2))).

(* We can try to run this test and see that it fails *)
QuickChick (forAll 
              (binary_pair_generator 1 nan1) 
              (fun '(b1, b2) => binary_eqb b1 b2)).

(* Let's now say that you want to work with 
   specific binary_float constructors. For example,
   B754_zero and B754_infinity. *)
Definition convert {prec emax : Z} (b: binary_float prec emax) 
  : binary_float prec emax := 
  match b with
    | B754_zero s => B754_infinity prec emax s
    | B754_infinity s => B754_zero prec emax s
    | _ => B754_zero prec emax true
  end.

(* Here we define new custom generator for our test *)
Definition zer_inf_gen := oneOf_ zerg32 [zerg32 ; infg32].

(* Let's define testing function *)
Definition mirrorb (b1 : binary32) :=
  binary_eqb (convert (convert b1)) b1.

(* All tests passed *)
QuickChick (forAll (zer_inf_gen) mirrorb).
