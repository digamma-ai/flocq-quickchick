Require Import FlocqQuickChick.Generators.
Require Import ZArith PArith Bool.BoolEq List Bool.BoolEq.
Require Import Flocq.IEEE754.Binary.
Import ListNotations.
From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

Theorem nan1 : nan_pl 24 1 = true.
Proof. auto. Qed.

Definition Float_maxnum {prec emax : Z} (a b : binary_float prec emax) :=
  match (Bcompare prec emax a b) with
    | (Some Eq) => Some a
    | (Some Lt) => Some b
    | (Some Gt) => Some a
    | None => None
  end.

Definition predicate {prec emax : Z} (a b : binary_float prec emax) :=
  match Float_maxnum a b with
    | (Some m) => (*m >= a && m >= b && ((m = a) || (m = b))*)
      match Bcompare prec emax m a with
        | (Some Eq) | (Some Gt) => 
          match Bcompare prec emax m b with
            | (Some Eq) | (Some Gt) => 
              match Bcompare prec emax m a with
                | (Some Eq) => true
                | _ => 
                  match Bcompare prec emax m b with
                    | (Some Eq) => true
                    | _ => false
                  end
              end
            | _ => false
          end
        | _ => false
      end
    | None => false
  end.

Definition pair_fin32_gen : G (binary32 * binary32) := 
  bindGen (fing32) (fun b1 =>
    bindGen (fing32) (fun b2 =>
      returnGen (b1, b2))).

QuickChick (forAll pair_fin32_gen (fun '(b1, b2) => predicate b1 b2)).
