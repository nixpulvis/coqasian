Section BasicImplication.

Theorem proof_is_proof : (forall A : Prop, A -> A).
Proof.
    intros A.
    intros proof_of_A.
    exact proof_of_A.
Qed.

Theorem forward_implication : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
    intros A B.
    intros proof_of_A A_implies_B.
    pose (proof_of_B := A_implies_B proof_of_A).
    exact proof_of_B.
Qed.

Theorem forward_implication_chained : (forall A B C : Prop, A -> (A -> B) -> (B -> C) -> C).
Proof.
    intros A B C.
    intros proof_of_A A_implies_B B_implies_C.
    pose (proof_of_B := A_implies_B proof_of_A).
    pose (proof_of_C := B_implies_C proof_of_B).
    exact proof_of_C.
Qed.

Theorem backward_implication : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
    intros A B.
    intros proof_of_A A_implies_B.
    refine (A_implies_B _).
        exact proof_of_A.
Qed.

Theorem backward_implication_chained : (forall A B C : Prop, A -> (A -> B) -> (B -> C) -> C).
Proof.
    intros A B C.
    intros proof_of_A A_implies_B B_implies_C.
    refine (B_implies_C _).
        refine (A_implies_B _).
        exact proof_of_A.
Qed.

End BasicImplication.

Section Booleans.

(* A proposition with no proofs. This `False` could be thought of as
*  Unprovable. *)
Inductive False : Prop := .
(* A proposition with a single proof `I`. This `True` could be thought of
*  as Provable. *)
Inductive True : Prop :=
    | I : True.

Theorem True_can_be_proven : True.
    exact I.
Qed.

(* In the example a Definition of `not` is introduced here as:
 * ```
 * Definition not (A : Prop) := A -> False.
 * ```
 * However I've skipped this here to avoid needing to unfold it... *)

(* I'm a bit confused as to what this really shows. I know that
 * `(forall p : False, X)` can only ever possibly have `False` for `X`, but
 * I don't understand how this proves it. *)
Theorem False_cannot_be_proven : (forall proof_of_False : False, False).
    intros proof_of_False.
    exact proof_of_False.
Qed.

(* This makes a bit more sense, but I'm still not 100% on the `forall` *)
Theorem False_cannot_be_proven_again : (forall proof_of_False : False, False).
    intros proof_of_False.
    case proof_of_False.
Qed.

Inductive bool : Set :=
    | true  : bool
    | false : bool.

End Booleans.
