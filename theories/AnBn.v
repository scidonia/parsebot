(* S1 — hand-written certified recogniser for a^n b^n.
   Establishes the index-based Dec(Σ …) shape with computable negative
   evidence, before any synthesis machinery exists (implementation plan §3 S1). *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.

Inductive Token := A | B.
Definition Input := list Token.

Definition tok (w : Input) (i : nat) : option Token := nth_error w i.

(* a^n b^n : w[i .. j) is balanced. Index-based segment relation. *)
Inductive AnBn : Input -> nat -> nat -> Type :=
| AB_nil  : forall (w : Input) (i : nat), AnBn w i i
| AB_cons : forall (w : Input) (i j : nat),
    tok w i = Some A ->
    AnBn w (S i) j ->
    tok w j = Some B ->
    AnBn w i (S j).

(* Dec P := {P} + {~P}, over Type (proof-relevant). *)
Inductive Dec (P : Type) : Type :=
| yes : P -> Dec P
| no  : (P -> False) -> Dec P.

Arguments yes {P}.
Arguments no  {P}.

(* Decidable token-presence tests. *)
Lemma some_B_not_some_A : Some B <> Some A. Proof. congruence. Qed.
Lemma none_not_some_A   : None <> Some A.   Proof. congruence. Qed.
Lemma some_A_not_some_B : Some A <> Some B. Proof. congruence. Qed.
Lemma none_not_some_B   : None <> Some B.   Proof. congruence. Qed.

Definition is_A (t : option Token) : Dec (t = Some A).
Proof.
  destruct t as [c |].
  - destruct c.
    + apply yes. reflexivity.
    + apply no. congruence.
  - apply no. congruence.
Defined.

Definition is_B (t : option Token) : Dec (t = Some B).
Proof.
  destruct t as [c |].
  - destruct c.
    + apply no. congruence.
    + apply yes. reflexivity.
  - apply no. congruence.
Defined.

(* Negative evidence. *)

Lemma ab_empty_impossible (w : Input) (i : nat) : AnBn w (S i) 0 -> False.
Proof.
  intros d. inversion d; subst; congruence.
Qed.

Lemma ab_first_not_a (w : Input) (i j : nat) :
  i <> S j -> tok w i <> Some A -> AnBn w i (S j) -> False.
Proof.
  intros ne fA d. inversion d; subst.
  - exfalso. apply ne. reflexivity.
  - exfalso. apply fA. assumption.
Qed.

Lemma ab_last_not_b (w : Input) (i j : nat) :
  i <> S j -> tok w i = Some A -> tok w j <> Some B -> AnBn w i (S j) -> False.
Proof.
  intros ne eA fB d. inversion d; subst.
  - exfalso. apply ne. reflexivity.
  - exfalso. apply fB. assumption.
Qed.

Lemma ab_inner_no (w : Input) (i j : nat) :
  i <> S j -> tok w i = Some A -> tok w j = Some B ->
  (AnBn w (S i) j -> False) -> AnBn w i (S j) -> False.
Proof.
  intros ne eA eB f d. inversion d; subst.
  - exfalso. apply ne. reflexivity.
  - exfalso. apply f. assumption.
Qed.

(* The certified recogniser: parse_ab w i j decides AnBn w i j.
   Structural recursion on the end index j; positions are concrete S-stacks,
   so no nat addition appears in the recogniser. *)
Fixpoint parse_ab (w : Input) (i j : nat) {struct j} : Dec (AnBn w i j) :=
  match j return Dec (AnBn w i j) with
  | O =>
      match i return Dec (AnBn w i 0) with
      | O    => yes (AB_nil w 0)
      | S i' => no (ab_empty_impossible w i')
      end
  | S j' =>
      match Nat.eq_dec i (S j') with
      | left e =>
          yes (eq_rect i (fun k => AnBn w i k) (AB_nil w i) (S j') e)
      | right ne =>
          match is_A (tok w i) with
          | no fA => no (ab_first_not_a w i j' ne fA)
          | yes eA =>
              match is_B (tok w j') with
              | no fB => no (ab_last_not_b w i j' ne eA fB)
              | yes eB =>
                  match parse_ab w (S i) j' with
                  | no f => no (ab_inner_no w i j' ne eA eB f)
                  | yes d => yes (AB_cons w i j' eA d eB)
                  end
              end
          end
      end
  end.

(* Whole-input parser. *)
Definition parse (w : Input) : Dec (AnBn w 0 (length w)) :=
  parse_ab w 0 (length w).
