(* Example — first concrete instantiation of the Spec calculus.
   A two-token grammar "A B" over the AnBn token alphabet, with a hand-built
   proof-relevant derivation. Shows the calculus works externally (after the
   section-closing Argument re-declaration in Spec.v). *)

From Stdlib Require Import List.
Import ListNotations.
From Parsebot Require Import Spec AnBn.
Import AnBn.

(* Token predicates. *)
Definition is_A (t : Token) : Type := t = A.
Definition is_B (t : Token) : Type := t = B.

(* The spec: the token sequence "A B", producing the pair (A, B). No environment
   (unit) and no nonterminals (the empty family). *)
Definition ab_spec : Spec Token unit (fun _ : Type => Empty_set) (Token * Token) :=
  Seq (Tok is_A) (Tok is_B).

(* The (unique) grammar for the empty nonterminal family. *)
Definition no_nts : Grammar Token unit (fun _ : Type => Empty_set) :=
  fun A n => match n with end.

(* A proof-relevant derivation: input [A; B] parses to (A, B), consuming exactly
   2 tokens. Parsing is constructive proof search for an inhabitant of denote. *)
Definition d_ab : denote no_nts [A; B] ab_spec tt 0 (A, B) tt 2.
Proof.
  unfold ab_spec.
  econstructor.          (* d_seq *)
  - econstructor; reflexivity.   (* d_tok: consume A at position 0 *)
  - econstructor; reflexivity.   (* d_tok: consume B at position 1 *)
Defined.
