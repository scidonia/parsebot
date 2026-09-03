(* Smoke test: proves the toolchain (rocq-core + stdpp) compiles and that the
   `Parsebot` logical path resolves. Nothing project-specific yet. *)

From stdpp Require Import list.

Lemma smoke_concat : [1; 2] ++ [3] = [1; 2; 3].
Proof. reflexivity. Qed.
