(* S2 — deep-embedded specification calculus with proof-relevant denotation.
   Implementation plan §3 S2.

   Deviation from the plan's `Many : Progress S -> …` signature: `Progress` is a
   separate inductive defined *after* `Spec`, not threaded through `Many`. Coq's
   mutual-inductive `with` clause cannot express `Progress`'s dependent arity
   (`forall A, Spec Γ N A -> Type` — the `forall` makes the co-defined `Spec`
   invisible), and `denote` ignores `Progress` anyway: it is termination evidence
   for the parser, threaded by `Searchable` in S4, not by the relation. *)

From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Section SpecCore.

Context (Token : Type).

(* The declarative core: a specification is a deep term over combinators.
   N : Type -> Type is the family of nonterminal names; recursion goes through
   Call n, unfolded by a grammar (Grammar Γ N). See implementation plan §3 S2. *)
Inductive Spec (Γ : Type) (N : Type -> Type) : Type -> Type :=
| Pure  : forall A, A -> Spec Γ N A
| Fail  : forall A, Spec Γ N A
| Tok   : (Token -> Type) -> Spec Γ N Token
| Seq   : forall A B, Spec Γ N A -> Spec Γ N B -> Spec Γ N (A * B)
| Alt   : forall A, Spec Γ N A -> Spec Γ N A -> Spec Γ N A
| Map   : forall A B, (A -> B) -> Spec Γ N A -> Spec Γ N B
| Bind  : forall A B, Spec Γ N A -> (A -> Spec Γ N B) -> Spec Γ N B
| Guard : forall A, (A -> Type) -> Spec Γ N A -> Spec Γ N A
| Many  : forall A, Spec Γ N A -> Spec Γ N (list A)
| Exactly : forall A, nat -> Spec Γ N A -> Spec Γ N (list A)
| Get   : Spec Γ N Γ
| Put   : Γ -> Spec Γ N unit
| Local : forall A, Spec Γ N A -> Spec Γ N A
| Call  : forall A, N A -> Spec Γ N A.

Arguments Pure  {Γ} {N} {A} _.
Arguments Fail  {Γ} {N} {A}.
Arguments Tok   {Γ} {N} _.
Arguments Seq   {Γ} {N} {A} {B} _ _.
Arguments Alt   {Γ} {N} {A} _ _.
Arguments Map   {Γ} {N} {A} {B} _ _.
Arguments Bind  {Γ} {N} {A} {B} _ _.
Arguments Guard {Γ} {N} {A} _ _.
Arguments Many  {Γ} {N} {A} _.
Arguments Exactly {Γ} {N} {A} _ _.
Arguments Get   {Γ} {N}.
Arguments Put   {Γ} {N} _.
Arguments Local {Γ} {N} {A} _.
Arguments Call  {Γ} {N} {A} _.

(* Progress s : sufficient structural evidence that s consumes at least one
   token whenever it succeeds. Needed to make Many terminate; used by Searchable
   (S4). Many itself does NOT progress (it may match zero repetitions), and Call
   is deferred (its progress depends on the grammar's productions). *)
Inductive Progress (Γ : Type) (N : Type -> Type) : forall A, Spec Γ N A -> Type :=
| P_tok    : forall (P : Token -> Type), Progress Γ N Token (Tok P)
| P_seq_l  : forall A B (s1 : Spec Γ N A) (s2 : Spec Γ N B), Progress Γ N A s1 -> Progress Γ N (A * B) (Seq s1 s2)
| P_seq_r  : forall A B (s1 : Spec Γ N A) (s2 : Spec Γ N B), Progress Γ N B s2 -> Progress Γ N (A * B) (Seq s1 s2)
| P_alt    : forall A (s1 s2 : Spec Γ N A), Progress Γ N A s1 -> Progress Γ N A s2 -> Progress Γ N A (Alt s1 s2)
| P_map    : forall A B (f : A -> B) (s : Spec Γ N A), Progress Γ N A s -> Progress Γ N B (Map f s)
| P_bind_l : forall A B (s : Spec Γ N A) (f : A -> Spec Γ N B), Progress Γ N A s -> Progress Γ N B (Bind s f)
| P_guard  : forall A (P : A -> Type) (s : Spec Γ N A), Progress Γ N A s -> Progress Γ N A (Guard P s)
| P_local  : forall A (s : Spec Γ N A), Progress Γ N A s -> Progress Γ N A (Local s)
| P_exactly : forall A (n : nat) (s : Spec Γ N A), Progress Γ N A s -> Progress Γ N (list A) (Exactly (S n) s).

Arguments Progress {Γ} {N} {A} _.

(* A grammar is a finite map of nonterminal names to their productions. *)
Definition Grammar (Γ : Type) (N : Type -> Type) := forall A, N A -> Spec Γ N A.

(* Proof-relevant denotation: denote G S γ i a γ' j is the type of derivations
   showing S, begun in environment γ at position i, produces a and finishes in
   γ' at j. Inductive (a relation), so Call unfolds via the grammar with no
   termination obligation at the spec level. *)
Section Denote.
Context (Γ : Type) (N : Type -> Type).
Variable (G : Grammar Γ N) (w : list Token).

Inductive denote : forall A, Spec Γ N A -> Γ -> nat -> A -> Γ -> nat -> Type :=
| d_pure : forall A (a : A) (γ : Γ) (i : nat),
    denote A (Pure a) γ i a γ i
| d_tok  : forall (P : Token -> Type) (t : Token) (γ : Γ) (i : nat),
    nth_error w i = Some t -> P t -> denote Token (Tok P) γ i t γ (S i)
| d_seq  : forall A B (s1 : Spec Γ N A) (s2 : Spec Γ N B) (γ γ' γ'' : Γ) (i j k : nat) (a : A) (b : B),
    denote A s1 γ i a γ' j -> denote B s2 γ' j b γ'' k -> denote (A * B) (Seq s1 s2) γ i (a, b) γ'' k
| d_alt_l : forall A (s1 s2 : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
    denote A s1 γ i a γ' j -> denote A (Alt s1 s2) γ i a γ' j
| d_alt_r : forall A (s1 s2 : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
    denote A s2 γ i a γ' j -> denote A (Alt s1 s2) γ i a γ' j
| d_map  : forall A B (f : A -> B) (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
    denote A s γ i a γ' j -> denote B (Map f s) γ i (f a) γ' j
| d_bind : forall A B (s : Spec Γ N A) (f : A -> Spec Γ N B) (γ γ' γ'' : Γ) (i j k : nat) (a : A) (b : B),
    denote A s γ i a γ' j -> denote B (f a) γ' j b γ'' k -> denote B (Bind s f) γ i b γ'' k
| d_guard : forall A (P : A -> Type) (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
    P a -> denote A s γ i a γ' j -> denote A (Guard P s) γ i a γ' j
| d_many_nil : forall A (s : Spec Γ N A) (γ : Γ) (i : nat),
    denote (list A) (Many s) γ i nil γ i
| d_many_cons : forall A (s : Spec Γ N A) (γ γ' γ'' : Γ) (i j k : nat) (a : A) (as_ : list A),
    denote A s γ i a γ' j -> denote (list A) (Many s) γ' j as_ γ'' k ->
    denote (list A) (Many s) γ i (a :: as_) γ'' k
| d_exactly_nil : forall A (s : Spec Γ N A) (γ : Γ) (i : nat),
    denote (list A) (Exactly 0 s) γ i nil γ i
| d_exactly_cons : forall A (n : nat) (s : Spec Γ N A) (γ γ' γ'' : Γ) (i j k : nat) (a : A) (as_ : list A),
    denote A s γ i a γ' j -> denote (list A) (Exactly n s) γ' j as_ γ'' k ->
    denote (list A) (Exactly (S n) s) γ i (a :: as_) γ'' k
| d_get : forall (γ : Γ) (i : nat),
    denote Γ Get γ i γ γ i
| d_put : forall (γ γ2 : Γ) (i : nat),
    denote unit (Put γ2) γ i tt γ2 i
| d_local : forall A (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
    denote A s γ i a γ' j -> denote A (Local s) γ i a γ j
| d_call : forall A (n : N A) (γ γ' : Γ) (i j : nat) (a : A),
    denote A (G A n) γ i a γ' j -> denote A (Call n) γ i a γ' j.

Arguments denote {A} _ _ _ _ _ _ : assert.

(* Type-level equivalence: denote is proof-relevant (Type-valued), so the laws
   use a Type-level iff over sigT (exists) and prod (and). *)
Notation "A × B" := (prod A B) (at level 40, no associativity).
Notation "A ⊕ B" := (sum A B) (at level 50, no associativity).

Definition iffT (A B : Type) : Type := (A -> B) × (B -> A).
Notation "A <->t B" := (iffT A B) (at level 95, no associativity).
Ltac invert_d :=
  inversion d; subst;
  repeat (match goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] => dependent destruction H
          end).
Ltac simpl_iff := repeat split; try reflexivity; try eassumption.

(* Compositional laws: each constructor is an exact characterization. *)

Lemma denote_pure_iff : forall A (a : A) (γ : Γ) (i : nat) (a' : A) (γ' : Γ) (j : nat),
  denote (Pure a) γ i a' γ' j <->t ((a' = a) × (γ' = γ) × (j = i)).
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. simpl_iff.
  - intros [[Ea Eg] Ej]. subst. constructor.
Qed.

Lemma denote_fail_elim : forall A (γ : Γ) (i : nat) (a : A) (γ' : Γ) (j : nat),
  denote Fail γ i a γ' j -> False.
Proof.
  intros A γ i a γ' j d. inversion d.
Qed.

Lemma denote_tok_iff : forall (P : Token -> Type) (t : Token) (γ γ' : Γ) (i j : nat),
  denote (Tok P) γ i t γ' j <->t ((γ' = γ) × (j = S i) × (nth_error w i = Some t) × P t).
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. simpl_iff.
  - intros [[[Eg Ej] Et] Pt]. subst. econstructor; eauto.
Qed.

Lemma denote_seq_iff : forall A B (s1 : Spec Γ N A) (s2 : Spec Γ N B) (γ γ'' : Γ) (i k : nat) (ab : A × B),
  denote (Seq s1 s2) γ i ab γ'' k <->t
  { γ' : Γ & { j : nat & { a : A & { b : B & (ab = (a, b)) × denote s1 γ i a γ' j × denote s2 γ' j b γ'' k }}}}.
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d.
    eexists; eexists; eexists; eexists. simpl_iff.
  - intros [γ' [j [a [b [[Eab d1] d2]]]]]. subst. econstructor; eassumption.
Qed.

Lemma denote_alt_iff : forall A (s1 s2 : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
  denote (Alt s1 s2) γ i a γ' j <->t (denote s1 γ i a γ' j ⊕ denote s2 γ i a γ' j).
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d; [left; eassumption | right; eassumption].
  - intros [d | d]; econstructor; eassumption.
Qed.

Lemma denote_map_iff : forall A B (f : A -> B) (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (b : B),
  denote (Map f s) γ i b γ' j <->t { a : A & (b = f a) × denote s γ i a γ' j }.
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. eexists. simpl_iff.
  - intros [a [Eb d]]. subst. econstructor; eassumption.
Qed.

Lemma denote_bind_iff : forall A B (s : Spec Γ N A) (f : A -> Spec Γ N B) (γ γ'' : Γ) (i k : nat) (b : B),
  denote (Bind s f) γ i b γ'' k <->t
  { γ' : Γ & { j : nat & { a : A & (denote s γ i a γ' j × denote (f a) γ' j b γ'' k) }}}.
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. eexists; eexists; eexists. simpl_iff.
  - intros [γ' [j [a [d1 d2]]]]. econstructor; eassumption.
Qed.

Lemma denote_guard_iff : forall A (P : A -> Type) (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
  denote (Guard P s) γ i a γ' j <->t (P a × denote s γ i a γ' j).
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. simpl_iff.
  - intros [Pa d]. econstructor; eassumption.
Qed.

Lemma denote_many_iff : forall A (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (as_ : list A),
  denote (Many s) γ i as_ γ' j <->t
  ((as_ = nil) × (γ' = γ) × (j = i)) ⊕
  { a : A & { as' : list A & { γ'' : Γ & { k : nat &
    (as_ = a :: as') × denote s γ i a γ'' k × denote (Many s) γ'' k as' γ' j }}}}.
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d.
    + left. simpl_iff.
    + right. eexists; eexists; eexists; eexists. simpl_iff.
  - intros [[[Eas Eg] Ej] | [a [as' [γ'' [k [[Eas2 d1] d2]]]]]].
    + subst. constructor.
    + subst. econstructor; eassumption.
Qed.

Lemma denote_exactly_iff : forall A (n : nat) (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (as_ : list A),
  denote (Exactly n s) γ i as_ γ' j <->t
  ((n = 0) × (as_ = nil) × (γ' = γ) × (j = i)) ⊕
  { n' : nat & { a : A & { as' : list A & { γ'' : Γ & { k : nat &
    (n = S n') × (as_ = a :: as') × denote s γ i a γ'' k × denote (Exactly n' s) γ'' k as' γ' j }}}}}.
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d.
    + left. simpl_iff.
    + right. eexists; eexists; eexists; eexists; eexists. simpl_iff.
  - intros [[[[En Eas] Eg] Ej] | [n' [a [as' [γ'' [k [[[En Eas] d1] d2]]]]]]].
    + subst. constructor.
    + subst. econstructor; eassumption.
Qed.

Lemma denote_get_iff : forall (γ γr γ' : Γ) (i j : nat),
  denote Get γ i γr γ' j <->t ((γr = γ) × (γ' = γ) × (j = i)).
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. simpl_iff.
  - intros [[Er Eg] Ej]. subst. constructor.
Qed.

Lemma denote_put_iff : forall (γ γ2 γ' : Γ) (i j : nat) (u : unit),
  denote (Put γ2) γ i u γ' j <->t ((u = tt) × (γ' = γ2) × (j = i)).
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. simpl_iff.
  - intros [[Eu Eg] Ej]. subst. constructor.
Qed.

Lemma denote_local_iff : forall A (s : Spec Γ N A) (γ γ' : Γ) (i j : nat) (a : A),
  denote (Local s) γ i a γ' j <->t ((γ' = γ) × { γmid : Γ & denote s γ i a γmid j }).
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d. split; [reflexivity | eexists; eassumption].
  - intros [Eg [γmid d]]. subst. econstructor; eassumption.
Qed.

Lemma denote_call_iff : forall A (n : N A) (γ γ' : Γ) (i j : nat) (a : A),
  denote (Call n) γ i a γ' j <->t denote (G A n) γ i a γ' j.
Proof.
  intros. unfold iffT. split.
  - intros d. invert_d; eassumption.
  - intros d. econstructor; eassumption.
Qed.

End Denote.
End SpecCore.

(* Section closing re-generalises `Token` as a leading argument, which resets
   the in-section `Arguments`. Re-declare them for the generalized constants.
   `Spec` and `Grammar` stay fully explicit (used in type annotations). *)
Arguments Pure  {Token} {Γ} {N} {A} _.
Arguments Fail  {Token} {Γ} {N} {A}.
Arguments Tok   {Token} {Γ} {N} _.
Arguments Seq   {Token} {Γ} {N} {A} {B} _ _.
Arguments Alt   {Token} {Γ} {N} {A} _ _.
Arguments Map   {Token} {Γ} {N} {A} {B} _ _.
Arguments Bind  {Token} {Γ} {N} {A} {B} _ _.
Arguments Guard {Token} {Γ} {N} {A} _ _.
Arguments Many  {Token} {Γ} {N} {A} _.
Arguments Get   {Token} {Γ} {N}.
Arguments Put   {Token} {Γ} {N} _.
Arguments Local {Token} {Γ} {N} {A} _.
Arguments Call  {Token} {Γ} {N} {A} _.
Arguments Progress {Token} {Γ} {N} {A} _.
Arguments denote {Token} {Γ} {N} _ _ {A} _ _ _ _ _ _.
