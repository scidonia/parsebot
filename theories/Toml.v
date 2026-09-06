(* S8 — TOML key/table state (TOML 1.0 document-level validity).

   A TOML document is a sequence of statements: key-value pairs, `[table]`
   headers, and `[[array-of-tables]]` headers.  Keys are dotted paths; the
   *namespace* records how each defined path was introduced.  A statement is
   valid iff its state transition is permitted:

     - a key may be defined at most once (duplicate key → invalid),
     - a `[table]` may not be redefined,
     - an `[[array-of-tables]]` may re-append (same path, again),
     - dotted keys create *implicit* tables for their prefixes.

   This slice is the state machine: the declarative relation `DocumentStep`,
   a certified decision procedure `run`, and runnable examples.  The
   character-level surface grammar (the BNF) is a separate stage. *)

From Stdlib Require Import List Bool Nat.
Import ListNotations.

(* ------------------------------------------------------------------------- *)
(* Model                                                                      *)
(* ------------------------------------------------------------------------- *)

(* A key is a non-empty dotted path of segment names.  (Abstract segments;
   the surface lexer maps bare/dotted keys onto these.) *)
Definition seg : Type := nat.
Definition key : Type := list seg.

(* How a path was introduced. *)
Inductive kind : Type :=
| KImplicit   (* an intermediate of a dotted key *)
| KTable      (* a [table] *)
| KArrayTable (* an [[array-of-tables]] *)
| KScalar.    (* a key = value leaf *)

Definition Namespace : Type := list (key * kind).

(* Statements. *)
Inductive stmt : Type :=
| SKV    (k : key) (v : nat)  (* k = v *)
| STable (k : key)            (* [k]   *)
| SArray (k : key).           (* [[k]] *)

Definition Document : Type := list stmt.

(* ------------------------------------------------------------------------- *)
(* Decidable equality for keys and kinds (needed by the decision procedure).  *)
(* ------------------------------------------------------------------------- *)

Fixpoint key_eqb (k1 k2 : key) : bool :=
  match k1, k2 with
  | [], [] => true
  | s1 :: r1, s2 :: r2 => Nat.eqb s1 s2 && key_eqb r1 r2
  | _, _ => false
  end.

Definition kind_eqb (k1 k2 : kind) : bool :=
  match k1, k2 with
  | KImplicit, KImplicit => true
  | KTable, KTable => true
  | KArrayTable, KArrayTable => true
  | KScalar, KScalar => true
  | _, _ => false
  end.

Lemma kind_eqb_eq : forall k1 k2, kind_eqb k1 k2 = true -> k1 = k2.
Proof.
  intros k1 k2 H. destruct k1, k2; simpl in H; try discriminate; reflexivity.
Qed.

(* Look up the (most recent) classification of a path. *)
Fixpoint lookup (ns : Namespace) (k : key) : option kind :=
  match ns with
  | [] => None
  | (k', v) :: rest => if key_eqb k k' then Some v else lookup rest k
  end.

(* ------------------------------------------------------------------------- *)
(* The state transition (semantics of one statement)                          *)
(* ------------------------------------------------------------------------- *)

(* Define a single-segment path as kind K. *)
Definition define_leaf (ns : Namespace) (s : seg) (K : kind) : option Namespace :=
  match lookup ns [s] with
  | None => Some (([s], K) :: ns)
  | Some KImplicit => Some (([s], K) :: ns)
  | Some KArrayTable => if kind_eqb K KArrayTable then Some ns else None
  | Some KTable | Some KScalar => None
  end.

(* Define a (possibly dotted) path as kind K.  Proper prefixes that are
   absent become implicit tables; a prefix that is a table continues; a
   prefix that is a scalar or an array-of-tables blocks the definition. *)
Fixpoint define (ns : Namespace) (k : key) (K : kind) : option Namespace :=
  match k with
  | [] => None
  | [s] => define_leaf ns s K
  | s :: rest =>
      match lookup ns [s] with
      | None => define (([s], KImplicit) :: ns) rest K
      | Some KImplicit | Some KTable => define ns rest K
      | Some KScalar | Some KArrayTable => None
      end
  end.

(* One statement's transition. *)
Definition step (ns : Namespace) (s : stmt) : option Namespace :=
  match s with
  | SKV k v => define ns k KScalar
  | STable k => define ns k KTable
  | SArray k => define ns k KArrayTable
  end.

(* Fold the transition over a document. *)
Fixpoint run (ns : Namespace) (doc : Document) : option Namespace :=
  match doc with
  | [] => Some ns
  | s :: rest =>
      match step ns s with
      | None => None
      | Some ns' => run ns' rest
      end
  end.

(* ------------------------------------------------------------------------- *)
(* Examples                                                                   *)
(* ------------------------------------------------------------------------- *)

(*   a = 1          →  a : Scalar
*    b.c = 2        →  b : Implicit,  b.c : Scalar
*    b.d = 3        →  b.d : Scalar  (b stays implicit)                     *)
Definition ex_valid : Document :=
  [SKV [1] 1; SKV [2;3] 2; SKV [2;4] 3].

(* duplicate key:  a = 1  then  a = 2 *)
Definition ex_dup_key : Document := [SKV [1] 1; SKV [1] 2].

(* table redefinition:  [a]  then  [a] *)
Definition ex_dup_table : Document := [STable [1]; STable [1]].

(* array re-append:  [[a]]  then  [[a]]  — allowed *)
Definition ex_array_append : Document := [SArray [1]; SArray [1]].

(* table under a scalar:  a = 1  then  [a.b] — blocked *)
Definition ex_table_under_scalar : Document := [SKV [1] 1; STable [1;2]].

Eval compute in run [] ex_valid.
Eval compute in run [] ex_dup_key.
Eval compute in run [] ex_dup_table.
Eval compute in run [] ex_array_append.
Eval compute in run [] ex_table_under_scalar.

(* ------------------------------------------------------------------------- *)
(* The declarative relation                                                   *)
(* ------------------------------------------------------------------------- *)

(* `defines ns k K ns'` : path k may be defined as kind K in namespace ns,
   yielding ns'.  The TOML rules, stated declaratively (not as the decision
   procedure). *)
Inductive defines : Namespace -> key -> kind -> Namespace -> Prop :=
| def_leaf_new : forall ns s K, lookup ns [s] = None -> defines ns [s] K (([s], K) :: ns)
| def_leaf_promote : forall ns s K, lookup ns [s] = Some KImplicit -> defines ns [s] K (([s], K) :: ns)
| def_leaf_array : forall ns s, lookup ns [s] = Some KArrayTable -> defines ns [s] KArrayTable ns
| def_cons_absent : forall ns s rest K ns',
    lookup ns [s] = None -> defines (([s], KImplicit) :: ns) rest K ns' -> defines ns (s :: rest) K ns'
| def_cons_implicit : forall ns s rest K ns',
    lookup ns [s] = Some KImplicit -> defines ns rest K ns' -> defines ns (s :: rest) K ns'
| def_cons_table : forall ns s rest K ns',
    lookup ns [s] = Some KTable -> defines ns rest K ns' -> defines ns (s :: rest) K ns'.

(* One statement's transition. *)
Inductive DocumentStep : Namespace -> stmt -> Namespace -> Prop :=
| DS_kv : forall ns k v ns', defines ns k KScalar ns' -> DocumentStep ns (SKV k v) ns'
| DS_table : forall ns k ns', defines ns k KTable ns' -> DocumentStep ns (STable k) ns'
| DS_array : forall ns k ns', defines ns k KArrayTable ns' -> DocumentStep ns (SArray k) ns'.

(* A whole document. *)
Inductive doc_valid : Namespace -> Document -> Namespace -> Prop :=
| doc_nil : forall ns, doc_valid ns [] ns
| doc_cons : forall ns s ns' doc ns'',
    DocumentStep ns s ns' -> doc_valid ns' doc ns'' -> doc_valid ns (s :: doc) ns''.

(* ------------------------------------------------------------------------- *)
(* The decision procedure agrees with the relation                            *)
(* ------------------------------------------------------------------------- *)

Lemma defines_define : forall ns k K ns', defines ns k K ns' -> define ns k K = Some ns'.
Proof.
  intros ns k K ns' H. induction H; simpl.
  - unfold define_leaf. rewrite H. reflexivity.
  - unfold define_leaf. rewrite H. reflexivity.
  - unfold define_leaf. rewrite H. reflexivity.
  - destruct rest as [| s2 rest'].
    + simpl in IHdefines. discriminate.
    + simpl. rewrite H. exact IHdefines.
  - destruct rest as [| s2 rest'].
    + simpl in IHdefines. discriminate.
    + simpl. rewrite H. exact IHdefines.
  - destruct rest as [| s2 rest'].
    + simpl in IHdefines. discriminate.
    + simpl. rewrite H. exact IHdefines.
Qed.

Lemma define_defines : forall k ns K ns', define ns k K = Some ns' -> defines ns k K ns'.
Proof.
  induction k as [| s rest IH]; intros ns K ns' H.
  - simpl in H. discriminate.
  - destruct rest as [| s2 rest'].
    + (* k = [s] *) simpl in H. unfold define_leaf in H.
      destruct (lookup ns [s]) as [k0 |] eqn:Hl.
      * destruct k0;
          [ injection H as Hns'; subst ns'; apply def_leaf_promote; exact Hl
          | discriminate
          | destruct (kind_eqb K KArrayTable) eqn:Hk;
              [ injection H as Hns'; subst ns'; apply kind_eqb_eq in Hk; subst K; apply def_leaf_array; exact Hl
              | discriminate ]
          | discriminate ].
      * injection H as Hns'. subst ns'. apply def_leaf_new. exact Hl.
    + (* k = s :: s2 :: rest' *) simpl in H.
      destruct (lookup ns [s]) as [k0 |] eqn:Hl; simpl in H.
      * destruct k0;
          [ change (define ns (s2 :: rest') K = Some ns') in H;
            apply (def_cons_implicit ns s (s2 :: rest') K ns' Hl); apply (IH ns K ns'); exact H
          | change (define ns (s2 :: rest') K = Some ns') in H;
            apply (def_cons_table ns s (s2 :: rest') K ns' Hl); apply (IH ns K ns'); exact H
          | discriminate
          | discriminate ].
      * change (define (([s], KImplicit) :: ns) (s2 :: rest') K = Some ns') in H;
        apply def_cons_absent. exact Hl. apply (IH (([s], KImplicit) :: ns) K ns'). exact H.
Qed.

Lemma step_step : forall ns s ns', step ns s = Some ns' -> DocumentStep ns s ns'.
Proof.
  destruct s; simpl; intros ns' H.
  - apply DS_kv. apply (define_defines k ns KScalar ns' H).
  - apply DS_table. apply (define_defines k ns KTable ns' H).
  - apply DS_array. apply (define_defines k ns KArrayTable ns' H).
Qed.

Lemma step_step' : forall ns s ns', DocumentStep ns s ns' -> step ns s = Some ns'.
Proof.
  intros ns s ns' H. inversion H; subst; simpl; apply defines_define; eassumption.
Qed.

Lemma run_sound : forall doc ns ns', run ns doc = Some ns' -> doc_valid ns doc ns'.
Proof.
  induction doc as [| s doc' IH]; intros ns ns' H.
  - simpl in H. injection H as Hns'. subst ns'. apply doc_nil.
  - simpl in H. destruct (step ns s) as [n |] eqn:E.
    + apply (doc_cons ns s n doc' ns' (step_step ns s n E) (IH n ns' H)).
    + discriminate.
Qed.

Lemma run_complete : forall ns doc ns', doc_valid ns doc ns' -> run ns doc = Some ns'.
Proof.
  intros ns doc ns' H. induction H; simpl.
  - reflexivity.
  - rewrite (step_step' ns s ns' H). exact IHdoc_valid.
Qed.

(* ------------------------------------------------------------------------- *)
(* DocumentStep through the Spec framework (Get / Guard / Put)                *)
(* ------------------------------------------------------------------------- *)

From Parsebot Require Import Spec.

(* No recursion in this fragment: the nonterminal family is empty. *)
Inductive tom_nt : Type -> Type := .

Definition tom_grammar : Grammar unit Namespace tom_nt :=
  fun (A : Type) (n : tom_nt A) => match n with end.

(* A statement is valid in ns: there is a resulting namespace. *)
Definition valid_step (ns : Namespace) (s : stmt) : Type :=
  { ns' : Namespace & DocumentStep ns s ns' }.

(* The state-indexed statement spec: read the namespace, check the statement's
   validity (declaratively), and write the new namespace.  Token = unit — the
   cursor stays 0; the character surface is a separate layer. *)
Definition step_spec (s : stmt) : Spec unit Namespace tom_nt unit :=
  Bind Get (fun ns : Namespace =>
    Guard (fun _ : unit => valid_step ns s)
      (match step ns s with
       | None => Fail
       | Some ns' => Put ns'
       end)).

Lemma step_spec_sound : forall ns s ns',
  denote tom_grammar [] (step_spec s) ns 0 tt ns' 0 -> DocumentStep ns s ns'.
Proof.
  intros ns s ns' H. unfold step_spec in H.
  pose proof (fst (denote_bind_iff unit Namespace tom_nt tom_grammar []
      Namespace unit Get (fun ns0 : Namespace => Guard (fun _ : unit => valid_step ns0 s)
        (match step ns0 s with None => Fail | Some n => Put n end))
      ns ns' 0 0 tt) H) as Hb.
  destruct Hb as [γ' [j [a [Hget Hbody]]]].
  pose proof (fst (denote_get_iff unit Namespace tom_nt tom_grammar [] ns a γ' 0 j) Hget) as Hg.
  destruct Hg as [[Hr Hg'] Hj]. subst a. subst γ'. subst j.
  pose proof (fst (denote_guard_iff unit Namespace tom_nt tom_grammar []
      unit (fun _ : unit => valid_step ns s)
      (match step ns s with None => Fail | Some n => Put n end) ns ns' 0 0 tt) Hbody) as Hgd.
  destruct Hgd as [_ Hstep].  (* discard the valid_step evidence *)
  destruct (step ns s) as [n |] eqn:E.
  - pose proof (fst (denote_put_iff unit Namespace tom_nt tom_grammar [] ns n ns' 0 0 tt) Hstep) as Hp.
    destruct Hp as [[_ Hns'] _]. subst ns'.
    apply (step_step ns s n E).
  - exfalso. exact (denote_fail_elim unit Namespace tom_nt tom_grammar [] unit ns 0 tt ns' 0 Hstep).
Qed.

Lemma step_spec_complete : forall ns s ns',
  DocumentStep ns s ns' -> denote tom_grammar [] (step_spec s) ns 0 tt ns' 0.
Proof.
  intros ns s ns' Hd. unfold step_spec.
  eapply d_bind. apply d_get.
  eapply d_guard.
  - exists ns'. exact Hd.
  - rewrite (step_step' ns s ns' Hd). apply d_put.
Qed.
