(* S4 — first synthesised plan: `compile` turns the declarative `CodeBlock`
   spec (S3) into an executable `Plan` whose refinement proof is discharged
   compositionally by induction on the `Searchable` admissibility evidence.

   The plan is a small strategy language (RP §5 subset): Return, ReadToken,
   Map, ParseValueThen (value-dependent plan), and a Repeat node for
   `linesUntil`. Its interpreter is fuel-parameterised (`run_fuel`) so it is
   total; soundness is fuel-independent (a success at any fuel is a real
   derivation), and the generated plan is provably exact (sound + complete). *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.
From Parsebot Require Import Spec Fence AnBn.

(* Type-level conjunction (Spec's × is section-scoped and not re-exported). *)
Notation "A × B" := (prod A B) (at level 40, left associativity).

(* ------------------------------------------------------------------------- *)
(* 1. The content-line boolean test, with its correctness lemma              *)
(* ------------------------------------------------------------------------- *)

Definition is_contentb (fc : FenceChar) (n : nat) (l : Line) : bool :=
  negb (is_closerb fc n l).

Lemma is_contentb_iff (fc : FenceChar) (n : nat) (l : Line) :
  is_contentb fc n l = true <-> is_content fc n l.
Proof.
  unfold is_contentb, is_content.
  rewrite Bool.negb_true_iff.
  split.
  - intros Hfalse. intro Hcl.
    apply (proj2 (is_closerb_iff fc n l)) in Hcl. rewrite Hfalse in Hcl. discriminate.
  - intros Hnotcl.
    destruct (is_closerb fc n l) eqn:E.
    + exfalso. apply Hnotcl. apply (proj1 (is_closerb_iff fc n l)). exact E.
    + reflexivity.
Qed.

(* The closer test is the boolean complement of the content test. *)
Lemma is_contentb_complement (fc : FenceChar) (n : nat) (l : Line) :
  is_closerb fc n l = true <-> is_contentb fc n l = false.
Proof.
  unfold is_contentb.
  rewrite Bool.negb_false_iff.
  reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2. Plan: a small executable strategy over Line tokens                     *)
(* ------------------------------------------------------------------------- *)

Inductive Plan : Type -> Type :=
| PRet    : forall A, A -> Plan A
| PRead   : (Line -> bool) -> Plan Line
| PMap    : forall A B, (A -> B) -> Plan A -> Plan B
| PLet    : forall A B, Plan A -> (A -> Plan B) -> Plan B
| PRepeat : forall A, (Line -> bool) -> Plan A -> Plan (list A).

Arguments PRet    {A} a.
Arguments PRead   b.
Arguments PMap    {A B} f p.
Arguments PLet    {A B} p f.
Arguments PRepeat {A} stop body.

(* Fuel-parameterised interpreter. Total by structural recursion on `fuel`.
   `PRepeat stop body` peeks the current line: if it satisfies `stop` (or the
   input is exhausted) it returns the empty list without consuming; otherwise
   it runs `body` (one line) and recurses. *)
Fixpoint run_fuel {A} (fuel : nat) (p : Plan A) (w : Lines) (i : nat)
  : option (A * nat) :=
  match fuel with
  | O => None
  | S fuel' =>
      match p with
      | PRet a => Some (a, i)
      | PRead b =>
          match nth_error w i with
          | Some l => if b l then Some (l, S i) else None
          | None => None
          end
      | PMap f p' =>
          match run_fuel fuel' p' w i with
          | Some (a, j) => Some (f a, j)
          | None => None
          end
      | PLet p' f =>
          match run_fuel fuel' p' w i with
          | Some (a, j) => run_fuel fuel' (f a) w j
          | None => None
          end
      | PRepeat stop body =>
          match nth_error w i with
          | None => Some ([], i)
          | Some l =>
              if stop l then Some ([], i)
              else match run_fuel fuel' body w i with
                   | Some (a, j) =>
                       match run_fuel fuel' (PRepeat stop body) w j with
                       | Some (as_, k) => Some (a :: as_, k)
                       | None => None
                       end
                   | None => None
                   end
          end
      end
  end.

(* More fuel never hurts. *)
Lemma run_fuel_mono : forall A (p : Plan A) w i r n m,
  run_fuel n p w i = Some r -> n <= m -> run_fuel m p w i = Some r.
Proof.
  intros A p w i r n m Hn Hnm.
  revert A p w i r m Hnm Hn.
  induction n as [| n' IH]; intros A p w i r m Hnm Hn.
  - simpl in Hn. discriminate.
  - destruct m as [| m'].
    + lia.
    + assert (Hn'm' : n' <= m') by lia.
      destruct p as [A0 a | b | A0 B0 f p' | A0 B0 p' f | A stop body];
        simpl in Hn |- *.
      * exact Hn.
      * exact Hn.
      * destruct (run_fuel n' p' w i) as [[a0 j] |] eqn:E.
        -- rewrite (IH A0 p' w i (a0, j) m' Hn'm' E). exact Hn.
        -- discriminate.
      * destruct (run_fuel n' p' w i) as [[a0 j] |] eqn:E.
        -- rewrite (IH A0 p' w i (a0, j) m' Hn'm' E).
           exact (IH B0 (f a0) w j r m' Hn'm' Hn).
        -- discriminate.
      * destruct (nth_error w i) as [l |] eqn:Enth.
        -- destruct (stop l) eqn:Estop.
           ++ exact Hn.
           ++ destruct (run_fuel n' body w i) as [[a0 j] |] eqn:Eb.
              ** destruct (run_fuel n' (PRepeat stop body) w j) as [[as0 k] |] eqn:Er.
                 --- rewrite (IH A body w i (a0, j) m' Hn'm' Eb).
                     rewrite (IH (list A) (PRepeat stop body) w j (as0, k) m' Hn'm' Er).
                     exact Hn.
                 --- discriminate.
              ** discriminate.
        -- exact Hn.
Qed.

(* Inverting a successful single read. *)

Lemma run_PRead_inv : forall b fuel w i a j,
  run_fuel fuel (PRead b) w i = Some (a, j) ->
  prod (prod (nth_error w i = Some a) (b a = true)) (j = S i).
  intros b fuel w i a j H.
  destruct fuel as [| fuel']; [cbn in H; discriminate |].
  cbn in H.
  destruct (nth_error w i) as [l |] eqn:Enth; [| discriminate].
  destruct (b l) eqn:Eb; [| discriminate].
  injection H as Ha Hj. subst.
  split; [split; [reflexivity | exact Eb] | reflexivity].
Qed.

(* Driving a single read. *)
Lemma run_PRead_ok : forall b fuel w i l,
  nth_error w i = Some l -> b l = true -> 0 < fuel ->
  run_fuel fuel (PRead b) w i = Some (l, S i).
Proof.
  intros b fuel w i l Hnth Hb Hpos.
  destruct fuel as [| fuel']; [lia |].
  cbn. rewrite Hnth, Hb. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3. Implements: result/trace refinement (soundness)                        *)
(* ------------------------------------------------------------------------- *)

Definition Implements {A} (p : Plan A) (S : Spec Line unit NT A) : Type :=
  forall fuel w i a j,
    run_fuel fuel p w i = Some (a, j) ->
    denote empty_grammar w S tt i a tt j.

(* ------------------------------------------------------------------------- *)
(* 4. Searchable: compositional admissibility, carrying the bool deciders     *)
(*    used to build the plan                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive Searchable : forall A, Spec Line unit NT A -> Type :=
| S_pure : forall A (a : A), Searchable A (Pure a)
| S_tok  : forall (P : Line -> Prop) (b : Line -> bool),
           (forall l, b l = true <-> P l) -> Searchable Line (Tok P)
| S_map  : forall A B (f : A -> B) (s : Spec Line unit NT A),
           Searchable A s -> Searchable B (Map f s)
| S_bind : forall A B (s : Spec Line unit NT A) (f : A -> Spec Line unit NT B),
           Searchable A s -> (forall a, Searchable B (f a)) ->
           Searchable B (Bind s f)
| S_many_tok : forall (P : Line -> Prop) (b stop : Line -> bool),
           (forall l, b l = true <-> P l) ->
           (forall l, stop l = true <-> b l = false) ->
           Searchable (list Line) (Many (Tok P)).

Arguments S_pure {A} a.
Arguments S_tok {P} b Hiff.
Arguments S_map {A B} f {s} Hs.
Arguments S_bind {A B} {s} {f} Hs Hf.
Arguments S_many_tok {P} b stop Hiffb Hiffstop.


(* ------------------------------------------------------------------------- *)
(* 5. compile: synthesis of the plan, transparent so Eval compute reduces it  *)
(* ------------------------------------------------------------------------- *)
Fixpoint compile_plan {A} (S : Spec Line unit NT A) (sb : Searchable A S) : Plan A.
Proof.
  destruct sb as [A0 a | P b Hiff | A0 B f s Hs | A0 B s f Hs Hf | P b stop Hiffb Hiffstop].
  - exact (PRet a).
  - exact (PRead b).
  - exact (PMap f (@compile_plan _ s Hs)).
  - exact (PLet (@compile_plan _ s Hs) (fun a => @compile_plan _ (f a) (Hf a))).
  - exact (PRepeat stop (PRead b)).
Defined.


(* Soundness of the repeat node: every success is a Many(Tok P) derivation. *)
Lemma run_repeat_sound : forall (P : Line -> Prop) (b stop : Line -> bool),
  (forall l, b l = true <-> P l) ->
  forall fuel w i as_ j,
    run_fuel fuel (PRepeat stop (PRead b)) w i = Some (as_, j) ->
    denote empty_grammar w (Many (Tok P)) tt i as_ tt j.
Proof.
  intros P b stop Hiff fuel w i as_ j Hrun.
  revert fuel w i j Hrun.
  induction as_ as [| a as' IH]; intros fuel w i j Hrun.
  - destruct fuel as [| fuel']; [cbn in Hrun; discriminate |].
    cbn in Hrun.
    destruct (nth_error w i) as [l |] eqn:Enth.
    + destruct (stop l) eqn:Estop.
      * inversion Hrun. subst. apply d_many_nil.
      * destruct (run_fuel fuel' (PRead b) w i) as [[a0 j0] |] eqn:Ebody.
        -- destruct (run_fuel fuel' (PRepeat stop (PRead b)) w j0) as [[as0 k] |] eqn:Erec.
           ++ injection Hrun as Ha Hj. subst. simpl in Ha. discriminate.
           ++ discriminate.
        -- discriminate.
    + inversion Hrun. subst. apply d_many_nil.
  - destruct fuel as [| fuel']; [cbn in Hrun; discriminate |].
    cbn in Hrun.
    destruct (nth_error w i) as [l |] eqn:Enth.
    + destruct (stop l) eqn:Estop.
      * injection Hrun as Ha Hj. subst. simpl in Ha. discriminate.
      * destruct (run_fuel fuel' (PRead b) w i) as [[a0 j0] |] eqn:Ebody.
        -- destruct (run_fuel fuel' (PRepeat stop (PRead b)) w j0) as [[as0 k] |] eqn:Erec.
           ++ injection Hrun as Ha_a Ha_as Hk. subst a0 as0 k.
              destruct (run_PRead_inv b fuel' w i a j0 Ebody) as [[Enth' Eb] Hj0]. subst j0.
              eapply d_many_cons; [ apply d_tok; [ exact Enth' | apply (proj1 (Hiff a)); exact Eb ] | apply (IH fuel' w (S i) j Erec) ].
           ++ discriminate.
        -- discriminate.
    + injection Hrun as Ha Hj. subst. simpl in Ha. discriminate.
Qed.

(* The core S4 theorem: compile_plan S sb implements S, compositionally. *)
Lemma compile_plan_implements : forall A (S : Spec Line unit NT A) (sb : Searchable A S),
  Implements (compile_plan S sb) S.
Proof.
  intros A S sb.
  induction sb as
    [ A a
    | P b Hiff
    | A B f s Hs IHmap
    | A B s f Hs IHbind Hf IHf
    | P b stop Hiffb Hiffstop ];
    simpl; red; intros fuel w i a' j Hrun.
  - (* S_pure *)
    destruct fuel as [| fuel']; [cbn in Hrun; discriminate |].
    cbn in Hrun. injection Hrun as Ha Hj. subst. apply d_pure.
  - (* S_tok *)
    destruct fuel as [| fuel']; [cbn in Hrun; discriminate |].
    cbn in Hrun.
    destruct (nth_error w i) as [l |] eqn:Enth; [| discriminate].
    destruct (b l) eqn:Eb; [| discriminate].
    injection Hrun as Ha Hj. subst.
    apply d_tok; [ exact Enth | apply (proj1 (Hiff a')); exact Eb ].
  - (* S_map *)
    destruct fuel as [| fuel']; [cbn in Hrun; discriminate |].
    cbn in Hrun.
    destruct (run_fuel fuel' (compile_plan s Hs) w i) as [[a0 j0] |] eqn:E; [| discriminate].
    injection Hrun as Hb Hj. subst.
    apply d_map. apply (IHmap fuel' w i a0 j E).
  - (* S_bind *)
    destruct fuel as [| fuel']; [cbn in Hrun; discriminate |].
    cbn in Hrun.
    destruct (run_fuel fuel' (compile_plan s Hs) w i) as [[a0 j0] |] eqn:E; [| discriminate].
    eapply d_bind.
    + apply (IHbind fuel' w i a0 j0 E).
    + apply (IHf a0 fuel' w j0 a' j Hrun).
  - (* S_many_tok *)
    apply (run_repeat_sound P b stop Hiffb fuel w i a' j Hrun).
Qed.

Arguments compile_plan_implements {A} S sb.

(* ------------------------------------------------------------------------- *)
(* 6. compile as a Dec (inhabited because Searchable gives a witness)         *)
(* ------------------------------------------------------------------------- *)

Definition compile {A} (S : Spec Line unit NT A) (sb : Searchable A S)
  : Dec { p : Plan A & Implements p S } :=
  yes (existT _ (compile_plan S sb) (compile_plan_implements S sb)).

(* ------------------------------------------------------------------------- *)
(* 7. The Searchable witness for CodeBlock, and the generated plan            *)
(* ------------------------------------------------------------------------- *)

(* The body of CodeBlock's continuation, with `let`-destructuring replaced by
   `fst`/`snd` so the dependent `Searchable` witness unifies. *)
Definition CodeBlockBody (fc : FenceChar) (n : nat)
  : Spec Line unit NT (FenceChar * nat * list Line) :=
  Bind (Many (ContentLine fc n))
    (fun content => Bind (FenceClose fc n) (fun _ => Pure (fc, n, content))).

Definition searchable_CodeBlock : Searchable (FenceChar * nat * list Line) CodeBlock :=
  @S_bind (FenceChar * nat) (FenceChar * nat * list Line)
    FenceOpen
    (fun fc_n => CodeBlockBody (fst fc_n) (snd fc_n))
    (@S_bind Line (FenceChar * nat)
       (Tok (fun l : Line => is_open l)) (fun l => Pure (open_info l))
       (S_tok is_openb is_openb_iff)
       (fun l => S_pure (open_info l)))
    (fun fc_n =>
       @S_bind (list Line) (FenceChar * nat * list Line)
         (Many (ContentLine (fst fc_n) (snd fc_n)))
         (fun content =>
           Bind (FenceClose (fst fc_n) (snd fc_n)) (fun _ => Pure (fst fc_n, snd fc_n, content)))
         (S_many_tok (is_contentb (fst fc_n) (snd fc_n)) (is_closerb (fst fc_n) (snd fc_n))
            (is_contentb_iff (fst fc_n) (snd fc_n))
            (is_contentb_complement (fst fc_n) (snd fc_n)))
         (fun content =>
           @S_bind unit (FenceChar * nat * list Line)
             (FenceClose (fst fc_n) (snd fc_n))
             (fun _ => Pure (fst fc_n, snd fc_n, content))
             (S_map (fun _ : Line => tt)
                (S_tok (is_closerb (fst fc_n) (snd fc_n)) (is_closerb_iff (fst fc_n) (snd fc_n))))
             (fun _ => S_pure (fst fc_n, snd fc_n, content)))).

Definition codeblock_plan : Plan (FenceChar * nat * list Line) :=
  compile_plan CodeBlock searchable_CodeBlock.
(* The plan `compile` synthesises, written out — exactly the S3 hand-written
   scanner, re-derived by proof search. The Repeat stop predicate is the closer
   test; the content read is the content test. *)
Definition codeblock_plan_explicit : Plan (FenceChar * nat * list Line) :=
  PLet (PLet (PRead is_openb) (fun l => PRet (open_info l)))
    (fun fc_n =>
      PLet (PRepeat (is_closerb (fst fc_n) (snd fc_n)) (PRead (is_contentb (fst fc_n) (snd fc_n))))
        (fun content => PLet (PMap (fun _ : Line => tt) (PRead (is_closerb (fst fc_n) (snd fc_n))))
          (fun _ => PRet (fst fc_n, snd fc_n, content)))).

Lemma codeblock_plan_reduces : codeblock_plan = codeblock_plan_explicit.
Proof. reflexivity. Qed.


(* The synthesized scanner's soundness: kernel-checked. *)
Definition codeblock_plan_implements : Implements codeblock_plan CodeBlock :=
  compile_plan_implements CodeBlock searchable_CodeBlock.

(* A public run, total, with a fuel bound comfortably above the plan's depth
   (opener 2 + content ≤ length w + closer 3). *)
Definition plan_fuel (w : Lines) : nat := S (S (S (length w))).

Definition run {A} (p : Plan A) (w : Lines) (i : nat) : option (A * nat) :=
  run_fuel (plan_fuel w) p w i.

(* Keep `simpl`/`cbn` from unfolding the content test; `Eval compute` still
   reduces it. *)
Opaque is_contentb.

(* ------------------------------------------------------------------------- *)
(* 8. Completeness: the generated plan finds every derivation                 *)
(* ------------------------------------------------------------------------- *)

(* The repeat node, driven from a Many + closer derivation, consumes exactly
   the content. *)
Lemma run_repeat_from_denote : forall fc n w i content closer,
  denote empty_grammar w (Many (ContentLine fc n)) tt i content tt (i + length content) ->
  denote empty_grammar w (Tok (fun l => is_closer fc n l)) tt (i + length content) closer tt (S (i + length content)) ->
  run_fuel (S (length content)) (PRepeat (is_closerb fc n) (PRead (is_contentb fc n))) w i
    = Some (content, i + length content).
Proof.
  intros fc n w i content closer.
  revert w i closer.
  induction content as [| a content' IH]; intros w i closer dmany dtok.
  - rewrite Nat.add_0_r in dtok.
    destruct (denote_tok_facts w (fun l => is_closer fc n l) closer tt tt i (S i) dtok) as [[Hnth Hcl] _].
    apply (proj2 (is_closerb_iff fc n closer)) in Hcl.
    cbn [run_fuel]. rewrite Hnth, Hcl. rewrite Nat.add_0_r. reflexivity.
  - pose proof (fst (denote_many_iff Line unit NT empty_grammar w Line (ContentLine fc n) tt tt i (i + length (a :: content')) (a :: content')) dmany) as Hmany.
    destruct Hmany as [Hnil | [a0 [as' [γ'' [k [[Has Hline] Hrest]]]]]].
    + destruct Hnil as [[Hnil1 _] _]. inversion Hnil1.
    + inversion Has; subst a0 as'.
      simpl in Hline.
      destruct (denote_tok_facts w (fun l => is_content fc n l) a tt γ'' i k Hline) as [[Hnth Hcontent] [Hk Hge]].
      subst k γ''.
      replace (i + length (a :: content')) with (S i + length content') in Hrest, dtok by (simpl; lia).
      replace (S (i + length (a :: content'))) with (S (S i + length content')) in dtok by (simpl; lia).
      assert (Hcb : is_closerb fc n a = false) by
        (destruct (is_closerb fc n a) eqn:E;
         [exfalso; apply Hcontent; apply (proj1 (is_closerb_iff fc n a)); exact E | reflexivity]).
      apply (proj2 (is_contentb_iff fc n a)) in Hcontent.
      simpl. rewrite Hnth, Hcb, Hcontent.
      change ((match run_fuel (S (length content')) (PRepeat (is_closerb fc n) (PRead (is_contentb fc n))) w (S i) with
               | Some (as_, k) => Some (a :: as_, k)
               | None => None end)
              = Some (a :: content', i + S (length content'))).
      rewrite (IH w (S i) closer Hrest dtok).
      cbn. replace (i + S (length content')) with (S i + length content') by lia. reflexivity.
Qed.
(* Whole-input completeness: a CodeBlock derivation is found by the plan. *)
Lemma plan_codeblock_complete : forall w block,
  denote empty_grammar w CodeBlock tt 0 block tt (length w) ->
  run codeblock_plan w 0 = Some (block, length w).
Proof.
  intros w block d.
  destruct (denote_codeblock_inv w block d) as [l ls' fc n content closer Hshape Hop Hblk Hlen Hinfo Hmany Htok].
  subst w block.
  rewrite codeblock_plan_reduces.
  unfold run, plan_fuel.
  simpl.
  rewrite (proj2 (is_openb_iff l) Hop).
  simpl.
  rewrite <- Hinfo.
  change ((match run_fuel (S (S (length ls'))) (PRepeat (is_closerb fc n) (PRead (is_contentb fc n))) (l :: ls') 1 with
           | Some (content0, j0) => run_fuel (S (S (length ls'))) (PLet (PMap (fun _ : Line => tt) (PRead (is_closerb fc n))) (fun _ : unit => PRet (fc, n, content0))) (l :: ls') j0
           | None => None end)
          = Some ((fc, n, content), length (l :: ls'))).
  assert (Hrep : run_fuel (S (S (length ls'))) (PRepeat (is_closerb fc n) (PRead (is_contentb fc n))) (l :: ls') 1 = Some (content, 1 + length content)). {
    apply (run_fuel_mono _ _ _ _ _ (S (length content)) (S (S (length ls')))).
    - apply (run_repeat_from_denote fc n (l :: ls') 1 content closer).
      + exact Hmany.
      + exact Htok.
    - simpl in Hlen. lia.
  }
  rewrite Hrep.
  change ((match match run_fuel (length ls') (PRead (is_closerb fc n)) (l :: ls') (1 + length content) with
                 | Some (a, j) => Some (tt, j)
                 | None => None end with
           | Some (u, j) => run_fuel (S (length ls')) (PRet (fc, n, content)) (l :: ls') j
           | None => None end)
          = Some ((fc, n, content), length (l :: ls'))).
  rewrite (run_PRead_ok (is_closerb fc n) (length ls') (l :: ls') (1 + length content) closer).
  2: { destruct (denote_tok_facts (l :: ls') (fun x => is_closer fc n x) closer tt tt (1 + length content) (S (1 + length content)) Htok) as [[Hnth _] _]. exact Hnth. }
  2: { destruct (denote_tok_facts (l :: ls') (fun x => is_closer fc n x) closer tt tt (1 + length content) (S (1 + length content)) Htok) as [[_ Hcl] _]. apply (proj2 (is_closerb_iff fc n closer)). exact Hcl. }
  2: { simpl in Hlen. lia. }
  simpl. simpl in Hlen. congruence.
Qed.

(* Rejection completeness: if the plan rejects, no derivation exists. *)
Definition plan_rejection_complete : forall w,
  run codeblock_plan w 0 = None ->
  forall block, denote empty_grammar w CodeBlock tt 0 block tt (length w) -> False.
Proof.
  intros w Hnone block d.
  apply plan_codeblock_complete in d.
  rewrite d in Hnone. discriminate.
Defined.

(* The generated plan is exactly the S3 hand-written scanner. *)
Lemma plan_scan_equiv : forall w block,
  run codeblock_plan w 0 = Some (block, length w) <-> scan_codeblock w = Some (block, []).
Proof.
  intros w block. split.
  - intros Hrun.
    pose proof (codeblock_plan_implements (plan_fuel w) w 0 block (length w) Hrun) as Hden.
    apply scan_codeblock_complete. exact Hden.
  - intros Hscan.
    apply plan_codeblock_complete.
    apply scan_codeblock_sound. exact Hscan.
Qed.

(* ------------------------------------------------------------------------- *)
(* 8. Acceptance: the generated scanner accepts the S3 example                *)
(* ------------------------------------------------------------------------- *)

Transparent is_contentb.
Eval compute in (run codeblock_plan example_block 0).
