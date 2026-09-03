(* S3 — CommonMark fenced code block fragment (RP §6.2, §12).
   The first discriminating experiment: a scanner whose closing test depends on
   the captured fence character and length, proved sound and complete against a
   declarative `Spec`/`denote` encoding. *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
Import ListNotations.
From Parsebot Require Import Spec.

(* Type-level conjunction (Spec's × is section-scoped and not re-exported). *)
Notation "A × B" := (prod A B) (at level 40, left associativity).

(* ------------------------------------------------------------------------- *)
(* 1. Line-oriented input model                                               *)
(* ------------------------------------------------------------------------- *)

Inductive Char := Backtick | Tilde | Other.
Scheme Equality for Char.

Definition Line := list Char.
Definition Lines := list Line.

(* The two fence-character kinds. *)
Inductive FenceChar := FBacktick | FTilde.

Definition fchar_to_char (fc : FenceChar) : Char :=
  match fc with FBacktick => Backtick | FTilde => Tilde end.

(* Length of the leading run of character c in line l. *)
Fixpoint leading_run (c : Char) (l : Line) : nat :=
  match l with
  | [] => 0
  | x :: l' => if Char_eq_dec x c then S (leading_run c l') else 0
  end.

(* ------------------------------------------------------------------------- *)
(* 2. Fence relations                                                         *)
(* ------------------------------------------------------------------------- *)

(* A line is a fence opener iff it starts with >= 3 backticks or >= 3 tildes. *)
Definition is_open (l : Line) : Prop :=
  leading_run Backtick l >= 3 \/ leading_run Tilde l >= 3.

Definition is_openb (l : Line) : bool :=
  (3 <=? leading_run Backtick l) || (3 <=? leading_run Tilde l).

Lemma is_openb_iff (l : Line) : is_openb l = true <-> is_open l.
Proof.
  unfold is_openb, is_open.
  rewrite Bool.orb_true_iff.
  rewrite !Nat.leb_le.
  reflexivity.
Qed.

(* A line closes a fence (fc, n) iff it starts with >= n copies of fc's char. *)
Definition is_closer (fc : FenceChar) (n : nat) (l : Line) : Prop :=
  leading_run (fchar_to_char fc) l >= n.

Definition is_closerb (fc : FenceChar) (n : nat) (l : Line) : bool :=
  n <=? leading_run (fchar_to_char fc) l.

Lemma is_closerb_iff (fc : FenceChar) (n : nat) (l : Line) :
  is_closerb fc n l = true <-> is_closer fc n l.
Proof.
  unfold is_closerb, is_closer.
  apply Nat.leb_le.
Qed.

Definition is_content (fc : FenceChar) (n : nat) (l : Line) : Prop :=
  ~ is_closer fc n l.

(* Compute (fc, n) from an opener line (defaults when the line is not an opener). *)
Definition open_info (l : Line) : FenceChar * nat :=
  match l with
  | Backtick :: _ => (FBacktick, leading_run Backtick l)
  | Tilde :: _    => (FTilde, leading_run Tilde l)
  | _             => (FBacktick, 0)
  end.

(* ------------------------------------------------------------------------- *)
(* 3. Hand-written scanner                                                    *)
(* ------------------------------------------------------------------------- *)

(* Scan content lines until a closer for (fc, n). Returns (content, rest) where
   rest is empty on failure to find a closer, or begins with the closer line. *)
Fixpoint scan_content (fc : FenceChar) (n : nat) (ls : Lines)
  : option (list Line * Lines) :=
  match ls with
  | [] => None
  | l :: ls' =>
      if is_closerb fc n l
      then Some ([], ls)
      else match scan_content fc n ls' with
           | None => None
           | Some (content, rest) => Some (l :: content, rest)
           end
  end.

(* Scan a whole fenced code block: opener, content lines, closer. *)
Definition scan_codeblock (ls : Lines)
  : option ((FenceChar * nat * list Line) * Lines) :=
  match ls with
  | [] => None
  | l :: ls' =>
      if is_openb l then
        let (fc, n) := open_info l in
        match scan_content fc n ls' with
        | Some (content, closer :: rest) => Some ((fc, n, content), rest)
        | _ => None
        end
      else None
  end.

(* ------------------------------------------------------------------------- *)
(* 4. CodeBlock as a Spec, and its denotation                                 *)
(* ------------------------------------------------------------------------- *)

Definition NT := fun (_ : Type) => Empty_set.

Definition empty_grammar : Grammar Line unit NT :=
  fun A n => match n with end.

Definition FenceOpen : Spec Line unit NT (FenceChar * nat) :=
  Bind (Tok (fun l => is_open l)) (fun l => Pure (open_info l)).

Definition FenceClose (fc : FenceChar) (n : nat) : Spec Line unit NT unit :=
  Map (fun _ => tt) (Tok (fun l => is_closer fc n l)).

Definition ContentLine (fc : FenceChar) (n : nat) : Spec Line unit NT Line :=
  Tok (fun l => is_content fc n l).

Definition CodeBlock : Spec Line unit NT (FenceChar * nat * list Line) :=
  Bind FenceOpen (fun fc_n =>
    Bind (Many (ContentLine (fst fc_n) (snd fc_n))) (fun content =>
      Bind (FenceClose (fst fc_n) (snd fc_n)) (fun _ => Pure (fst fc_n, snd fc_n, content)))).

(* ------------------------------------------------------------------------- *)
(* 5. Soundness and completeness                                             *)
(* ------------------------------------------------------------------------- *)

(* scan_content consumes exactly its content prefix. *)
Lemma scan_content_app : forall fc n ls content rest,
  scan_content fc n ls = Some (content, rest) -> ls = content ++ rest.
Proof.
  induction ls as [| l ls' IH]; intros content rest Hscan; simpl in Hscan.
  - discriminate.
  - destruct (is_closerb fc n l) eqn:E.
    + injection Hscan as Hc Hr. rewrite <- Hc. rewrite <- Hr. reflexivity.
    + destruct (scan_content fc n ls') as [[c' r'] |]; [| discriminate].
      injection Hscan as Hc Hr. rewrite <- Hc. rewrite <- Hr.
      simpl. f_equal. exact (IH c' r' eq_refl).
Qed.

(* scan_content's remainder starts with a closer. *)
Lemma scan_content_rest : forall fc n ls content rest,
  scan_content fc n ls = Some (content, rest) ->
  exists closer rest', rest = closer :: rest' /\ is_closerb fc n closer = true.
Proof.
  induction ls as [| l ls' IH]; intros content rest Hscan; simpl in Hscan.
  - discriminate.
  - destruct (is_closerb fc n l) eqn:E.
    + injection Hscan as Hc Hr. rewrite <- Hr.
      eexists; eexists; split; [reflexivity | exact E].
    + destruct (scan_content fc n ls') as [[c' r'] |]; [| discriminate].
      injection Hscan as Hc Hr. rewrite <- Hr.
      destruct (IH c' r' eq_refl) as [closer [rest' [Hr' Hcl]]].
      eexists; eexists; split; [exact Hr' | exact Hcl].
Qed.

(* nth_error at a prefix boundary, avoiding nth_error_app2's subtraction. *)
Lemma nth_error_app_cons (x : Line) (prefix l : Lines) :
  nth_error (prefix ++ x :: l) (length prefix) = Some x.
Proof.
  induction prefix as [| p ps IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(* Soundness of content scanning, prefix-threaded to avoid a shift lemma. *)
Lemma scan_content_sound : forall ls prefix fc n content rest,
  scan_content fc n ls = Some (content, rest) ->
  denote empty_grammar (prefix ++ ls) (Many (ContentLine fc n))
    tt (length prefix) content tt (length prefix + length content).
Proof.
  induction ls as [| l ls' IH]; intros prefix fc n content rest Hscan; simpl in Hscan.
  - discriminate.
  - destruct (is_closerb fc n l) eqn:E.
    + injection Hscan as Hc Hr. rewrite <- Hc. simpl. rewrite Nat.add_0_r. constructor.
    + case_eq (scan_content fc n ls').
      * intros pr Hsc. destruct pr as [c' r'].
        rewrite Hsc in Hscan. injection Hscan as Hc Hr. rewrite <- Hc.
        eapply d_many_cons;
        [ unfold ContentLine; eapply d_tok;
          [ exact (nth_error_app_cons l prefix ls')
          | intro Hcl; apply (proj2 (is_closerb_iff fc n l)) in Hcl; rewrite E in Hcl; congruence ]
        | replace (length prefix + length (l :: c')) with (length (prefix ++ [l]) + length c')
            by (rewrite length_app; simpl; lia);
          replace (S (length prefix)) with (length (prefix ++ [l]))
            by (rewrite length_app; simpl; lia);
          replace (prefix ++ l :: ls') with ((prefix ++ [l]) ++ ls')
            by (rewrite <- app_assoc; simpl; reflexivity);
          apply (IH (prefix ++ [l]) fc n c' r' Hsc) ].
      * intros Hnone. rewrite Hnone in Hscan. simpl in Hscan. discriminate Hscan.
Qed.

(* Soundness: the scanner is correct whenever it accepts. *)
Lemma scan_codeblock_sound : forall ls block,
  scan_codeblock ls = Some (block, []) ->
  denote empty_grammar ls CodeBlock tt 0 block tt (length ls).
Proof.
  intros ls block Hscan.
  unfold scan_codeblock in Hscan.
  destruct ls as [| l ls']; [discriminate |].
  destruct (is_openb l) eqn:Eopen; [| discriminate].
  destruct (open_info l) as [fc n] eqn:Einfo.
  destruct (scan_content fc n ls') as [[content rest] |] eqn:Escan; [| discriminate].
  destruct rest as [| closer rest']; [discriminate |].
  inversion Hscan; subst.
  pose proof (scan_content_app fc n ls' content (closer :: []) Escan) as Hsapp.
  subst ls'.
  replace (length (l :: content ++ [closer])) with (S (length [l] + length content))
    by (simpl; rewrite length_app; simpl; lia).
  unfold CodeBlock, FenceOpen, FenceClose, ContentLine.
  eapply d_bind;
  [ eapply d_bind;
    [ eapply d_tok;
      [ simpl; reflexivity
      | apply (proj1 (is_openb_iff l)); exact Eopen ]
    | rewrite Einfo; eapply d_pure ]
  | eapply d_bind;
    [ apply (scan_content_sound (content ++ closer :: []) [l] fc n content (closer :: []) Escan)
    | eapply d_bind;
      [ eapply d_map; eapply d_tok;
        [ simpl; exact (nth_error_app_cons closer content [])
        | destruct (scan_content_rest fc n (content ++ closer :: []) content (closer :: []) Escan)
            as [cl [rt [Hr Hcl]]];
          inversion Hr; subst; apply (proj1 (is_closerb_iff fc n cl)); exact Hcl ]
      | eapply d_pure ] ] ].
Qed.

(* Completeness of content scanning: any denote-derivation is found by the
   scanner, provided the following line closes the fence. *)
Lemma nth_error_length_none (l : Lines) : nth_error l (length l) = None.
Proof. induction l; simpl; auto. Qed.

Lemma nth_error_app_cons_inv (prefix ls : Lines) (x : Line) :
  nth_error (prefix ++ ls) (length prefix) = Some x -> {ls' : Lines & ls = x :: ls'}.
Proof.
  intros H. destruct ls as [| y ls'].
  - rewrite app_nil_r in H. rewrite nth_error_length_none in H. discriminate.
  - exists ls'. rewrite (nth_error_app_cons y prefix ls') in H. injection H as Hyx. subst y. reflexivity.
Qed.

Lemma denote_tok_facts (w : Lines) (P : Line -> Type) (t : Line) (γ γ' : unit) (i j : nat) :
  denote empty_grammar w (Tok P) γ i t γ' j ->
  prod (prod (nth_error w i = Some t) (P t)) (prod (j = S i) (γ' = γ)).
Proof.
  intros Htok.
  pose proof (fst (denote_tok_iff Line unit NT empty_grammar w P t γ γ' i j) Htok) as H'.
  destruct H' as [[[He Hj] Hnth] Hp].
  split; [split; [exact Hnth | exact Hp] | split; [exact Hj | exact He]].
Qed.

Lemma scan_content_complete : forall ls prefix fc n content closer,
  denote empty_grammar (prefix ++ ls) (Many (ContentLine fc n))
    tt (length prefix) content tt (length prefix + length content) ->
  denote empty_grammar (prefix ++ ls) (Tok (fun l => is_closer fc n l))
    tt (length prefix + length content) closer tt (S (length prefix + length content)) ->
  exists rest, scan_content fc n ls = Some (content, rest).
Proof.
  intros ls prefix fc n content closer.
  revert ls prefix closer.
  induction content as [| a content' IH]; intros ls prefix closer dmany dtok.
  - simpl in dtok. rewrite Nat.add_0_r in dtok.
    destruct (denote_tok_facts (prefix ++ ls) (fun l => is_closer fc n l) closer tt tt (length prefix) (S (length prefix)) dtok) as [[Hnth Hcl] Hj].
    destruct (nth_error_app_cons_inv prefix ls closer Hnth) as [ls' Hls'].
    subst ls.
    exists (closer :: ls'). simpl.
    apply (proj2 (is_closerb_iff fc n closer)) in Hcl. rewrite Hcl. reflexivity.
  - pose proof (fst (denote_many_iff Line unit NT empty_grammar (prefix ++ ls) Line (ContentLine fc n) tt tt (length prefix) (length prefix + length (a :: content')) (a :: content')) dmany) as Hmany.
    destruct Hmany as [Hnil | [a0 [as' [γ'' [k [[Has Hline] Hrest]]]]]].
    + destruct Hnil as [[Hnil1 _] _]. inversion Hnil1.
    + inversion Has; subst a0 as'.
      simpl in Hline.
      destruct (denote_tok_facts (prefix ++ ls) (fun l => is_content fc n l) a tt γ'' (length prefix) k Hline) as [[Hnth Hcontent] [Hj He]].
      subst k γ''.
      destruct (nth_error_app_cons_inv prefix ls a Hnth) as [ls' Hls'].
      subst ls.
      replace (length prefix + length (a :: content')) with (length (prefix ++ [a]) + length content')
        in Hrest by (rewrite length_app; simpl; lia).
      replace (length prefix + length (a :: content')) with (length (prefix ++ [a]) + length content')
        in dtok by (rewrite length_app; simpl; lia).
      replace (S (length prefix + length (a :: content'))) with (S (length (prefix ++ [a]) + length content'))
        in dtok by (rewrite length_app; simpl; lia).
      replace (prefix ++ a :: ls') with ((prefix ++ [a]) ++ ls') in Hrest, dtok by (rewrite <- app_assoc; simpl; reflexivity).
      replace (S (length prefix)) with (length (prefix ++ [a])) in Hrest by (rewrite length_app; simpl; lia).
      destruct (IH ls' (prefix ++ [a]) closer Hrest dtok) as [rest Hscan].
      exists rest.
      assert (Hb : is_closerb fc n a = false) by
        (destruct (is_closerb fc n a) eqn:E;
         [exfalso; apply Hcontent; apply (proj1 (is_closerb_iff fc n a)); exact E | reflexivity]).
      simpl. rewrite Hb. simpl. rewrite Hscan. reflexivity.
Qed.

(* The Many denotation consumes exactly length-content lines and preserves γ. *)
Lemma denote_many_content_facts : forall (w : Lines) (fc : FenceChar) (n : nat) (i : nat) (content : list Line) (γ γ' : unit) (j : nat),
  denote empty_grammar w (Many (ContentLine fc n)) γ i content γ' j ->
  prod (γ' = γ) (j = i + length content).
Proof.
  intros w fc n i content γ γ' j d.
  revert w fc n i γ γ' j d.
  induction content as [| a content' IH]; intros w fc n i γ γ' j d.
  - apply (fst (denote_many_iff Line unit NT empty_grammar w Line (ContentLine fc n) γ γ' i j [])) in d.
    destruct d as [Hnil | [a0 [as' [γ'' [k [[Has _] _]]]]]].
    + destruct Hnil as [[Hnil1 He] Hj]. split; [exact He | simpl; rewrite Nat.add_0_r; exact Hj].
    + inversion Has.
  - apply (fst (denote_many_iff Line unit NT empty_grammar w Line (ContentLine fc n) γ γ' i j (a :: content'))) in d.
    destruct d as [Hnil | Hcons].
    + destruct Hnil as [[Hnil1 _] _]. inversion Hnil1.
    + destruct Hcons as [a0 [as' [γ'' [k Hbody]]]].
      destruct Hbody as [[Has d1] d2].
      inversion Has; subst a0 as'.
      destruct (denote_tok_facts w (fun l => is_content fc n l) a γ γ'' i k d1) as [[Hnth Hcontent] [Hk Hge]].
      destruct (IH w fc n k γ'' γ' j d2) as [Hge' Hj'].
      split.
      * rewrite <- Hge. exact Hge'.
      * rewrite Hj'. rewrite Hk. simpl. lia.
Qed.
Record codeblock_facts (ls : Lines) (block : FenceChar * nat * list Line) : Type :=
  { cf_l : Line;
    cf_ls : Lines;
    cf_fc : FenceChar;
    cf_n : nat;
    cf_content : list Line;
    cf_closer : Line;
    cf_shape : ls = cf_l :: cf_ls;
    cf_open : is_open cf_l;
    cf_block : block = (cf_fc, cf_n, cf_content);
    cf_len : length ls = S (1 + length cf_content);
    cf_info : (cf_fc, cf_n) = open_info cf_l;
    cf_many : denote empty_grammar (cf_l :: cf_ls) (Many (ContentLine cf_fc cf_n)) tt 1 cf_content tt (1 + length cf_content);
    cf_tok : denote empty_grammar (cf_l :: cf_ls) (Tok (fun x => is_closer cf_fc cf_n x)) tt (1 + length cf_content) cf_closer tt (S (1 + length cf_content))
  }.

Lemma denote_codeblock_inv : forall ls block,
  denote empty_grammar ls CodeBlock tt 0 block tt (length ls) ->
  codeblock_facts ls block.
Proof.
  intros ls block d.
  unfold CodeBlock, FenceOpen, FenceClose, ContentLine in d.
  destruct (fst (denote_bind_iff Line unit NT empty_grammar ls (FenceChar * nat) (FenceChar * nat * list Line)
    (Bind (Tok (fun l0 => is_open l0)) (fun l0 => Pure (open_info l0)))
    (fun fc_n => Bind (Many (ContentLine (fst fc_n) (snd fc_n))) (fun content => Bind (FenceClose (fst fc_n) (snd fc_n)) (fun _ => Pure (fst fc_n, snd fc_n, content))))
    tt tt 0 (length ls) block) d) as [γ1 [j1 [a1 [dopen dblock]]]].
  destruct (fst (denote_bind_iff Line unit NT empty_grammar ls Line (FenceChar * nat)
    (Tok (fun l0 => is_open l0)) (fun l0 => Pure (open_info l0)) tt γ1 0 j1 a1) dopen) as [γ2 [j2 [l [dtok_open dpure_open]]]].
  destruct (fst (denote_tok_iff Line unit NT empty_grammar ls (fun l0 => is_open l0) l tt γ2 0 j2) dtok_open) as [[[Hge Hj] Hnth_open] Hop].
  destruct (fst (denote_pure_iff Line unit NT empty_grammar ls (FenceChar * nat) (open_info l) γ2 j2 a1 γ1 j1) dpure_open) as [[Hinfo Hge'] Hj'].
  destruct a1 as [fc n]. simpl in dblock.
  destruct (fst (denote_bind_iff Line unit NT empty_grammar ls (list Line) (FenceChar * nat * list Line)
    (Many (ContentLine fc n)) (fun content => Bind (FenceClose fc n) (fun _ => Pure (fc, n, content)))
    γ1 tt j1 (length ls) block) dblock) as [γ3 [j3 [content [dmany dclose]]]].
  destruct (fst (denote_bind_iff Line unit NT empty_grammar ls unit (FenceChar * nat * list Line)
    (FenceClose fc n) (fun _ => Pure (fc, n, content)) γ3 tt j3 (length ls) block) dclose) as [γ4 [j4 [u [dmap dpure_block]]]].
  destruct (fst (denote_map_iff Line unit NT empty_grammar ls Line unit (fun _ : Line => tt) (Tok (fun x => is_closer fc n x)) γ3 γ4 j3 j4 u) dmap) as [closer [Htt dtok_close]].
  destruct (fst (denote_pure_iff Line unit NT empty_grammar ls (FenceChar * nat * list Line) (fc, n, content) γ4 j4 block tt (length ls)) dpure_block) as [[Hblk Hge''] Hlen].
  destruct (nth_error_app_cons_inv [] ls l Hnth_open) as [ls' Hls'].
  rewrite Hls' in dmany, dtok_close.
  subst γ1 γ2 j1 j2.
  destruct (denote_many_content_facts (l :: ls') fc n 1 content tt γ3 j3 dmany) as [Hge3 Hj3].
  destruct (denote_tok_facts (l :: ls') (fun x => is_closer fc n x) closer γ3 γ4 j3 j4 dtok_close) as [[Hnth_close Hcl] [Hj4 Hge4]].
  subst γ3 γ4 j3.
  rewrite Hj4 in dtok_close, Hlen.
  exact (Build_codeblock_facts ls block l ls' fc n content closer Hls' Hop Hblk Hlen Hinfo dmany dtok_close).
Qed.

(* Completeness: the scanner accepts whenever a derivation exists. *)
Lemma scan_codeblock_complete : forall ls block,
  denote empty_grammar ls CodeBlock tt 0 block tt (length ls) ->
  scan_codeblock ls = Some (block, []).
Proof.
  intros ls block d.
  destruct (denote_codeblock_inv ls block d) as [l ls' fc n content closer Hls Hop Hblk Hoi Hinfo Hmany Htok].
  subst ls.
  destruct (scan_content_complete ls' [l] fc n content closer) as [rest Hs].
  - simpl in Hmany. exact Hmany.
  - simpl in Htok. exact Htok.
  - unfold scan_codeblock.
    rewrite (proj2 (is_openb_iff l) Hop).
    simpl. rewrite <- Hinfo. simpl.
    rewrite Hblk.
    rewrite Hs.
    assert (Happ : ls' = content ++ rest) by (exact (scan_content_app fc n ls' content rest Hs)).
    destruct (scan_content_rest fc n ls' content rest) as [cl [rt [Hr Hcl]]]; [exact Hs |].
    assert (Hlenrest : length rest = 1). {
      assert (Hlslen : length ls' = 1 + length content). {
        simpl in Hoi. injection Hoi as Hoi'. exact Hoi'.
      }
      rewrite Happ in Hlslen. rewrite length_app in Hlslen. lia.
    }
    rewrite Hr in Hlenrest. simpl in Hlenrest.
    destruct rt as [| r rt']; [| simpl in Hlenrest; lia].
    (* cl = closer *)
    assert (Hnth_cl : nth_error (l :: ls') (1 + length content) = Some cl). {
      rewrite Happ. rewrite Hr. simpl. exact (nth_error_app_cons cl content []).
    }
    destruct (denote_tok_facts (l :: ls') (fun x => is_closer fc n x) closer tt tt (1 + length content) (S (1 + length content)) Htok) as [[Hnth_close Hclclose] _].
    rewrite Hnth_cl in Hnth_close. injection Hnth_close as Hcl'. subst cl.
    rewrite Hr. simpl. reflexivity.
Qed.

(* Example: a concrete fenced code block. *)
Definition fence_open_line := [Backtick; Backtick; Backtick].
Definition content_line := [Other].
Definition fence_close_line := [Backtick; Backtick; Backtick; Backtick].

Definition example_block : Lines := [fence_open_line; content_line; fence_close_line].

Eval compute in (scan_codeblock example_block).
