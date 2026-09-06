(* S7 — Haskell layout (Haskell 2010 §2.7, §10.3).

   Layout inserts virtual braces and semicolons by indentation.  This slice is
   the *core stack algorithm* for nested `let`/`where` blocks plus explicit
   braces; the report's parse-error-dependent insertion rule is deferred
   (RP §6.4 scope), so declarations are single `TName` atoms whose column
   determines the `;` insertion.

   Layout is certified: the declarative relation `Layout` (an inductive
   rendering of the rules) agrees exactly with the algorithm `layout_run`. *)

From Stdlib Require Import List Bool Nat.
Import ListNotations.

(* Lexemes of a tiny fragment: let / where / in, declaration names, `=` and
   literals (for explicit-brace blocks), and the explicit punctuation. *)
Inductive tok : Type :=
| TLet | TWhere | TIn
| TName | TEq | TLit
| TLBrace | TRBrace | TSemi.

(* A raw lexeme is annotated with its column (indentation). *)
Definition RawTokens : Type := list (nat * tok).
Definition ExplicitTokens : Type := list tok.

(* Layout contexts on the stack. *)
Inductive ctx : Type :=
| CExplicit          (* `{` : indentation is never set *)
| CPending           (* `let`/`where` : set by the next lexeme *)
| CBlock (col : nat) (* implicit block at indentation col *).

Definition CtxStack : Type := list ctx.

(* A lexeme opens a new declaration only in the "first token" position.  The
   simplified stand-in for the report's parse-error(t) check. *)
Definition is_decl_starter (t : tok) : bool :=
  match t with
  | TName => true
  | TLet | TWhere | TIn | TEq | TLit | TLBrace | TRBrace | TSemi => false
  end.

(* Close every open context at end of input. *)
Definition close (st : CtxStack) : list tok :=
  List.repeat TRBrace (List.length st).

(* `{` pushes a context (overriding a pending one); `}` pops one. *)
Definition push_lbrace (st : CtxStack) : CtxStack :=
  match st with
  | CPending :: st' => CExplicit :: st'
  | _ => CExplicit :: st
  end.

Definition pop_rbrace (st : CtxStack) : option CtxStack :=
  match st with
  | [] => None
  | _ :: st' => Some st'
  end.

Opaque push_lbrace pop_rbrace.

(* Process one ordinary lexeme at column c: pop every enclosing implicit block
   whose column is greater than c (emitting `}`), then emit the lexeme — with a
   `;` when it starts a sibling at the block's column.  The first lexeme after
   a `let`/`where`/`{` also emits the opening `{`. *)
Fixpoint step_ordinary (col : nat) (t : tok) (st : CtxStack) : CtxStack * list tok :=
  match st with
  | [] => ([], [t])
  | CExplicit :: st' => (st, [t])
  | CPending :: st' => (CBlock col :: st', [TLBrace; t])
  | CBlock blk :: st' =>
      if Nat.ltb col blk
      then let '(st'', emitted) := step_ordinary col t st' in (st'', TRBrace :: emitted)
      else if Nat.eqb col blk && is_decl_starter t
           then (st, [TSemi; t])
           else (st, [t])
  end.

(* The stack algorithm (no accumulator; `++` is O(emitted) per lexeme). *)
Fixpoint layout_go (st : CtxStack) (raw : RawTokens) : option ExplicitTokens :=
  match raw with
  | [] => Some (close st)
  | (c, t) :: rest =>
      match t with
      | TLBrace =>
          match layout_go (push_lbrace st) rest with
          | None => None | Some e => Some (TLBrace :: e)
          end
      | TRBrace =>
          match pop_rbrace st with
          | None => None
          | Some st' =>
              match layout_go st' rest with
              | None => None | Some e => Some (TRBrace :: e)
              end
          end
      | TSemi =>
          match layout_go st rest with
          | None => None | Some e => Some (TSemi :: e)
          end
      | TLet | TWhere =>
          match layout_go (CPending :: st) rest with
          | None => None | Some e => Some (t :: e)
          end
      | TIn | TName | TEq | TLit =>
          let '(st', emitted) := step_ordinary c t st in
          match layout_go st' rest with
          | None => None | Some e => Some (emitted ++ e)
          end
      end
  end.

Definition layout_run (raw : RawTokens) : option ExplicitTokens :=
  layout_go [] raw.

(* ------------------------------------------------------------------------- *)
(* The declarative relation                                                   *)
(* ------------------------------------------------------------------------- *)

(* The ordinary (non-keyword, non-punctuation) lexemes. *)
Inductive ordinary : tok -> Prop :=
| OIn   : ordinary TIn
| OName : ordinary TName
| OEq   : ordinary TEq
| OLit  : ordinary TLit.

(* `Layout st raw e` : the lexemes of `raw`, laid out from context stack `st`,
   produce the explicit stream `e`.  Proof-relevant (the derivation *is* the
   layout). *)
Inductive Layout : CtxStack -> RawTokens -> ExplicitTokens -> Prop :=
| L_nil : forall st, Layout st [] (close st)
| L_lbrace : forall st c raw e,
    Layout (push_lbrace st) raw e ->
    Layout st ((c, TLBrace) :: raw) (TLBrace :: e)
| L_rbrace : forall st st' c raw e,
    pop_rbrace st = Some st' ->
    Layout st' raw e ->
    Layout st ((c, TRBrace) :: raw) (TRBrace :: e)
| L_semi : forall st c raw e,
    Layout st raw e ->
    Layout st ((c, TSemi) :: raw) (TSemi :: e)
| L_let : forall st c raw e,
    Layout (CPending :: st) raw e ->
    Layout st ((c, TLet) :: raw) (TLet :: e)
| L_where : forall st c raw e,
    Layout (CPending :: st) raw e ->
    Layout st ((c, TWhere) :: raw) (TWhere :: e)
| L_ordinary : forall st st' c t raw e emitted,
    ordinary t ->
    step_ordinary c t st = (st', emitted) ->
    Layout st' raw e ->
    Layout st ((c, t) :: raw) (emitted ++ e).

(* ------------------------------------------------------------------------- *)
(* Soundness and completeness                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma layout_go_sound : forall raw st e,
  layout_go st raw = Some e -> Layout st raw e.
Proof.
  induction raw as [| [c t] raw' IH]; intros st e H.
  - cbn in H. injection H as He. subst e. apply L_nil.
  - cbn in H. destruct t.
    + (* TLet *)
      destruct (layout_go (CPending :: st) raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. apply L_let. apply (IH (CPending :: st) l E).
      * discriminate.
    + (* TWhere *)
      destruct (layout_go (CPending :: st) raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. apply L_where. apply (IH (CPending :: st) l E).
      * discriminate.
    + (* TIn *)
      destruct (step_ordinary c TIn st) as [st' emitted] eqn:Es.
      destruct (layout_go st' raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. eapply L_ordinary. apply OIn. exact Es. apply (IH st' l E).
      * discriminate.
    + (* TName *)
      destruct (step_ordinary c TName st) as [st' emitted] eqn:Es.
      destruct (layout_go st' raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. eapply L_ordinary. apply OName. exact Es. apply (IH st' l E).
      * discriminate.
    + (* TEq *)
      destruct (step_ordinary c TEq st) as [st' emitted] eqn:Es.
      destruct (layout_go st' raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. eapply L_ordinary. apply OEq. exact Es. apply (IH st' l E).
      * discriminate.
    + (* TLit *)
      destruct (step_ordinary c TLit st) as [st' emitted] eqn:Es.
      destruct (layout_go st' raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. eapply L_ordinary. apply OLit. exact Es. apply (IH st' l E).
      * discriminate.
    + (* TLBrace *)
      destruct (layout_go (push_lbrace st) raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. apply L_lbrace. apply (IH (push_lbrace st) l E).
      * discriminate.
    + (* TRBrace *)
      destruct (pop_rbrace st) as [st' |] eqn:Ep; cbn in H.
      * destruct (layout_go st' raw') as [l |] eqn:E;
          [ injection H as He; symmetry in He; subst e; apply (L_rbrace st st' c raw' l Ep); apply (IH st' l E)
          | discriminate ].
      * discriminate.
    + (* TSemi *)
      destruct (layout_go st raw') as [l |] eqn:E.
      * injection H as He. symmetry in He. subst e. apply L_semi. apply (IH st l E).
      * discriminate.
Qed.

Lemma layout_complete_gen : forall st raw e, Layout st raw e -> layout_go st raw = Some e.
Proof.
  intros st raw e H.
  induction H as [st | st c raw e | st st' c raw e Ep | st c raw e
      | st c raw e | st c raw e | st st' c t raw e emitted Hord Es]; simpl.
  - reflexivity.
  - rewrite IHLayout. reflexivity.
  - rewrite Ep. rewrite IHLayout. reflexivity.
  - rewrite IHLayout. reflexivity.
  - rewrite IHLayout. reflexivity.
  - rewrite IHLayout. reflexivity.
  - destruct Hord; simpl; rewrite Es; simpl; rewrite IHLayout; reflexivity.
Qed.

Lemma layout_complete : forall raw e, Layout [] raw e -> layout_run raw = Some e.
Proof.
  intros raw e H. unfold layout_run. apply (layout_complete_gen [] raw e H).
Qed.

(* ------------------------------------------------------------------------- *)
(* Examples                                                                  *)
(* ------------------------------------------------------------------------- *)

Transparent push_lbrace pop_rbrace.

(*   let a
*        b
*    in  c   ⇒   let { a ; b } in c                                          *)
Definition ex_let : RawTokens :=
  [(0, TLet); (4, TName); (4, TName); (0, TIn); (0, TName)].

(*   f where { a = 1 ; b = 2 }    (explicit braces override the `where`)     *)
Definition ex_where_explicit : RawTokens :=
  [(0, TName); (2, TWhere); (4, TLBrace);
   (6, TName); (8, TEq); (10, TLit); (6, TSemi);
   (6, TName); (8, TEq); (10, TLit); (4, TRBrace)].

(*   a where
*       b where
*           c
*       d       ⇒   a where { b where { c } ; d }                          *)
Definition ex_nested : RawTokens :=
  [(0, TName); (2, TWhere); (4, TName); (6, TWhere); (8, TName); (4, TName)].

Eval compute in layout_run ex_let.
Eval compute in layout_run ex_where_explicit.
Eval compute in layout_run ex_nested.
