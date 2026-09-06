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

From Stdlib Require Import List Bool Nat Ascii Lia ZArith.
Import ListNotations.

(* ------------------------------------------------------------------------- *)
(* Model                                                                      *)
(* ------------------------------------------------------------------------- *)

(* A key is a non-empty dotted path of segment names.  (Abstract segments;
   the surface lexer maps bare/dotted keys onto these.) *)
Definition seg : Type := list ascii.
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

Fixpoint seg_eqb (s1 s2 : seg) : bool :=
  match s1, s2 with
  | [], [] => true
  | c1 :: r1, c2 :: r2 => Ascii.eqb c1 c2 && seg_eqb r1 r2
  | _, _ => false
  end.

Fixpoint key_eqb (k1 k2 : key) : bool :=
  match k1, k2 with
  | [], [] => true
  | s1 :: r1, s2 :: r2 => seg_eqb s1 s2 && key_eqb r1 r2
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
  [SKV [["a"%char]] 1; SKV [["b"%char]; ["c"%char]] 2; SKV [["b"%char]; ["d"%char]] 3].

(* duplicate key:  a = 1  then  a = 2 *)
Definition ex_dup_key : Document := [SKV [["a"%char]] 1; SKV [["a"%char]] 2].

(* table redefinition:  [a]  then  [a] *)
Definition ex_dup_table : Document := [STable [["a"%char]]; STable [["a"%char]]].

(* array re-append:  [[a]]  then  [[a]]  — allowed *)
Definition ex_array_append : Document := [SArray [["a"%char]]; SArray [["a"%char]]].

(* table under a scalar:  a = 1  then  [a.b] — blocked *)
Definition ex_table_under_scalar : Document := [SKV [["a"%char]] 1; STable [["a"%char]; ["b"%char]]].

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

(* ------------------------------------------------------------------------- *)
(* The surface grammar (BNF) — characters to statements                       *)
(* ------------------------------------------------------------------------- *)

Definition surface_grammar : Grammar ascii unit tom_nt :=
  fun (A : Type) (n : tom_nt A) => match n with end.

(* a literal character *)
Definition ch (c : ascii) : Spec ascii unit tom_nt unit :=
  Map (fun _ : ascii => tt) (Tok (fun c' => c' = c)).

Definition is_digit (c : ascii) : bool :=
  Ascii.eqb c "0"%char || Ascii.eqb c "1"%char || Ascii.eqb c "2"%char
  || Ascii.eqb c "3"%char || Ascii.eqb c "4"%char || Ascii.eqb c "5"%char
  || Ascii.eqb c "6"%char || Ascii.eqb c "7"%char || Ascii.eqb c "8"%char
  || Ascii.eqb c "9"%char.

Definition is_ws (c : ascii) : bool :=
  Ascii.eqb c " "%char || Ascii.eqb c "009"%char
  || Ascii.eqb c "010"%char || Ascii.eqb c "013"%char.

(* identifiers: any non-ws, non-structural character *)
Definition is_ident_char (c : ascii) : bool :=
  negb (is_ws c || Ascii.eqb c "="%char || Ascii.eqb c "["%char
        || Ascii.eqb c "]"%char || Ascii.eqb c "."%char).

Definition ws_spec : Spec ascii unit tom_nt unit :=
  Map (fun _ : list unit => tt)
      (Many (Map (fun _ : ascii => tt) (Tok (fun c => is_ws c = true)))).

Definition digit_spec : Spec ascii unit tom_nt ascii := Tok (fun c => is_digit c = true).

Fixpoint digits_to_nat (ds : list ascii) (acc : nat) : nat :=
  match ds with
  | [] => acc
  | d :: rest =>
      if Ascii.eqb d "0"%char then digits_to_nat rest (10 * acc + 0)
      else if Ascii.eqb d "1"%char then digits_to_nat rest (10 * acc + 1)
      else if Ascii.eqb d "2"%char then digits_to_nat rest (10 * acc + 2)
      else if Ascii.eqb d "3"%char then digits_to_nat rest (10 * acc + 3)
      else if Ascii.eqb d "4"%char then digits_to_nat rest (10 * acc + 4)
      else if Ascii.eqb d "5"%char then digits_to_nat rest (10 * acc + 5)
      else if Ascii.eqb d "6"%char then digits_to_nat rest (10 * acc + 6)
      else if Ascii.eqb d "7"%char then digits_to_nat rest (10 * acc + 7)
      else if Ascii.eqb d "8"%char then digits_to_nat rest (10 * acc + 8)
      else digits_to_nat rest (10 * acc + 9)
  end.

(* a non-negative integer: one or more digits *)
Definition int_spec : Spec ascii unit tom_nt nat :=
  Map (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p) 0)
      (Seq digit_spec (Many digit_spec)).

(* a bare identifier: one or more ident characters *)
Definition ident_spec : Spec ascii unit tom_nt seg :=
  Map (fun p : ascii * list ascii => fst p :: snd p)
      (Seq (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true)))).

(* a (possibly dotted) key: ident (. ident)* *)
Definition key_spec : Spec ascii unit tom_nt key :=
  Map (fun p : seg * list seg => fst p :: snd p)
      (Seq ident_spec
           (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)))).

(* key = value *)
Definition kv_spec : Spec ascii unit tom_nt stmt :=
  Bind key_spec (fun k =>
    Bind ws_spec (fun _ =>
      Bind (ch "="%char) (fun _ =>
        Bind ws_spec (fun _ =>
          Map (fun v : nat => SKV k v) int_spec)))).

(* [key] *)
Definition table_spec : Spec ascii unit tom_nt stmt :=
  Bind (ch "["%char) (fun _ =>
    Bind key_spec (fun k =>
      Bind (ch "]"%char) (fun _ => Pure (STable k)))).

(* [[key]] *)
Definition array_spec : Spec ascii unit tom_nt stmt :=
  Bind (ch "["%char) (fun _ =>
    Bind (ch "["%char) (fun _ =>
      Bind key_spec (fun k =>
        Bind (ch "]"%char) (fun _ =>
          Bind (ch "]"%char) (fun _ => Pure (SArray k)))))).

Definition stmt_spec : Spec ascii unit tom_nt stmt :=
  Alt kv_spec (Alt table_spec array_spec).

(* a document: (ws stmt)* ws *)
Definition doc_spec : Spec ascii unit tom_nt Document :=
  Bind ws_spec (fun _ =>
    Many (Bind ws_spec (fun _ => stmt_spec))).

(* ------------------------------------------------------------------------- *)
(* The surface parser (fuel-bounded)                                          *)
(* ------------------------------------------------------------------------- *)

Fixpoint take_digits (w : list ascii) : list ascii * list ascii :=
  match w with
  | c :: rest => if is_digit c then let (ds, r) := take_digits rest in (c :: ds, r) else (nil, w)
  | [] => (nil, nil)
  end.

Fixpoint skip_ws (w : list ascii) : list ascii :=
  match w with
  | c :: rest => if is_ws c then skip_ws rest else w
  | [] => []
  end.

Fixpoint take_ident (w : list ascii) : list ascii * list ascii :=
  match w with
  | c :: rest => if is_ident_char c then let (ds, r) := take_ident rest in (c :: ds, r) else (nil, w)
  | [] => (nil, nil)
  end.

(* parse an integer: returns (value, rest) *)
Definition parse_int (w : list ascii) : option (nat * list ascii) :=
  match w with
  | c :: rest => if is_digit c
      then let (ds, rest') := take_digits rest in Some (digits_to_nat (c :: ds) 0, rest')
      else None
  | [] => None
  end.

(* parse an identifier segment: returns (segment, rest) *)
Definition parse_ident (w : list ascii) : option (seg * list ascii) :=
  match w with
  | c :: rest => if is_ident_char c
      then let (ds, rest') := take_ident rest in Some (c :: ds, rest')
      else None
  | [] => None
  end.

(* parse a (dotted) key *)
Fixpoint parse_key (fuel : nat) (w : list ascii) : option (key * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match parse_ident w with
      | None => None
      | Some (s, rest) =>
          match rest with
          | c :: rest' =>
              if Ascii.eqb c "."%char then
                match parse_key fuel' rest' with
                | None => None
                | Some (ks, rest'') => Some (s :: ks, rest'')
                end
              else Some ([s], rest)
          | [] => Some ([s], [])
          end
      end
  end.

Definition parse_stmt (fuel : nat) (w : list ascii) : option (stmt * list ascii) :=
  match fuel, w with
  | O, _ | _, [] => None
  | S fuel', c :: rest =>
      if Ascii.eqb c "["%char then
        match rest with
        | "["%char :: rest' =>
            match parse_key fuel' rest' with
            | Some (k, "]"%char :: "]"%char :: rest'') => Some (SArray k, rest'')
            | _ => None
            end
        | _ =>
            match parse_key fuel' rest with
            | Some (k, "]"%char :: rest'') => Some (STable k, rest'')
            | _ => None
            end
        end
      else
        match parse_key fuel' w with
        | Some (k, rest) =>
            match skip_ws rest with
            | "="%char :: rest' =>
                match parse_int (skip_ws rest') with
                | Some (v, rest'') => Some (SKV k v, rest'')
                | None => None
                end
            | _ => None
            end
        | _ => None
        end
  end.

Fixpoint parse_doc (fuel : nat) (w : list ascii) : option Document :=
  let w' := skip_ws w in
  match w' with
  | [] => Some []
  | _ =>
      match fuel with
      | O => None
      | S fuel' =>
          match parse_stmt fuel' w' with
          | None => None
          | Some (s, rest) =>
              match parse_doc fuel' rest with
              | None => None
              | Some ss => Some (s :: ss)
              end
          end
      end
  end.

(* parse-then-validate: surface-parse, then run the state machine *)
Definition parse_then_validate (w : list ascii) : option Namespace :=
  match parse_doc (S (2 * List.length w)) w with
  | None => None
  | Some doc => run [] doc
  end.

(* ------------------------------------------------------------------------- *)
(* Surface examples                                                           *)
(* ------------------------------------------------------------------------- *)

Definition ex_text : list ascii :=
  "a"%char :: " "%char :: "="%char :: " "%char :: "1"%char :: "010"%char ::
  "b"%char :: "."%char :: "c"%char :: " "%char :: "="%char :: " "%char :: "2"%char :: "010"%char ::
  "b"%char :: "."%char :: "d"%char :: " "%char :: "="%char :: " "%char :: "3"%char :: [].

Eval compute in parse_doc 100 ex_text.
Eval compute in parse_then_validate ex_text.

(* ------------------------------------------------------------------------- *)
(* Soundness: the surface parser refines `denote`                             *)
(* ------------------------------------------------------------------------- *)

Set Bullet Behavior "None".

Lemma nth_error_app_cons (x : ascii) (prefix rest : list ascii) :
  nth_error (prefix ++ x :: rest) (List.length prefix) = Some x.
Proof.
  induction prefix as [| p ps IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma ch_sound (c : ascii) (prefix rest : list ascii) :
  denote surface_grammar (prefix ++ c :: rest) (ch c) tt (List.length prefix) tt tt (S (List.length prefix)).
Proof.
  unfold ch. apply d_map with (a := c). apply d_tok.
  - exact (nth_error_app_cons c prefix rest).
  - reflexivity.
Qed.

(* The skipped whitespace run at the head of `w`. *)
Fixpoint ws_part (w : list ascii) : list ascii :=
  match w with
  | c :: rest => if is_ws c then c :: ws_part rest else []
  | [] => []
  end.

Lemma ws_part_skip (w : list ascii) : ws_part w ++ skip_ws w = w.
Proof.
  induction w as [| c w' IH]; simpl.
  - reflexivity.
  - destruct (is_ws c) eqn:E; simpl.
    + rewrite IH. reflexivity.
    + reflexivity.
Qed.

Lemma length_ws_part_skip (w : list ascii) :
  List.length w = List.length (ws_part w) + List.length (skip_ws w).
Proof. rewrite <- (ws_part_skip w) at 1. rewrite length_app. reflexivity. Qed.

Lemma skip_ws_many_sound (prefix w rest : list ascii) :
  denote surface_grammar (prefix ++ w ++ rest)
    (Many (Map (fun _ : ascii => tt) (Tok (fun c => is_ws c = true))))
    tt (List.length prefix) (List.map (fun _ : ascii => tt) (ws_part w))
    tt (List.length prefix + List.length (ws_part w)).
Proof.
  revert prefix rest. induction w as [| c w' IH]; intros prefix rest; simpl.
  - rewrite Nat.add_0_r. apply d_many_nil.
  - destruct (is_ws c) eqn:Ews.
    + apply d_many_cons with (γ' := tt) (j := S (List.length prefix)).
      * apply d_map with (a := c). apply d_tok.
        -- exact (nth_error_app_cons c prefix (w' ++ rest)).
        -- exact Ews.
      * replace (prefix ++ c :: w' ++ rest) with ((prefix ++ [c]) ++ w' ++ rest) by (rewrite <- app_assoc; simpl; reflexivity).
        replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
        replace (List.length prefix + List.length (c :: ws_part w')) with (List.length (prefix ++ [c]) + List.length (ws_part w')) by (rewrite length_app; simpl; lia).
        apply (IH (prefix ++ [c]) rest).
    + rewrite Nat.add_0_r. apply d_many_nil.
Qed.

Lemma skip_ws_sound (prefix w rest : list ascii) :
  denote surface_grammar (prefix ++ w ++ rest) ws_spec tt (List.length prefix)
    tt tt (List.length prefix + List.length (ws_part w)).
Proof.
  unfold ws_spec. apply d_map with (a := List.map (fun _ : ascii => tt) (ws_part w)). apply skip_ws_many_sound.
Qed.

Lemma skip_ws_mid_sound (l m : list ascii) :
  { pre : list ascii & pre ++ m = l } ->
  denote surface_grammar l ws_spec tt (List.length l - List.length m) tt
    tt (List.length l - List.length m + List.length (ws_part m)).
Proof.
  intros [pre Hpre].
  replace (List.length l - List.length m) with (List.length pre) by (rewrite <- Hpre; rewrite length_app; lia).
  replace l with (pre ++ m ++ @nil ascii) by (rewrite <- Hpre; rewrite app_nil_r; reflexivity).
  apply (skip_ws_sound pre m (@nil ascii)).
Qed.

(* ------------------------------------------------------------------------- *)
(* Integers                                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma take_digits_sound (prefix w : list ascii) :
  denote surface_grammar (prefix ++ w) (Many digit_spec)
    tt (List.length prefix) (fst (take_digits w)) tt (List.length prefix + List.length (fst (take_digits w))).
Proof.
  revert prefix. induction w as [| c w' IH]; intros prefix; simpl.
  - rewrite Nat.add_0_r. apply d_many_nil.
  - destruct (is_digit c) eqn:Ed.
    + destruct (take_digits w') as [ds rest'] eqn:Eds; simpl in *.
      apply d_many_cons with (γ' := tt) (j := S (List.length prefix)).
      * apply d_tok; [ exact (nth_error_app_cons c prefix w') | exact Ed ].
      * replace (prefix ++ c :: w') with ((prefix ++ [c]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
        replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
        replace (List.length prefix + S (List.length ds)) with (List.length (prefix ++ [c]) + List.length ds) by (rewrite length_app; simpl; lia).
        apply (IH (prefix ++ [c])).
    + rewrite Nat.add_0_r. apply d_many_nil.
Qed.

Lemma take_digits_shape (w ds rest : list ascii) :
  take_digits w = (ds, rest) -> w = ds ++ rest.
Proof.
  revert ds rest.
  induction w as [| c w' IH]; intros ds rest Htake; simpl in Htake.
  - injection Htake as Hds Hrest. subst ds rest. reflexivity.
  - destruct (is_digit c) eqn:Ed.
    + destruct (take_digits w') as [ds' rest'] eqn:Erec.
      injection Htake as Hds Hrest. subst ds rest.
      simpl. f_equal. apply (IH ds' rest' eq_refl).
    + injection Htake as Hds Hrest. subst ds rest. reflexivity.
Qed.

Lemma parse_int_sound (prefix w : list ascii) (n : nat) (rest : list ascii) :
  parse_int w = Some (n, rest) ->
  denote surface_grammar (prefix ++ w) int_spec tt (List.length prefix) n
    tt (List.length prefix + List.length w - List.length rest).
Proof.
  unfold parse_int, int_spec.
  intros Hparse.
  destruct w as [| c w']; [discriminate |].
  destruct (is_digit c) eqn:Ed; [| discriminate].
  destruct (take_digits w') as [ds rest'] eqn:Eds.
  injection Hparse as Hn Hrest. subst n rest.
  apply d_map with (a := (c, ds)).
  apply d_seq with (γ' := tt) (j := S (List.length prefix)).
  - apply d_tok; [ exact (nth_error_app_cons c prefix w') | exact Ed ].
  - replace (prefix ++ c :: w') with ((prefix ++ [c]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
    replace (List.length prefix + List.length (c :: w') - List.length rest') with (List.length (prefix ++ [c]) + List.length ds) by (rewrite (take_digits_shape w' ds rest' Eds); simpl; rewrite !length_app; simpl; lia).
    replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
    pose proof (take_digits_sound (prefix ++ [c]) w') as Hdig.
    rewrite Eds in Hdig. simpl in Hdig. apply Hdig.
Qed.

(* ------------------------------------------------------------------------- *)
(* Identifiers (key segments)                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma take_ident_sound (prefix w : list ascii) :
  denote surface_grammar (prefix ++ w) (Many (Tok (fun c => is_ident_char c = true)))
    tt (List.length prefix) (fst (take_ident w)) tt (List.length prefix + List.length (fst (take_ident w))).
Proof.
  revert prefix. induction w as [| c w' IH]; intros prefix; simpl.
  - rewrite Nat.add_0_r. apply d_many_nil.
  - destruct (is_ident_char c) eqn:Ei.
    + destruct (take_ident w') as [ds rest'] eqn:Eds; simpl in *.
      apply d_many_cons with (γ' := tt) (j := S (List.length prefix)).
      * apply d_tok; [ exact (nth_error_app_cons c prefix w') | exact Ei ].
      * replace (prefix ++ c :: w') with ((prefix ++ [c]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
        replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
        replace (List.length prefix + S (List.length ds)) with (List.length (prefix ++ [c]) + List.length ds) by (rewrite length_app; simpl; lia).
        apply (IH (prefix ++ [c])).
    + rewrite Nat.add_0_r. apply d_many_nil.
Qed.

Lemma take_ident_shape (w ds rest : list ascii) :
  take_ident w = (ds, rest) -> w = ds ++ rest.
Proof.
  revert ds rest.
  induction w as [| c w' IH]; intros ds rest Htake; simpl in Htake.
  - injection Htake as Hds Hrest. subst ds rest. reflexivity.
  - destruct (is_ident_char c) eqn:Ei.
    + destruct (take_ident w') as [ds' rest'] eqn:Erec.
      injection Htake as Hds Hrest. subst ds rest.
      simpl. f_equal. apply (IH ds' rest' eq_refl).
    + injection Htake as Hds Hrest. subst ds rest. reflexivity.
Qed.

Lemma parse_ident_sound (prefix w : list ascii) (s : seg) (rest : list ascii) :
  parse_ident w = Some (s, rest) ->
  denote surface_grammar (prefix ++ w) ident_spec tt (List.length prefix) s
    tt (List.length prefix + List.length w - List.length rest).
Proof.
  unfold parse_ident, ident_spec.
  intros Hparse.
  destruct w as [| c w']; [discriminate |].
  destruct (is_ident_char c) eqn:Ei; [| discriminate].
  destruct (take_ident w') as [ds rest'] eqn:Eds.
  injection Hparse as Hs Hrest. subst s rest.
  apply d_map with (a := (c, ds)).
  apply d_seq with (γ' := tt) (j := S (List.length prefix)).
  - apply d_tok; [ exact (nth_error_app_cons c prefix w') | exact Ei ].
  - replace (prefix ++ c :: w') with ((prefix ++ [c]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
    replace (List.length prefix + List.length (c :: w') - List.length rest') with (List.length (prefix ++ [c]) + List.length ds) by (rewrite (take_ident_shape w' ds rest' Eds); simpl; rewrite !length_app; simpl; lia).
    replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
    pose proof (take_ident_sound (prefix ++ [c]) w') as Hid.
    rewrite Eds in Hid. simpl in Hid. apply Hid.
Qed.

(* ------------------------------------------------------------------------- *)
(* Keys (dotted identifiers)                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma parse_ident_shape (w s rest : list ascii) :
  parse_ident w = Some (s, rest) -> w = s ++ rest.
Proof.
  intros H. unfold parse_ident in H.
  destruct w as [| c w']; [discriminate |].
  destruct (is_ident_char c) eqn:Ei; [| discriminate].
  destruct (take_ident w') as [ds rest'] eqn:Eds.
  injection H as Hs Hrest. subst s rest.
  simpl. f_equal. apply (take_ident_shape w' ds rest' Eds).
Qed.

(* The dotted-tail of a key: `parse_key fuel w` reading `ks` corresponds to
   `Many (· "." ident)` reading `.w`, consuming the leading dot each round. *)
Ltac pos := repeat rewrite length_app; simpl; lia.

Lemma parse_key_many_sound : forall fuel prefix w ks rest,
  parse_key fuel w = Some (ks, rest) ->
  denote surface_grammar (prefix ++ "."%char :: w)
    (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)))
    tt (List.length prefix) ks tt (List.length prefix + S (List.length w) - List.length rest).
Proof.
  induction fuel as [| fuel' IH]; intros prefix w ks rest Hparse.
  - simpl in Hparse. discriminate.
  - simpl in Hparse.
    destruct (parse_ident w) as [[s rest0] |] eqn:Eid; [| discriminate].
    destruct rest0 as [| c rest'] eqn:Er.
    + (* key = [s], rest = [] *)
      injection Hparse as Hk Hrest. subst ks rest.
      replace (List.length prefix + S (List.length w) - List.length (@nil ascii)) with (S (List.length prefix) + List.length w) by pos.
      apply d_many_cons with (γ' := tt) (j := S (List.length prefix) + List.length w).
      * apply d_map with (a := (tt, s)).
        apply d_seq with (γ' := tt) (j := S (List.length prefix)).
        -- apply (ch_sound "."%char prefix w).
        -- replace (prefix ++ "."%char :: w) with ((prefix ++ ["."%char]) ++ w) by (rewrite <- app_assoc; simpl; reflexivity).
           replace (S (List.length prefix) + List.length w) with (List.length (prefix ++ ["."%char]) + List.length w - 0) by pos.
           replace (S (List.length prefix)) with (List.length (prefix ++ ["."%char])) by pos.
           apply (parse_ident_sound (prefix ++ ["."%char]) w s [] Eid).
      * apply d_many_nil.
    + destruct (Ascii.eqb c "."%char) eqn:Edot.
      * apply (Ascii.eqb_eq c "."%char) in Edot. subst c.
        destruct (parse_key fuel' rest') as [[ks' rest''] |] eqn:Ek; [| discriminate].
        injection Hparse as Hk Hrest. subst ks rest.
        replace (List.length prefix + S (List.length w) - List.length rest'') with (List.length (prefix ++ ["."%char] ++ s) + S (List.length rest') - List.length rest'') by (rewrite (parse_ident_shape w s ("."%char :: rest') Eid); pos).
        apply d_many_cons with (γ' := tt) (j := List.length (prefix ++ ["."%char] ++ s)).
        -- apply d_map with (a := (tt, s)).
           apply d_seq with (γ' := tt) (j := S (List.length prefix)).
           ++ apply (ch_sound "."%char prefix w).
           ++ replace (prefix ++ "."%char :: w) with ((prefix ++ ["."%char]) ++ w) by (rewrite <- app_assoc; simpl; reflexivity).
              replace (S (List.length prefix)) with (List.length (prefix ++ ["."%char])) by pos.
              replace (List.length (prefix ++ ["."%char] ++ s)) with (List.length (prefix ++ ["."%char]) + List.length w - List.length ("."%char :: rest')) by (rewrite (parse_ident_shape w s ("."%char :: rest') Eid); pos).
              apply (parse_ident_sound (prefix ++ ["."%char]) w s ("."%char :: rest') Eid).
        -- replace (prefix ++ "."%char :: w) with ((prefix ++ ["."%char] ++ s) ++ "."%char :: rest')
             by (rewrite (parse_ident_shape w s ("."%char :: rest') Eid); simpl; rewrite <- !app_assoc; simpl; reflexivity).
           apply (IH (prefix ++ ["."%char] ++ s) rest' ks' rest'' Ek).
      * injection Hparse as Hk Hrest. subst ks rest.
        replace (List.length prefix + S (List.length w) - List.length (c :: rest')) with (S (List.length prefix) + List.length s) by (rewrite (parse_ident_shape w s (c :: rest') Eid); pos).
        apply d_many_cons with (γ' := tt) (j := S (List.length prefix) + List.length s).
        -- apply d_map with (a := (tt, s)).
           apply d_seq with (γ' := tt) (j := S (List.length prefix)).
           ++ apply (ch_sound "."%char prefix w).
           ++ replace (prefix ++ "."%char :: w) with ((prefix ++ ["."%char]) ++ w) by (rewrite <- app_assoc; simpl; reflexivity).
              replace (S (List.length prefix) + List.length s) with (List.length (prefix ++ ["."%char]) + List.length w - List.length (c :: rest')) by (rewrite (parse_ident_shape w s (c :: rest') Eid); pos).
              replace (S (List.length prefix)) with (List.length (prefix ++ ["."%char])) by pos.
              apply (parse_ident_sound (prefix ++ ["."%char]) w s (c :: rest') Eid).
        -- apply d_many_nil.
Qed.

Lemma parse_key_sound (fuel : nat) (prefix w : list ascii) (k : key) (rest : list ascii) :
  parse_key fuel w = Some (k, rest) ->
  denote surface_grammar (prefix ++ w) key_spec tt (List.length prefix) k
    tt (List.length prefix + List.length w - List.length rest).
Proof.
  unfold key_spec.
  induction fuel as [| fuel' IH]; intros Hparse.
  - simpl in Hparse. discriminate.
  - simpl in Hparse.
    destruct (parse_ident w) as [[s rest0] |] eqn:Eid; [| discriminate].
    destruct rest0 as [| c rest'] eqn:Er.
    + (* key = [s], rest = [] *)
      injection Hparse as Hk Hrest. subst k rest.
      replace (List.length prefix + List.length w - List.length (@nil ascii)) with (List.length prefix + List.length w) by pos.
      apply d_map with (a := (s, @nil seg)).
      apply d_seq with (γ' := tt) (j := List.length prefix + List.length w).
      * replace (List.length prefix + List.length w) with (List.length prefix + List.length w - 0) by pos.
        apply (parse_ident_sound prefix w s [] Eid).
      * apply d_many_nil.
    + destruct (Ascii.eqb c "."%char) eqn:Edot.
      * apply (Ascii.eqb_eq c "."%char) in Edot. subst c.
        destruct (parse_key fuel' rest') as [[ks' rest''] |] eqn:Ek; [| discriminate].
        injection Hparse as Hk Hrest. subst k rest.
        replace (List.length prefix + List.length w - List.length rest'') with (List.length (prefix ++ s) + S (List.length rest') - List.length rest'') by (rewrite (parse_ident_shape w s ("."%char :: rest') Eid); pos).
        apply d_map with (a := (s, ks')).
        apply d_seq with (γ' := tt) (j := List.length (prefix ++ s)).
        -- replace (List.length (prefix ++ s)) with (List.length prefix + List.length w - List.length ("."%char :: rest')) by (rewrite (parse_ident_shape w s ("."%char :: rest') Eid); pos).
           apply (parse_ident_sound prefix w s ("."%char :: rest') Eid).
        -- replace (prefix ++ w) with ((prefix ++ s) ++ "."%char :: rest')
             by (rewrite (parse_ident_shape w s ("."%char :: rest') Eid); rewrite app_assoc; reflexivity).
           apply (parse_key_many_sound fuel' (prefix ++ s) rest' ks' rest'' Ek).
      * injection Hparse as Hk Hrest. subst k rest.
        replace (List.length prefix + List.length w - List.length (c :: rest')) with (List.length prefix + List.length s) by (rewrite (parse_ident_shape w s (c :: rest') Eid); pos).
        apply d_map with (a := (s, @nil seg)).
        apply d_seq with (γ' := tt) (j := List.length prefix + List.length s).
        -- replace (List.length prefix + List.length s) with (List.length prefix + List.length w - List.length (c :: rest')) by (rewrite (parse_ident_shape w s (c :: rest') Eid); pos).
           apply (parse_ident_sound prefix w s (c :: rest') Eid).
        -- apply d_many_nil.
Qed.

