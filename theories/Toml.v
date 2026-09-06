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

(* a document: leading ws, then (stmt ws)* — each statement is followed by ws,
   so the trailing ws is consumed too. *)
Definition doc_spec : Spec ascii unit tom_nt Document :=
  Bind ws_spec (fun _ =>
    Many (Bind stmt_spec (fun s => Bind ws_spec (fun _ => Pure s)))).

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
        | c2 :: rest' =>
            if Ascii.eqb c2 "["%char then
              match parse_key fuel' rest' with
              | Some (k, r) =>
                  match r with
                  | r1 :: r' =>
                      if Ascii.eqb r1 "]"%char then
                        match r' with
                        | r2 :: r'' => if Ascii.eqb r2 "]"%char then Some (SArray k, r'') else None
                        | [] => None
                        end
                      else None
                  | [] => None
                  end
              | None => None
              end
            else
              match parse_key fuel' rest with
              | Some (k, r) =>
                  match r with
                  | r1 :: r'' => if Ascii.eqb r1 "]"%char then Some (STable k, r'') else None
                  | [] => None
                  end
              | None => None
              end
        | [] => None
        end
      else
        match parse_key fuel' w with
        | Some (k, rest1) =>
            match skip_ws rest1 with
            | e :: rest2 =>
                if Ascii.eqb e "="%char then
                  match parse_int (skip_ws rest2) with
                  | Some (v, rest3) => Some (SKV k v, rest3)
                  | None => None
                  end
                else None
            | [] => None
            end
        | None => None
        end
  end.

(* parse-then-validate: surface-parse, then run the state machine *)
Fixpoint parse_doc (fuel : nat) (w : list ascii) : option Document :=
  match skip_ws w with
  | [] => Some []
  | _ =>
      match fuel with
      | O => None
      | S fuel' =>
          match parse_stmt fuel' (skip_ws w) with
          | None => None
          | Some (s, rest) =>
              match parse_doc fuel' rest with
              | None => None
              | Some ss => Some (s :: ss)
              end
          end
      end
  end.

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
Ltac pos := repeat (rewrite length_app; simpl); simpl; lia.

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


(* ------------------------------------------------------------------------- *)
(* Statements                                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma skip_ws_rest_len (w : list ascii) (c : ascii) (rest : list ascii) :
  skip_ws w = c :: rest -> List.length w = List.length (ws_part w) + S (List.length rest).
Proof.
  intros H. rewrite <- (ws_part_skip w) at 1. rewrite H. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma parse_int_shape (w : list ascii) (n : nat) (rest : list ascii) :
  parse_int w = Some (n, rest) -> { pre : list ascii & pre ++ rest = w }.
Proof.
  intros H. unfold parse_int in H.
  destruct w as [| c w']; [discriminate |].
  destruct (is_digit c) eqn:Ed; [| discriminate].
  destruct (take_digits w') as [ds rest'] eqn:Eds.
  injection H as Hn Hrest. subst n rest.
  exists (c :: ds). simpl. f_equal. symmetry. apply (take_digits_shape w' ds rest' Eds).
Qed.

Lemma parse_key_shape : forall fuel w k rest,
  parse_key fuel w = Some (k, rest) -> { pre : list ascii & pre ++ rest = w }.
Proof.
  induction fuel as [| fuel' IH]; intros w k rest Hparse.
  - simpl in Hparse. discriminate.
  - simpl in Hparse.
    destruct (parse_ident w) as [[s rest0] |] eqn:Eid; [| discriminate].
    destruct rest0 as [| c rest'] eqn:Er.
    + injection Hparse as Hk Hrest. subst k rest.
      exists s. symmetry. apply (parse_ident_shape w s [] Eid).
    + destruct (Ascii.eqb c "."%char) eqn:Edot.
      * apply Ascii.eqb_eq in Edot. subst c.
        destruct (parse_key fuel' rest') as [[ks' rest''] |] eqn:Ek; [| discriminate].
        injection Hparse as Hk Hrest. subst k rest.
        destruct (IH rest' ks' rest'' Ek) as [pre Hpre].
        exists (s ++ "."%char :: pre).
        rewrite (parse_ident_shape w s ("."%char :: rest') Eid). rewrite <- app_assoc. simpl. rewrite Hpre. reflexivity.
      * injection Hparse as Hk Hrest. subst k rest.
        exists s. symmetry. apply (parse_ident_shape w s (c :: rest') Eid).
Qed.

Lemma app_len_sub (kpre rest w : list ascii) :
  kpre ++ rest = w -> List.length w - List.length rest = List.length kpre.
Proof.
  intros H. rewrite <- H. rewrite length_app. lia.
Qed.

Lemma kv_ws_pos (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1)
  = List.length prefix + List.length w - List.length ("="%char :: rest2).
Proof.
  intros Hk Hskip.
  assert (Hr : rest1 = ws_part rest1 ++ "="%char :: rest2).
  { symmetry. rewrite <- Hskip. apply (ws_part_skip rest1). }
  assert (H1 : List.length prefix + List.length w - List.length rest1 = List.length prefix + List.length kpre).
  { rewrite <- Hk. rewrite !length_app. lia. }
  assert (H2 : List.length prefix + List.length w - List.length ("="%char :: rest2) = List.length prefix + List.length kpre + List.length (ws_part rest1)).
  { rewrite <- Hk. rewrite Hr at 1. rewrite !length_app. simpl. lia. }
  rewrite H1. rewrite H2. lia.
Qed.

Ltac app := simpl; repeat (rewrite <- app_assoc; simpl); try reflexivity.

Lemma kv_input_eq (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  prefix ++ w = (prefix ++ kpre ++ ws_part rest1) ++ "="%char :: rest2.
Proof.
  intros Hk Hs. rewrite <- Hk. rewrite <- (ws_part_skip rest1) at 1. rewrite Hs. app.
Qed.

Lemma kv_mid_eq (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  (prefix ++ kpre ++ ws_part rest1 ++ ["="%char]) ++ rest2 = prefix ++ w.
Proof.
  intros Hk Hs. rewrite <- Hk. rewrite <- (ws_part_skip rest1) at 2. rewrite Hs. app.
Qed.


Lemma kv_eq_pos (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  List.length prefix + List.length w - List.length rest2 = S (List.length (prefix ++ kpre ++ ws_part rest1)).
Proof.
  intros Hk Hs. rewrite <- Hk. rewrite <- (ws_part_skip rest1) at 1. rewrite Hs. rewrite !length_app. simpl. lia.
Qed.

Lemma kv_eq_len (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  List.length prefix + List.length w - List.length ("="%char :: rest2) = List.length (prefix ++ kpre ++ ws_part rest1).
Proof.
  intros Hk Hs. rewrite <- Hk. rewrite <- (ws_part_skip rest1) at 1. rewrite Hs. rewrite !length_app. simpl. lia.
Qed.

Lemma kv_int_len (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  List.length prefix + List.length w - List.length rest2 + List.length (ws_part rest2) = List.length (prefix ++ kpre ++ ws_part rest1 ++ ["="%char] ++ ws_part rest2).
Proof.
  intros Hk Hs. rewrite <- Hk. rewrite <- (ws_part_skip rest1) at 1. rewrite Hs. rewrite !length_app. simpl. lia.
Qed.

Lemma kv_int_len2 (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  List.length prefix + List.length w = List.length (prefix ++ kpre ++ ws_part rest1 ++ ["="%char] ++ ws_part rest2) + List.length (skip_ws rest2).
Proof.
  intros Hk Hs. rewrite <- Hk. rewrite <- (ws_part_skip rest1) at 1. rewrite Hs. rewrite <- (ws_part_skip rest2) at 1. repeat (rewrite length_app; simpl). lia.
Qed.

Lemma kv_int_eq (prefix kpre rest1 w rest2 : list ascii) :
  kpre ++ rest1 = w -> skip_ws rest1 = "="%char :: rest2 ->
  prefix ++ w = (prefix ++ kpre ++ ws_part rest1 ++ ["="%char] ++ ws_part rest2) ++ skip_ws rest2.
Proof.
  intros Hk Hs. rewrite <- Hk. rewrite <- (ws_part_skip rest1) at 1. rewrite Hs. rewrite <- (ws_part_skip rest2) at 1. app.
Qed.



Lemma parse_stmt_sound (fuel : nat) (prefix w : list ascii) (s : stmt) (rest : list ascii) :
  parse_stmt fuel w = Some (s, rest) ->
  denote surface_grammar (prefix ++ w) stmt_spec tt (List.length prefix) s
    tt (List.length prefix + List.length w - List.length rest).
Proof.
  unfold parse_stmt, stmt_spec in *.
  intros Hparse.
  destruct fuel as [| fuel']; [discriminate |].
  destruct w as [| c w'] eqn:Ew; [discriminate |].
  destruct (Ascii.eqb c "["%char) eqn:Eb.
  - (* bracket: table or array *)
    apply Ascii.eqb_eq in Eb. subst c.
    destruct w' as [| c2 w''] eqn:Ew'; [discriminate |].
    destruct (Ascii.eqb c2 "["%char) eqn:Eb2.
    + (* array [[key]] *)
      apply Ascii.eqb_eq in Eb2. subst c2.
      destruct (parse_key fuel' w'') as [[k r] |] eqn:Ek; [| discriminate].
      destruct r as [| r1 r'] eqn:Er; [discriminate |].
      destruct (Ascii.eqb r1 "]"%char) eqn:Er1; [| discriminate].
      apply Ascii.eqb_eq in Er1. subst r1.
      destruct r' as [| r2 rest''] eqn:Er'; [discriminate |].
      destruct (Ascii.eqb r2 "]"%char) eqn:Er2; [| discriminate].
      apply Ascii.eqb_eq in Er2. subst r2.
      injection Hparse as Hs Hrest. subst s rest.
      destruct (parse_key_shape fuel' w'' k ("]"%char :: "]"%char :: rest'') Ek) as [kpre Hkpre].
      apply d_alt_r. apply d_alt_r.
      apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix)).
      -- apply (ch_sound "["%char prefix ("["%char :: w'')).
      -- apply d_bind with (a := tt) (γ' := tt) (j := S (S (List.length prefix))).
         ++ replace (prefix ++ "["%char :: "["%char :: w'') with ((prefix ++ ["["%char]) ++ "["%char :: w'') by app.
             replace (S (List.length prefix)) with (List.length (prefix ++ ["["%char])) by pos.
             replace (S (S (List.length prefix))) with (S (List.length (prefix ++ ["["%char]))) by pos.
             apply (ch_sound "["%char (prefix ++ ["["%char]) w'').
         ++ apply d_bind with (a := k) (γ' := tt) (j := List.length (prefix ++ ["["%char; "["%char]) + List.length w'' - List.length ("]"%char :: "]"%char :: rest'')).
            ** replace (prefix ++ "["%char :: "["%char :: w'') with ((prefix ++ ["["%char; "["%char]) ++ w'') by app.
               replace (S (S (List.length prefix))) with (List.length (prefix ++ ["["%char; "["%char])) by pos.
               apply (parse_key_sound fuel' (prefix ++ ["["%char; "["%char]) w'' k ("]"%char :: "]"%char :: rest'') Ek).
            ** apply d_bind with (a := tt) (γ' := tt) (j := S (List.length (prefix ++ "["%char :: "["%char :: kpre))).
               -- replace (prefix ++ "["%char :: "["%char :: w'') with ((prefix ++ "["%char :: "["%char :: kpre) ++ "]"%char :: "]"%char :: rest'') by (rewrite <- Hkpre; app).
                  replace (List.length (prefix ++ ["["%char; "["%char]) + List.length w'' - List.length ("]"%char :: "]"%char :: rest'')) with (List.length (prefix ++ "["%char :: "["%char :: kpre)) by (rewrite <- Hkpre; pos).
                  apply (ch_sound "]"%char (prefix ++ "["%char :: "["%char :: kpre) ("]"%char :: rest'')).
               -- apply d_bind with (a := tt) (γ' := tt) (j := S (List.length (prefix ++ "["%char :: "["%char :: kpre ++ ["]"%char]))).
                  ++ replace (prefix ++ "["%char :: "["%char :: w'') with ((prefix ++ "["%char :: "["%char :: kpre ++ ["]"%char]) ++ "]"%char :: rest'') by (rewrite <- Hkpre; app).
                     replace (S (List.length (prefix ++ "["%char :: "["%char :: kpre))) with (List.length (prefix ++ "["%char :: "["%char :: kpre ++ ["]"%char])) by pos.
                     apply (ch_sound "]"%char (prefix ++ "["%char :: "["%char :: kpre ++ ["]"%char]) rest'').
                  ++ replace (List.length prefix + List.length ("["%char :: "["%char :: w'') - List.length rest'') with (S (List.length (prefix ++ "["%char :: "["%char :: kpre ++ ["]"%char]))) by (rewrite <- Hkpre; pos).
                      apply d_pure.
    + (* table [key] *)
      rewrite <- Ew' in *.
      destruct (parse_key fuel' w') as [[k r] |] eqn:Ek; [| discriminate].
      destruct r as [| r1 rest''] eqn:Er; [discriminate |].
      destruct (Ascii.eqb r1 "]"%char) eqn:Er1; [| discriminate].
      apply Ascii.eqb_eq in Er1. subst r1.
      injection Hparse as Hs Hrest. subst s rest.
      destruct (parse_key_shape fuel' w' k ("]"%char :: rest'') Ek) as [kpre Hkpre].
      apply d_alt_r. apply d_alt_l.
      apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix)).
      -- apply (ch_sound "["%char prefix w').
      -- apply d_bind with (a := k) (γ' := tt) (j := List.length (prefix ++ ["["%char]) + List.length w' - List.length ("]"%char :: rest'')).
         ++ replace (prefix ++ "["%char :: w') with ((prefix ++ ["["%char]) ++ w') by app.
             replace (S (List.length prefix)) with (List.length (prefix ++ ["["%char])) by pos.
             apply (parse_key_sound fuel' (prefix ++ ["["%char]) w' k ("]"%char :: rest'') Ek).
         ++ apply d_bind with (a := tt) (γ' := tt) (j := S (List.length (prefix ++ "["%char :: kpre))).
            ** replace (prefix ++ "["%char :: w') with ((prefix ++ "["%char :: kpre) ++ "]"%char :: rest'') by (rewrite <- Hkpre; app).
               replace (List.length (prefix ++ ["["%char]) + List.length w' - List.length ("]"%char :: rest'')) with (List.length (prefix ++ "["%char :: kpre)) by (rewrite <- Hkpre; pos).
               apply (ch_sound "]"%char (prefix ++ "["%char :: kpre) rest'').
            ** replace (List.length prefix + List.length ("["%char :: w') - List.length rest'') with (S (List.length (prefix ++ "["%char :: kpre))) by (rewrite <- Hkpre; pos).
               apply d_pure.
  - (* kv key = value *)
    rewrite <- Ew in *.
    destruct (parse_key fuel' w) as [[k rest1] |] eqn:Hk; [| discriminate].
    destruct (skip_ws rest1) as [| e rest2] eqn:Eskip; [discriminate |].
    destruct (Ascii.eqb e "="%char) eqn:Eeq; [| discriminate].
    apply Ascii.eqb_eq in Eeq. subst e.
    destruct (parse_int (skip_ws rest2)) as [[v rest3] |] eqn:Hi; [| discriminate].
    injection Hparse as Hs Hrest. subst s rest.
    destruct (parse_key_shape fuel' w k rest1 Hk) as [kpre Hkpre].
    apply d_alt_l.
    apply d_bind with (a := k) (γ' := tt) (j := List.length prefix + List.length w - List.length rest1).
    * apply (parse_key_sound fuel' prefix w k rest1 Hk).
    * apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1)).
      -- replace (List.length prefix + List.length w - List.length rest1) with (List.length (prefix ++ w) - List.length rest1) by pos.
         apply (skip_ws_mid_sound (prefix ++ w) rest1).
         exists (prefix ++ kpre). rewrite <- app_assoc. rewrite Hkpre. reflexivity.
      -- replace (List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1)) with (List.length prefix + List.length w - List.length ("="%char :: rest2)) by (symmetry; apply (kv_ws_pos prefix kpre rest1 w rest2 Hkpre Eskip)).
         apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length w - List.length rest2).
         ++ replace (prefix ++ w) with ((prefix ++ kpre ++ ws_part rest1) ++ "="%char :: rest2) by (symmetry; apply (kv_input_eq prefix kpre rest1 w rest2 Hkpre Eskip)).
            replace (List.length prefix + List.length w - List.length ("="%char :: rest2)) with (List.length (prefix ++ kpre ++ ws_part rest1)) by (symmetry; apply (kv_eq_len prefix kpre rest1 w rest2 Hkpre Eskip)).
            replace (List.length prefix + List.length w - List.length rest2) with (S (List.length (prefix ++ kpre ++ ws_part rest1))) by (symmetry; apply (kv_eq_pos prefix kpre rest1 w rest2 Hkpre Eskip)).
            apply (ch_sound "="%char (prefix ++ kpre ++ ws_part rest1) rest2).
         ++ apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length w - List.length rest2 + List.length (ws_part rest2)).
            ** replace (List.length prefix + List.length w - List.length rest2) with (List.length (prefix ++ w) - List.length rest2) by pos.
               apply (skip_ws_mid_sound (prefix ++ w) rest2).
               exists (prefix ++ kpre ++ ws_part rest1 ++ ["="%char]).
               apply (kv_mid_eq prefix kpre rest1 w rest2 Hkpre Eskip).
            ** replace (List.length prefix + List.length w - List.length rest2 + List.length (ws_part rest2)) with (List.length (prefix ++ kpre ++ ws_part rest1 ++ ["="%char] ++ ws_part rest2)) by (symmetry; apply (kv_int_len prefix kpre rest1 w rest2 Hkpre Eskip)).
               apply d_map with (a := v).
               (* int_spec from skip_ws rest2 *)
               replace (prefix ++ w) with ((prefix ++ kpre ++ ws_part rest1 ++ ["="%char] ++ ws_part rest2) ++ skip_ws rest2) by (symmetry; apply (kv_int_eq prefix kpre rest1 w rest2 Hkpre Eskip)).
               replace (List.length prefix + List.length w - List.length rest3) with (List.length (prefix ++ kpre ++ ws_part rest1 ++ ["="%char] ++ ws_part rest2) + List.length (skip_ws rest2) - List.length rest3) by (rewrite (kv_int_len2 prefix kpre rest1 w rest2 Hkpre Eskip); reflexivity).
               apply (parse_int_sound (prefix ++ kpre ++ ws_part rest1 ++ ["="%char] ++ ws_part rest2) (skip_ws rest2) v rest3 Hi).
Qed.



(* ------------------------------------------------------------------------- *)
(* Documents                                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma parse_stmt_shape : forall fuel w s rest,
  parse_stmt fuel w = Some (s, rest) -> { pre : list ascii & pre ++ rest = w }.
Proof.
  intros fuel w s rest Hparse. unfold parse_stmt in Hparse.
  destruct fuel as [| fuel']; [discriminate |].
  destruct w as [| c w'] eqn:Ew; [discriminate |].
  destruct (Ascii.eqb c "["%char) eqn:Eb.
  - apply Ascii.eqb_eq in Eb. subst c.
    destruct w' as [| c2 w''] eqn:Ew'; [discriminate |].
    destruct (Ascii.eqb c2 "["%char) eqn:Eb2.
    + (* array [[key]] *)
      apply Ascii.eqb_eq in Eb2. subst c2.
      destruct (parse_key fuel' w'') as [[k r] |] eqn:Ek; [| discriminate].
      destruct r as [| r1 r'] eqn:Er; [discriminate |].
      destruct (Ascii.eqb r1 "]"%char) eqn:Er1; [| discriminate].
      apply Ascii.eqb_eq in Er1. subst r1.
      destruct r' as [| r2 rest''] eqn:Er'; [discriminate |].
      destruct (Ascii.eqb r2 "]"%char) eqn:Er2; [| discriminate].
      apply Ascii.eqb_eq in Er2. subst r2.
      injection Hparse as Hs Hrest. subst s rest.
      destruct (parse_key_shape fuel' w'' k ("]"%char :: "]"%char :: rest'') Ek) as [kpre Hkpre].
      exists ("["%char :: "["%char :: kpre ++ "]"%char :: "]"%char :: nil).
      rewrite <- Hkpre. app.
    + (* table [key] *)
      rewrite <- Ew' in *.
      destruct (parse_key fuel' w') as [[k r] |] eqn:Ek; [| discriminate].
      destruct r as [| r1 rest''] eqn:Er; [discriminate |].
      destruct (Ascii.eqb r1 "]"%char) eqn:Er1; [| discriminate].
      apply Ascii.eqb_eq in Er1. subst r1.
      injection Hparse as Hs Hrest. subst s rest.
      destruct (parse_key_shape fuel' w' k ("]"%char :: rest'') Ek) as [kpre Hkpre].
      exists ("["%char :: kpre ++ "]"%char :: nil).
      rewrite <- Hkpre. app.
  - (* kv key = value *)
    rewrite <- Ew in *.
    destruct (parse_key fuel' w) as [[k rest1] |] eqn:Hk; [| discriminate].
    destruct (skip_ws rest1) as [| e rest2] eqn:Eskip; [discriminate |].
    destruct (Ascii.eqb e "="%char) eqn:Eeq; [| discriminate].
    apply Ascii.eqb_eq in Eeq. subst e.
    destruct (parse_int (skip_ws rest2)) as [[v rest3] |] eqn:Hi; [| discriminate].
    injection Hparse as Hs Hrest. subst s rest.
    destruct (parse_key_shape fuel' w k rest1 Hk) as [kpre Hkpre].
    destruct (parse_int_shape (skip_ws rest2) v rest3 Hi) as [ipre Hipre].
    exists (kpre ++ ws_part rest1 ++ "="%char :: ws_part rest2 ++ ipre).
    rewrite <- Hkpre. rewrite <- (ws_part_skip rest1) at 2. rewrite Eskip. rewrite <- (ws_part_skip rest2) at 2. app. rewrite Hipre. reflexivity.
Qed.

Lemma doc_mid_len (prefix spre rest' w' : list ascii) :
  spre ++ rest' = w' ->
  List.length prefix + List.length w' - List.length rest' + List.length (ws_part rest') = List.length (prefix ++ spre ++ ws_part rest').
Proof.
  intros H. rewrite <- H. rewrite !length_app. simpl. lia.
Qed.

Lemma doc_tail_len (prefix spre rest' w : list ascii) :
  spre ++ ws_part rest' ++ skip_ws rest' = w ->
  List.length prefix + List.length w = List.length (prefix ++ spre ++ ws_part rest') + List.length (skip_ws rest').
Proof.
  intros H. rewrite <- H. rewrite !length_app. simpl. lia.
Qed.

Lemma parse_doc_many_sound : forall fuel prefix w ss,
  parse_doc fuel w = Some ss ->
  denote surface_grammar (prefix ++ skip_ws w)
    (Many (Bind stmt_spec (fun s => Bind ws_spec (fun _ => Pure s))))
    tt (List.length prefix) ss tt (List.length prefix + List.length (skip_ws w)).
Proof.
  induction fuel as [| fuel' IH]; intros prefix w ss Hparse.
  - simpl in Hparse.
    destruct (skip_ws w) as [| c w']; [| discriminate].
    injection Hparse as Hss. subst ss. replace (List.length prefix + List.length (@nil ascii)) with (List.length prefix) by (simpl; lia). apply d_many_nil.
  - simpl in Hparse.
    destruct (skip_ws w) as [| c w'] eqn:Ew.
    + injection Hparse as Hss. subst ss. replace (List.length prefix + List.length (@nil ascii)) with (List.length prefix) by (simpl; lia). apply d_many_nil.
    + destruct (parse_stmt fuel' (c :: w')) as [[s rest'] |] eqn:Es; [| discriminate].
      destruct (parse_doc fuel' rest') as [ss' |] eqn:Ed; [| discriminate].
      injection Hparse as Hss. subst ss.
      destruct (parse_stmt_shape fuel' (c :: w') s rest' Es) as [spre Hspre].
      apply d_many_cons with (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest' + List.length (ws_part rest')).
      * apply d_bind with (a := s) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest').
        -- apply (parse_stmt_sound fuel' prefix (c :: w') s rest' Es).
        -- apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest' + List.length (ws_part rest')).
           ++ replace (List.length prefix + List.length (c :: w') - List.length rest' + List.length (ws_part rest')) with (List.length (prefix ++ (c :: w')) - List.length rest' + List.length (ws_part rest')) by pos.
              replace (List.length prefix + List.length (c :: w') - List.length rest') with (List.length (prefix ++ (c :: w')) - List.length rest') by pos.
              apply (skip_ws_mid_sound (prefix ++ (c :: w')) rest').
              exists (prefix ++ spre). rewrite <- app_assoc. rewrite Hspre. reflexivity.
           ++ apply d_pure.
      * rewrite <- Ew in *.
        replace (prefix ++ skip_ws w) with ((prefix ++ spre ++ ws_part rest') ++ skip_ws rest')
          by (rewrite <- Hspre; rewrite <- (ws_part_skip rest') at 3; app).
        replace (List.length prefix + List.length (skip_ws w) - List.length rest' + List.length (ws_part rest')) with (List.length (prefix ++ spre ++ ws_part rest')) by (symmetry; apply (doc_mid_len prefix spre rest' (skip_ws w) Hspre)).
        assert (Htail : spre ++ ws_part rest' ++ skip_ws rest' = skip_ws w) by (rewrite <- Hspre; rewrite <- (ws_part_skip rest') at 3; app).
        replace (List.length prefix + List.length (skip_ws w)) with (List.length (prefix ++ spre ++ ws_part rest') + List.length (skip_ws rest')) by (symmetry; apply (doc_tail_len prefix spre rest' (skip_ws w) Htail)).
        apply (IH (prefix ++ spre ++ ws_part rest') rest' ss' Ed).
Qed.

Lemma ws_direct_sound (w : list ascii) :
  denote surface_grammar w ws_spec tt 0 tt tt (List.length (ws_part w)).
Proof.
  replace 0 with (List.length w - List.length w) by (apply Nat.sub_diag).
  replace (List.length (ws_part w)) with (List.length w - List.length w + List.length (ws_part w)) by (rewrite Nat.sub_diag; apply Nat.add_0_l).
  apply (skip_ws_mid_sound w w).
  exists []. reflexivity.
Qed.

Lemma parse_doc_sound : forall fuel w doc,
  parse_doc fuel w = Some doc ->
  denote surface_grammar w doc_spec tt 0 doc tt (List.length w).
Proof.
  intros fuel w doc Hparse. unfold doc_spec.
  apply d_bind with (a := tt) (γ' := tt) (j := List.length (ws_part w)).
  - apply ws_direct_sound.
  - replace (List.length w) with (List.length (ws_part w) + List.length (skip_ws w)) by (symmetry; apply (length_ws_part_skip w)).
    apply (eq_rect (ws_part w ++ skip_ws w)
             (fun x : list ascii => denote surface_grammar x (Many (Bind stmt_spec (fun s => Bind ws_spec (fun _ => Pure s)))) tt (List.length (ws_part w)) doc tt (List.length (ws_part w) + List.length (skip_ws w)))
             (parse_doc_many_sound fuel (ws_part w) w doc Hparse) w (ws_part_skip w)).
Qed.


(* ------------------------------------------------------------------------- *)
(* Direct state-indexed parsing: interleave surface parsing with the state   *)
(* machine, producing a Namespace in a single pass (RP §6.5 "directParse").   *)
(* ------------------------------------------------------------------------- *)

Fixpoint direct_parse (fuel : nat) (ns : Namespace) (w : list ascii) : option Namespace :=
  match skip_ws w with
  | [] => Some ns
  | _ =>
      match fuel with
      | O => None
      | S fuel' =>
          match parse_stmt fuel' (skip_ws w) with
          | None => None
          | Some (s, rest) =>
              match step ns s with
              | None => None
              | Some ns' => direct_parse fuel' ns' rest
              end
          end
      end
  end.

(* direct_parse is equivalent to parse-then-validate: parsing a document and
   folding the transition is the same as stepping while parsing. *)
Lemma parse_doc_O (w : list ascii) :
  parse_doc 0 w = match skip_ws w with [] => Some [] | _ => None end.
Proof. reflexivity. Qed.

Lemma parse_doc_S (fuel : nat) (w : list ascii) :
  parse_doc (S fuel) w =
  match skip_ws w with
  | [] => Some []
  | _ => match parse_stmt fuel (skip_ws w) with
         | None => None
         | Some (s, rest) => match parse_doc fuel rest with None => None | Some ss => Some (s :: ss) end
         end
  end.
Proof. reflexivity. Qed.

Lemma run_O (ns : Namespace) : run ns [] = Some ns.
Proof. reflexivity. Qed.

Lemma direct_parse_O (ns : Namespace) (w : list ascii) :
  direct_parse 0 ns w = match skip_ws w with [] => Some ns | _ => None end.
Proof. reflexivity. Qed.

Lemma direct_parse_S (fuel : nat) (ns : Namespace) (w : list ascii) :
  direct_parse (S fuel) ns w =
  match skip_ws w with
  | [] => Some ns
  | _ => match parse_stmt fuel (skip_ws w) with
         | None => None
         | Some (s, rest) => match step ns s with None => None | Some ns' => direct_parse fuel ns' rest end
         end
  end.
Proof. reflexivity. Qed.

Lemma direct_parse_to_run : forall fuel ns w ns',
  direct_parse fuel ns w = Some ns' ->
  exists doc, parse_doc fuel w = Some doc /\ run ns doc = Some ns'.
Proof.
  induction fuel as [| fuel' IH]; intros ns w ns' H.
  - rewrite direct_parse_O in H.
    destruct (skip_ws w) as [| c w'] eqn:Ew; [| discriminate].
    injection H as Hn. subst ns'. exists [].
    rewrite parse_doc_O. rewrite Ew. simpl. auto.
  - rewrite direct_parse_S in H.
    destruct (skip_ws w) as [| c w'] eqn:Ew.
    + injection H as Hn. subst ns'. exists [].
      rewrite parse_doc_S. rewrite Ew. simpl. auto.
    + destruct (parse_stmt fuel' (c :: w')) as [[s rest] |] eqn:Es; [| discriminate].
      destruct (step ns s) as [ns1 |] eqn:Estep; [| discriminate].
      apply (IH ns1 rest ns') in H. destruct H as [doc [Hp Hr]].
      exists (s :: doc). split.
      * rewrite parse_doc_S. rewrite Ew. simpl. rewrite Es. rewrite Hp. reflexivity.
      * simpl. rewrite Estep. exact Hr.
Qed.

Lemma run_to_direct_parse : forall fuel ns w ns',
  (exists doc, parse_doc fuel w = Some doc /\ run ns doc = Some ns') ->
  direct_parse fuel ns w = Some ns'.
Proof.
  induction fuel as [| fuel' IH]; intros ns w ns' [doc [Hp Hr]].
  - rewrite parse_doc_O in Hp.
    destruct (skip_ws w) as [| c w'] eqn:Ew; [| discriminate].
    injection Hp as Hd. subst doc. simpl in Hr.
    injection Hr as Hn. subst ns'. rewrite direct_parse_O. simpl. rewrite Ew. reflexivity.
  - rewrite parse_doc_S in Hp.
    destruct (skip_ws w) as [| c w'] eqn:Ew.
    + injection Hp as Hd. subst doc. simpl in Hr.
      injection Hr as Hn. subst ns'. rewrite direct_parse_S. simpl. rewrite Ew. reflexivity.
    + destruct (parse_stmt fuel' (c :: w')) as [[s rest] |] eqn:Es; [| discriminate].
      destruct (parse_doc fuel' rest) as [doc' |] eqn:Ed; [| discriminate].
      injection Hp as Hd. subst doc. simpl in Hr.
      destruct (step ns s) as [ns1 |] eqn:Estep; [| discriminate].
      rewrite direct_parse_S. simpl. rewrite Ew. rewrite Es. rewrite Estep.
      apply (IH ns1 rest ns'). exists doc'. split; [exact Ed | exact Hr].
Qed.

Lemma direct_parse_equiv : forall fuel ns w ns',
  direct_parse fuel ns w = Some ns' <->
  (exists doc, parse_doc fuel w = Some doc /\ run ns doc = Some ns').
Proof.
  intros fuel ns w ns'. split.
  - apply direct_parse_to_run.
  - apply run_to_direct_parse.
Qed.
Lemma parse_then_validate_iff_direct : forall w ns,
  parse_then_validate w = Some ns <-> direct_parse (S (2 * List.length w)) [] w = Some ns.
Proof.
  intros w ns. unfold parse_then_validate.
  split; intros H.
  - destruct (parse_doc (S (2 * List.length w)) w) as [doc |] eqn:E; [| discriminate].
    simpl in H. destruct (run [] doc) as [n |] eqn:Er; [| discriminate].
    injection H as Hn. subst n.
    apply (direct_parse_equiv (S (2 * List.length w)) [] w ns).
    exists doc. split; [exact E | exact Er].
  - apply (direct_parse_equiv (S (2 * List.length w)) [] w ns) in H.
    destruct H as [doc [Hp Hr]].
    rewrite Hp. simpl. rewrite Hr. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* Completeness: every denotation is accepted by the parser                   *)
(* ------------------------------------------------------------------------- *)


Lemma nth_error_skipn_head (A : Type) (w : list A) (i : nat) :
  nth_error (skipn i w) 0 = nth_error w i.
Proof.
  revert w. induction i as [| i' IH]; intros w.
  - reflexivity.
  - destruct w as [| a w']; [simpl; reflexivity | simpl; apply IH].
Qed.

Lemma skipn_length_app (prefix w : list ascii) :
  skipn (List.length prefix) (prefix ++ w) = w.
Proof.
  revert w. induction prefix as [| p ps IH]; intros w; simpl; [reflexivity | apply IH].
Qed.

Lemma skipn_cons_head (A : Type) (w : list A) (i : nat) (c : A) :
  nth_error w i = Some c -> skipn i w = c :: skipn (S i) w.
Proof.
  revert w. induction i as [| i' IH]; intros w H.
  - destruct w as [| a w']; simpl in *; [discriminate | injection H as Hc; subst; reflexivity].
  - destruct w as [| a w']; simpl in *; [discriminate | apply IH; exact H].
Qed.

Lemma take_digits_none (w : list ascii) :
  (forall c, nth_error w 0 = Some c -> is_digit c = false) ->
  take_digits w = (nil, w).
Proof.
  destruct w as [| c w']; intros Hnd; simpl; [reflexivity |].
  destruct (is_digit c) eqn:E.
  - assert (Hc : nth_error (c :: w') 0 = Some c) by reflexivity.
    specialize (Hnd c Hc). rewrite Hnd in E. discriminate.
  - reflexivity.
Qed.

Lemma take_ident_none (w : list ascii) :
  (forall c, nth_error w 0 = Some c -> is_ident_char c = false) ->
  take_ident w = (nil, w).
Proof.
  destruct w as [| c w']; intros Hnd; simpl; [reflexivity |].
  destruct (is_ident_char c) eqn:E.
  - assert (Hc : nth_error (c :: w') 0 = Some c) by reflexivity.
    specialize (Hnd c Hc). rewrite Hnd in E. discriminate.
  - reflexivity.
Qed.

(* Keep `skipn`/`take_digits`/`take_ident` abstract while destructing their
   results: `cbn`/`simpl` would otherwise reduce `skipn (S i) (prefix ++ w)`
   by iota (the `nat` argument is a constructor), desynchronising `destruct`. *)
Opaque skipn digits_to_nat.

Lemma take_digits_complete (prefix w : list ascii) (i j : nat) (ds : list ascii) :
  denote surface_grammar (prefix ++ w) (Many digit_spec) tt i ds tt j ->
  (forall c, nth_error (prefix ++ w) j = Some c -> is_digit c = false) ->
  take_digits (skipn i (prefix ++ w)) = (ds, skipn j (prefix ++ w)).
Proof.
  revert prefix w i j. induction ds as [| d ds' IH]; intros prefix w i j Hd Hnd.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii digit_spec tt tt i j (@nil ascii))) in Hd.
    destruct Hd as [Hnil | Hcons].
    + destruct Hnil as [[_ Eg] Ej]. subst.
      apply take_digits_none. intros c Hc.
      rewrite nth_error_skipn_head in Hc. eapply Hnd. exact Hc.
    + destruct Hcons as [a [as' [γ'' [k [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii digit_spec tt tt i j (d :: ds'))) in Hd.
    destruct Hd as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
      injection E as Ed Eas'. subst a as'.
      apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar (prefix ++ w) (fun c => is_digit c = true) d tt γ'' i k)) in Hone.
      destruct Hone as [[[Eg Ej] Hnth] HP]. subst γ''. subst k.
      rewrite (skipn_cons_head ascii (prefix ++ w) i d Hnth).
      cbn -[skipn]. rewrite HP.
      destruct (take_digits (skipn (S i) (prefix ++ w))) as [ds1 rest1] eqn:Etd.
      rewrite (IH prefix w (S i) j Htail Hnd) in Etd. injection Etd as H1 H2. subst ds1 rest1. reflexivity.
Qed.

(* int: a denotation whose next position is not a digit forces parse_int. *)
Lemma int_complete (prefix w : list ascii) (n : nat) (j : nat) :
  denote surface_grammar (prefix ++ w) int_spec tt (List.length prefix) n tt j ->
  (forall c, nth_error (prefix ++ w) j = Some c -> is_digit c = false) ->
  parse_int w = Some (n, skipn j (prefix ++ w)).
Proof.
  intros Hd Hnd. unfold int_spec in Hd.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (ascii * list ascii) nat
    (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p) 0)
    (Seq digit_spec (Many digit_spec)) tt tt (List.length prefix) j n)) in Hd.
  destruct Hd as [p [En Hseq]].
  apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii (list ascii)
    digit_spec (Many digit_spec) tt tt (List.length prefix) j p)) in Hseq.
  destruct Hseq as [γ' [k [d [ds [[Ep Hd1] Hd2]]]]].
  subst p. simpl in En.
  apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar (prefix ++ w) (fun c => is_digit c = true) d tt γ' (List.length prefix) k)) in Hd1.
  destruct Hd1 as [[[Eg Ek] Hnth] HP]. subst γ'. subst k.
  rewrite <- (skipn_length_app prefix w) at 1.
  rewrite (skipn_cons_head ascii (prefix ++ w) (List.length prefix) d Hnth).
  unfold parse_int. cbn -[skipn]. rewrite HP.
  destruct (take_digits (skipn (S (List.length prefix)) (prefix ++ w))) as [ds1 rest1] eqn:Etd.
  rewrite (take_digits_complete prefix w (S (List.length prefix)) j ds Hd2 Hnd) in Etd.
  injection Etd as Hds1 Hrest1. subst ds1 rest1.
  congruence.
Qed.

Lemma take_ident_complete (prefix w : list ascii) (i j : nat) (ds : list ascii) :
  denote surface_grammar (prefix ++ w) (Many (Tok (fun c => is_ident_char c = true))) tt i ds tt j ->
  (forall c, nth_error (prefix ++ w) j = Some c -> is_ident_char c = false) ->
  take_ident (skipn i (prefix ++ w)) = (ds, skipn j (prefix ++ w)).
Proof.
  revert prefix w i j. induction ds as [| d ds' IH]; intros prefix w i j Hd Hnd.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii (Tok (fun c => is_ident_char c = true)) tt tt i j (@nil ascii))) in Hd.
    destruct Hd as [Hnil | Hcons].
    + destruct Hnil as [[_ Eg] Ej]. subst.
      apply take_ident_none. intros c Hc.
      rewrite nth_error_skipn_head in Hc. eapply Hnd. exact Hc.
    + destruct Hcons as [a [as' [γ'' [k [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii (Tok (fun c => is_ident_char c = true)) tt tt i j (d :: ds'))) in Hd.
    destruct Hd as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
      injection E as Ed Eas'. subst a as'.
      apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar (prefix ++ w) (fun c => is_ident_char c = true) d tt γ'' i k)) in Hone.
      destruct Hone as [[[Eg Ej] Hnth] HP]. subst γ''. subst k.
      specialize (IH prefix w (S i) j Htail Hnd).
      rewrite (skipn_cons_head ascii (prefix ++ w) i d Hnth).
      cbn -[skipn]. rewrite HP.
      destruct (take_ident (skipn (S i) (prefix ++ w))) as [ds1 rest1] eqn:Etd.
      rewrite IH in Etd. congruence.
Qed.

Lemma ident_complete (prefix w : list ascii) (s : seg) (j : nat) :
  denote surface_grammar (prefix ++ w) ident_spec tt (List.length prefix) s tt j ->
  (forall c, nth_error (prefix ++ w) j = Some c -> is_ident_char c = false) ->
  parse_ident w = Some (s, skipn j (prefix ++ w)).
Proof.
  intros Hd Hnd. unfold ident_spec in Hd.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (ascii * list ascii) seg
    (fun p : ascii * list ascii => fst p :: snd p)
    (Seq (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true)))) tt tt (List.length prefix) j s)) in Hd.
  destruct Hd as [p [Es Hseq]].
  apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii (list ascii)
    (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true))) tt tt (List.length prefix) j p)) in Hseq.
  destruct Hseq as [γ' [k [d [ds [[Ep Hd1] Hd2]]]]].
  subst p. simpl in Es.
  apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar (prefix ++ w) (fun c => is_ident_char c = true) d tt γ' (List.length prefix) k)) in Hd1.
  destruct Hd1 as [[[Eg Ek] Hnth] HP]. subst γ'. subst k.
  rewrite <- (skipn_length_app prefix w) at 1.
  rewrite (skipn_cons_head ascii (prefix ++ w) (List.length prefix) d Hnth).
  unfold parse_ident. cbn -[skipn]. rewrite HP.
  destruct (take_ident (skipn (S (List.length prefix)) (prefix ++ w))) as [ds1 rest1] eqn:Etd.
  rewrite (take_ident_complete prefix w (S (List.length prefix)) j ds Hd2 Hnd) in Etd.
  injection Etd as Hds1 Hrest1. subst ds1 rest1.
  subst s. reflexivity.
Qed.

Lemma nth_error_self_none (w : list ascii) : nth_error w (List.length w) = None.
Proof. induction w; simpl; [reflexivity | exact IHw]. Qed.

Lemma is_ident_char_dot : is_ident_char "."%char = false.
Proof. unfold is_ident_char. simpl. reflexivity. Qed.

Lemma ch_nth (c : ascii) (w : list ascii) (i j : nat) :
  denote surface_grammar w (ch c) tt i tt tt j -> nth_error w i = Some c /\ j = S i.
Proof.
  intros Hd. unfold ch in Hd.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar w ascii unit (fun _ : ascii => tt) (Tok (fun c' => c' = c)) tt tt i j tt)) in Hd.
  destruct Hd as [t [Et Htok]].
  apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar w (fun c' => c' = c) t tt tt i j)) in Htok.
  destruct Htok as [[[Eg Ej] Hnth] HP]. subst t.
  split; [exact Hnth | exact Ej].
Qed.

Lemma ident_complete_at (prefix w : list ascii) (i j : nat) (s : seg) :
  denote surface_grammar (prefix ++ w) ident_spec tt i s tt j ->
  (forall c, nth_error (prefix ++ w) j = Some c -> is_ident_char c = false) ->
  parse_ident (skipn i (prefix ++ w)) = Some (s, skipn j (prefix ++ w)).
Proof.
  intros Hd Hnd. unfold ident_spec in Hd.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (ascii * list ascii) seg
    (fun p : ascii * list ascii => fst p :: snd p)
    (Seq (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true)))) tt tt i j s)) in Hd.
  destruct Hd as [p [Es Hseq]].
  apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii (list ascii)
    (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true))) tt tt i j p)) in Hseq.
  destruct Hseq as [γ' [k [d [ds [[Ep Hd1] Hd2]]]]].
  subst p. simpl in Es.
  apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar (prefix ++ w) (fun c => is_ident_char c = true) d tt γ' i k)) in Hd1.
  destruct Hd1 as [[[Eg Ek] Hnth] HP]. subst γ'. subst k.
  rewrite (skipn_cons_head ascii (prefix ++ w) i d Hnth).
  unfold parse_ident. cbn -[skipn]. rewrite HP.
  destruct (take_ident (skipn (S i) (prefix ++ w))) as [ds1 rest1] eqn:Etd.
  rewrite (take_ident_complete prefix w (S i) j ds Hd2 Hnd) in Etd.
  injection Etd as Hds1 Hrest1. subst ds1 rest1.
  subst s. reflexivity.
Qed.

Lemma parse_key_mono : forall fuel fuel' w r,
  fuel <= fuel' -> parse_key fuel w = Some r -> parse_key fuel' w = Some r.
Proof.
  induction fuel as [| fuel IH]; intros fuel' w r Hle Hparse.
  - simpl in Hparse. discriminate.
  - destruct fuel' as [| fuel'']; [lia |].
    simpl in Hparse. destruct (parse_ident w) as [[s rest0] |] eqn:Eid; [| discriminate].
    destruct rest0 as [| c rest1] eqn:Er.
    + injection Hparse as Hr. subst r. simpl. rewrite Eid. reflexivity.
    + destruct (Ascii.eqb c "."%char) eqn:Edot.
      * destruct (parse_key fuel rest1) as [[ks rest2] |] eqn:Ek; [| discriminate].
        injection Hparse as Hr. subst r.
        simpl. rewrite Eid. rewrite Edot.
        rewrite (IH fuel'' rest1 (ks, rest2) ltac:(lia) Ek). reflexivity.
      * injection Hparse as Hr. subst r. simpl. rewrite Eid. rewrite Edot. reflexivity.
Qed.

(* Keep `parse_key` abstract so `cbn`/`simpl` do not reduce the recursive call. *)
Opaque parse_key.

(* denote consumes input monotonically forward. *)
Lemma denote_pos_ge : forall A (spec : Spec ascii unit tom_nt A) (a : A) (w : list ascii) i j,
  denote surface_grammar w spec tt i a tt j -> i <= j.
Proof.
  intros A spec a w i j Hd. induction Hd; simpl; lia.
Qed.

(* A single token stays within the input. *)
Lemma tok_spec_end_le : forall P (t : ascii) (w : list ascii) i j,
  denote surface_grammar w (Tok P) tt i t tt j -> j <= List.length w.
Proof.
  intros P t w i j Hd.
  apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar w P t tt tt i j)) in Hd.
  destruct Hd as [[[Eg Ej] Hnth] HP]. subst.
  apply (proj1 (nth_error_Some w i)). intro Hc. rewrite Hnth in Hc. discriminate.
Qed.

(* A Many of single-char tokens stays within the input. *)
Lemma many_tok_end_le : forall P (w : list ascii) k (ds : list ascii) j,
  denote surface_grammar w (Many (Tok P)) tt k ds tt j -> k <= List.length w -> j <= List.length w.
Proof.
  intros P w k ds j. revert k j. induction ds as [| d ds' IH]; intros k j Hd Hk.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar w ascii (Tok P) tt tt k j (@nil ascii))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[_ _] Ej]; subst j; exact Hk | destruct Hcons as [a [as' [_ [k' [[E _] _]]]]]; discriminate].
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar w ascii (Tok P) tt tt k j (d :: ds'))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
    destruct Hcons as [a [as' [γ' [k' [[E Hone] Htail]]]]]. injection E as Ea Eas'. subst a as'.
    apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar w P d tt γ' k k')) in Hone.
    destruct Hone as [[[Eg Ek'] Hnth] HP]. subst γ'. subst k'.
    assert (Hk' : S k <= List.length w).
    { apply (proj1 (nth_error_Some w k)). intro Hc. rewrite Hnth in Hc. discriminate. }
    exact (IH (S k) j Htail Hk').
Qed.

(* The end of an identifier denotation stays within the input. *)
Lemma ident_spec_end_le : forall (w : list ascii) i j (s : seg),
  denote surface_grammar w ident_spec tt i s tt j -> j <= List.length w.
Proof.
  intros w i j s Hd. unfold ident_spec in Hd.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar w (ascii * list ascii) seg
    (fun p : ascii * list ascii => fst p :: snd p)
    (Seq (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true)))) tt tt i j s)) in Hd.
  destruct Hd as [p [Es Hseq]].
  apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar w ascii (list ascii)
    (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true))) tt tt i j p)) in Hseq.
  destruct Hseq as [γ' [k [d [ds [[Ep Hd1] Hd2]]]]].
  apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar w (fun c => is_ident_char c = true) d tt γ' i k)) in Hd1.
  destruct Hd1 as [[[Eg Ek] Hnth] HP]. subst γ'. subst k.
  assert (Hk : S i <= List.length w).
  { apply (proj1 (nth_error_Some w i)). intro Hc. rewrite Hnth in Hc. discriminate. }
  exact (many_tok_end_le (fun c => is_ident_char c = true) w (S i) ds j Hd2 Hk).
Qed.

(* An identifier denotation strictly advances past its start. *)
Lemma ident_spec_pos_ge : forall prefix w s j,
  denote surface_grammar (prefix ++ w) ident_spec tt (List.length prefix) s tt j ->
  S (List.length prefix) <= j.
Proof.
  intros prefix w s j Hd. unfold ident_spec in Hd.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (ascii * list ascii) seg
    (fun p : ascii * list ascii => fst p :: snd p)
    (Seq (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true)))) tt tt (List.length prefix) j s)) in Hd.
  destruct Hd as [p [Es Hseq]].
  apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) ascii (list ascii)
    (Tok (fun c => is_ident_char c = true)) (Many (Tok (fun c => is_ident_char c = true))) tt tt (List.length prefix) j p)) in Hseq.
  destruct Hseq as [γ' [k [d [ds [[Ep Hd1] Hd2]]]]].
  apply (fst (denote_tok_iff ascii unit tom_nt surface_grammar (prefix ++ w) (fun c => is_ident_char c = true) d tt γ' (List.length prefix) k)) in Hd1.
  destruct Hd1 as [[[Eg Ek] Hnth] HP]. subst γ'. subst k.
  exact (denote_pos_ge (list ascii) (Many (Tok (fun c => is_ident_char c = true))) ds (prefix ++ w) (S (List.length prefix)) j Hd2).
Qed.

(* A non-empty dotted-tail denotation ends within the input. *)
Lemma many_tail_end_le : forall prefix w i j s ks,
  denote surface_grammar (prefix ++ w) (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec))) tt i (s :: ks) tt j ->
  j <= List.length (prefix ++ w).
Proof.
  intros prefix w i j s ks. revert prefix w i j s. induction ks as [| s2 ks' IH]; intros prefix w i j s Hd.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt i j (s :: nil))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
    destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]]. injection E as Ea Eas'. subst a as'.
    apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) γ'' tt k j (@nil seg))) in Htail.
    destruct Htail as [Hnil | Hcons]; [| destruct Hcons as [a [as' [γ2 [k2 [[E _] _]]]]]; discriminate].
    destruct Hnil as [[_ Eg] Ej]. subst γ''. subst j.
    apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (unit * seg) seg
      (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec) tt tt i k s)) in Hone.
    destruct Hone as [p [Es Hseq]].
    apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) unit seg
      (ch "."%char) ident_spec tt tt i k p)) in Hseq.
    destruct Hseq as [γ1 [k1 [u [s' [[Ep Hdot] Hid]]]]].
    destruct u. destruct γ1.
    pose proof (ch_nth "."%char (prefix ++ w) i k1 Hdot) as [Hnth Ek1]. subst k1.
    exact (ident_spec_end_le (prefix ++ w) (S i) k s' Hid).
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt i j (s :: s2 :: ks'))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
    destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]]. injection E as Ea Eas'. subst a as'.
    destruct γ''.
    exact (IH prefix w k j s2 Htail).
Qed.

(* A non-empty dotted-tail denotation bounds the number of segments by the
   consumed input length. *)
Lemma many_tail_length_le : forall prefix w i j s ks,
  denote surface_grammar (prefix ++ w) (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec))) tt i (s :: ks) tt j ->
  List.length (s :: ks) <= j - i.
Proof.
  intros prefix w i j s ks. revert prefix w i j s. induction ks as [| s2 ks' IH]; intros prefix w i j s Hd.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt i j (s :: nil))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
    destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]]. injection E as Ea Eas'. subst a as'.
    apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) γ'' tt k j (@nil seg))) in Htail.
    destruct Htail as [Hnil | Hcons]; [| destruct Hcons as [a [as' [γ2 [k2 [[E _] _]]]]]; discriminate].
    destruct Hnil as [[_ Eg] Ej]. subst γ''. subst j.
    apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (unit * seg) seg
      (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec) tt tt i k s)) in Hone.
    destruct Hone as [p [Es Hseq]].
    apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) unit seg
      (ch "."%char) ident_spec tt tt i k p)) in Hseq.
    destruct Hseq as [γ1 [k1 [u [s' [[Ep Hdot] Hid]]]]].
    destruct u. destruct γ1.
    pose proof (ch_nth "."%char (prefix ++ w) i k1 Hdot) as [Hnth Ek1]. subst k1.
    assert (Hge : S i <= k) by (apply (denote_pos_ge seg ident_spec s' (prefix ++ w) (S i) k Hid)).
    simpl. lia.
  - apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt i j (s :: s2 :: ks'))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
    destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]]. injection E as Ea Eas'. subst a as'.
    apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (unit * seg) seg
      (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec) tt γ'' i k s)) in Hone.
    destruct Hone as [p [Es Hseq]].
    apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) unit seg
      (ch "."%char) ident_spec tt γ'' i k p)) in Hseq.
    destruct Hseq as [γ1 [k1 [u [s' [[Ep Hdot] Hid]]]]].
    destruct u. destruct γ1. destruct γ''.
    pose proof (ch_nth "."%char (prefix ++ w) i k1 Hdot) as [Hnth Ek1]. subst k1.
    assert (Hge : S i <= k) by (apply (denote_pos_ge seg ident_spec s' (prefix ++ w) (S i) k Hid)).
    specialize (IH prefix w k j s2 Htail).
    assert (Hkj : k <= j) by (apply (denote_pos_ge (list seg) (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec))) (s2 :: ks') (prefix ++ w) k j Htail)).
    cbn in *. lia.
Qed.

(* The head of a non-empty `Many (. ident)` is a dot at position i. *)
Lemma many_tail_head_dot : forall prefix w i j s ks,
  denote surface_grammar (prefix ++ w) (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec))) tt i (s :: ks) tt j ->
  nth_error (prefix ++ w) i = Some "."%char.
Proof.
  intros prefix w i j s ks Hd.
  apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
    (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt i j (s :: ks))) in Hd.
  destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
  destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
  injection E as Ea Eas'. subst a as'.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (unit * seg) seg
    (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec) tt γ'' i k s)) in Hone.
  destruct Hone as [p [Es Hseq]].
  apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) unit seg
    (ch "."%char) ident_spec tt γ'' i k p)) in Hseq.
  destruct Hseq as [γ1 [k1 [u [s' [[Ep Hdot] Hid]]]]].
  destruct u. destruct γ1.
  exact (proj1 (ch_nth "."%char (prefix ++ w) i k1 Hdot)).
Qed.

Lemma parse_key_O (w : list ascii) : parse_key 0 w = None.
Proof. reflexivity. Qed.

Lemma parse_key_S (fuel : nat) (w : list ascii) :
  parse_key (S fuel) w =
  match parse_ident w with
  | None => None
  | Some (s, rest) =>
      match rest with
      | c :: rest' => if Ascii.eqb c "."%char then
          match parse_key fuel rest' with None => None | Some (ks, rest'') => Some (s :: ks, rest'') end
        else Some ([s], rest)
      | [] => Some ([s], [])
      end
  end.
Proof. reflexivity. Qed.

Lemma key_dotted_complete : forall fuel prefix w i j s1 ks,
  List.length ks <= fuel ->
  denote surface_grammar (prefix ++ w)
    (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)))
    tt i (s1 :: ks) tt j ->
  (forall c, nth_error (prefix ++ w) j = Some c -> c <> "."%char /\ is_ident_char c = false) ->
  parse_key (S fuel) (skipn (S i) (prefix ++ w)) = Some (s1 :: ks, skipn j (prefix ++ w)).
Proof.
  intros fuel prefix w i j s1 ks. revert fuel prefix w i j s1. induction ks as [| s2 ks' IH]; intros fuel prefix w i j s1 Hlen Hd Hnd.
  - (* base: [s1] *)
    apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt i j (s1 :: nil))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
    destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
    injection E as Ea Eas'. subst a as'.
    apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) γ'' tt k j (@nil seg))) in Htail.
    destruct Htail as [Hnil | Hcons]; [| destruct Hcons as [a [as' [γ2 [k2 [[E _] _]]]]]; discriminate].
    destruct Hnil as [[_ Eg] Ej]. subst γ''. subst j.
    apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (unit * seg) seg
      (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec) tt tt i k s1)) in Hone.
    destruct Hone as [p [Es1 Hseq]].
    apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) unit seg
      (ch "."%char) ident_spec tt tt i k p)) in Hseq.
    destruct Hseq as [γ1 [k1 [u [s1' [[Ep Hdot] Hid]]]]].
    subst p. simpl in Es1. subst s1'. destruct u. destruct γ1.
    pose proof (ch_nth "."%char (prefix ++ w) i k1 Hdot) as [Hnth Ek1]. subst k1.
    assert (Himax : forall c, nth_error (prefix ++ w) k = Some c -> is_ident_char c = false).
    { intros c Hc. specialize (Hnd c Hc). destruct Hnd as [_ Hic]. exact Hic. }
    rewrite parse_key_S. simpl. rewrite (ident_complete_at prefix w (S i) k s1 Hid Himax).
    destruct (skipn k (prefix ++ w)) as [| c rest] eqn:Esk; [reflexivity |].
    destruct (Ascii.eqb c "."%char) eqn:Ec; [| reflexivity].
    exfalso. apply Ascii.eqb_eq in Ec. subst c.
    assert (Hc : nth_error (prefix ++ w) k = Some "."%char).
    { rewrite <- nth_error_skipn_head. rewrite Esk. reflexivity. }
    specialize (Hnd "."%char Hc). destruct Hnd as [Hndot _]. exact (Hndot eq_refl).
  - (* recursive: s1 :: s2 :: ks' *)
    apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
      (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt i j (s1 :: s2 :: ks'))) in Hd.
    destruct Hd as [Hnil | Hcons]; [destruct Hnil as [[E _] _]; discriminate |].
    destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
    injection E as Ea Eas'. subst a as'. destruct γ''.
    apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (unit * seg) seg
      (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec) tt tt i k s1)) in Hone.
    destruct Hone as [p [Es1 Hseq]].
    apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) unit seg
      (ch "."%char) ident_spec tt tt i k p)) in Hseq.
    destruct Hseq as [γ1 [k1 [u [s1' [[Ep Hdot] Hid]]]]].
    subst p. simpl in Es1. subst s1'. destruct u. destruct γ1.
    pose proof (ch_nth "."%char (prefix ++ w) i k1 Hdot) as [Hnth Ek1]. subst k1.
    assert (Himax : forall c, nth_error (prefix ++ w) k = Some c -> is_ident_char c = false).
    { intros c Hc. pose proof (many_tail_head_dot prefix w k j s2 ks' Htail) as Hnk.
      rewrite Hnk in Hc. injection Hc as Hc'. subst c. exact is_ident_char_dot. }
    destruct fuel as [| fuel']; [simpl in Hlen; lia |].
    rewrite parse_key_S. cbn -[skipn]. rewrite (ident_complete_at prefix w (S i) k s1 Hid Himax).
    rewrite (skipn_cons_head ascii (prefix ++ w) k "."%char (many_tail_head_dot prefix w k j s2 ks' Htail)).
    cbn -[skipn]. rewrite (IH fuel' prefix w k j s2 ltac:(simpl in Hlen; lia) Htail Hnd). reflexivity.
Qed.

Lemma key_complete (prefix w : list ascii) (k : key) (j : nat) :
  denote surface_grammar (prefix ++ w) key_spec tt (List.length prefix) k tt j ->
  (forall c, nth_error (prefix ++ w) j = Some c -> c <> "."%char /\ is_ident_char c = false) ->
  parse_key (List.length w) w = Some (k, skipn j (prefix ++ w)).
Proof.
  intros Hd Hnd. unfold key_spec in Hd.
  apply (fst (denote_map_iff ascii unit tom_nt surface_grammar (prefix ++ w) (seg * list seg) key
    (fun p : seg * list seg => fst p :: snd p) (Seq ident_spec (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)))) tt tt (List.length prefix) j k)) in Hd.
  destruct Hd as [p [Ek Hseq]].
  apply (fst (denote_seq_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg (list seg)
    ident_spec (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec))) tt tt (List.length prefix) j p)) in Hseq.
  destruct Hseq as [γ' [j1 [s [ks [[Ep Hd1] Hd2]]]]].
  subst p. destruct γ'. simpl in Ek.
  apply (fst (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
    (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt j1 j ks)) in Hd2.
  destruct Hd2 as [Hnil | Hcons].
  + (* ks = [] *)
    destruct Hnil as [[Eks Eg] Ej]. subst ks. subst j. (* j = j1 *)
    assert (Himax : forall c, nth_error (prefix ++ w) j1 = Some c -> is_ident_char c = false).
    { intros c Hc. specialize (Hnd c Hc). destruct Hnd as [_ Hic]. exact Hic. }
    destruct (List.length w) as [| fuel'] eqn:Hlen.
    * destruct w as [| c w']; [| simpl in Hlen; discriminate].
      exfalso. pose proof (ident_complete prefix [] s j1 Hd1 Himax) as Hp.
      unfold parse_ident in Hp. simpl in Hp. discriminate.
    * rewrite parse_key_S. simpl. rewrite (ident_complete prefix w s j1 Hd1 Himax).
      destruct (skipn j1 (prefix ++ w)) as [| c rest] eqn:Esk; [rewrite Ek; reflexivity |].
      destruct (Ascii.eqb c "."%char) eqn:Ec; [| rewrite Ek; reflexivity].
      exfalso. apply Ascii.eqb_eq in Ec. subst c.
      assert (Hc : nth_error (prefix ++ w) j1 = Some "."%char).
      { rewrite <- nth_error_skipn_head. rewrite Esk. reflexivity. }
      specialize (Hnd "."%char Hc). destruct Hnd as [Hndot _]. exact (Hndot eq_refl).
  + (* ks = s1 :: ks' *)
    destruct Hcons as [s1 [ks' [γ2 [j2 [[Eks Hone] Htail]]]]].
    subst ks. destruct γ2. (* k = s :: s1 :: ks' (from Ek) *)
    assert (Hfull : denote surface_grammar (prefix ++ w)
      (Many (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec))) tt j1 (s1 :: ks') tt j).
    { apply (snd (denote_many_iff ascii unit tom_nt surface_grammar (prefix ++ w) seg
        (Map (fun p : unit * seg => snd p) (Seq (ch "."%char) ident_spec)) tt tt j1 j (s1 :: ks'))).
      right. exists s1, ks', tt, j2. split; [split; [reflexivity | exact Hone] | exact Htail]. }
    assert (Himax : forall c, nth_error (prefix ++ w) j1 = Some c -> is_ident_char c = false).
    { intros c Hc. pose proof (many_tail_head_dot prefix w j1 j s1 ks' Hfull) as Hnk.
      rewrite Hnk in Hc. injection Hc as Hc'. subst c. exact is_ident_char_dot. }
    destruct (List.length w) as [| fuel'] eqn:Hlen.
    * destruct w as [| c w']; [| simpl in Hlen; discriminate].
      exfalso. pose proof (ident_complete prefix [] s j1 Hd1 Himax) as Hp.
      unfold parse_ident in Hp. simpl in Hp. discriminate.
    * destruct fuel' as [| fuel''].
      { exfalso.
        pose proof (many_tail_length_le prefix w j1 j s1 ks' Hfull) as Hbnd.
        pose proof (many_tail_end_le prefix w j1 j s1 ks' Hfull) as Hend.
        pose proof (ident_spec_pos_ge prefix w s j1 Hd1) as Hj1.
        rewrite length_app in Hend. rewrite Hlen in Hend. simpl in *. lia. }
      rewrite parse_key_S. simpl. rewrite (ident_complete prefix w s j1 Hd1 Himax).
      rewrite (skipn_cons_head ascii (prefix ++ w) j1 "."%char (many_tail_head_dot prefix w j1 j s1 ks' Hfull)).
      cbn -[skipn]. rewrite (key_dotted_complete fuel'' prefix w j1 j s1 ks' ltac:(pose proof (many_tail_length_le prefix w j1 j s1 ks' Hfull) as Hbnd; pose proof (many_tail_end_le prefix w j1 j s1 ks' Hfull) as Hend; pose proof (ident_spec_pos_ge prefix w s j1 Hd1) as Hj1; rewrite length_app in Hend; rewrite Hlen in Hend; simpl in *; lia) Hfull Hnd). rewrite Ek. reflexivity.
Qed.

Transparent skipn digits_to_nat parse_key.
