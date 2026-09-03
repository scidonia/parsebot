(* S5 — JSON as the control experiment (RP §6.1).
   First slice: the RFC 8259 grammar as a deep `Spec` over `ascii` tokens,
   with recursion through named nonterminals (`Call` + `Grammar`). A JSON AST
   is threaded through `Map`/`Bind` semantic actions, so a `denote` derivation
   is a derivation-indexed JSON value.

   Recursion: only `value` is recursive (object/array nest values). Named
   nonterminal `NT_value : json_nt Json`; `json_grammar` unfolds it. *)

From Stdlib Require Import List Ascii String ZArith Bool Lia.
Import ListNotations.
From Parsebot Require Import Spec.

(* The soundness lemmas dispatch on the first character, nesting up to eight
   case-analysis levels deep; strict bullet nesting would force unreadable
   `++++++++`-style chains. Bullets here are cosmetic. *)
Set Bullet Behavior "None".

Definition Token := ascii.

(* ------------------------------------------------------------------------- *)
(* 1. JSON abstract syntax                                                    *)


Inductive Json : Type :=
| JNull   : Json
| JBool   : bool -> Json
| JNumber : Z -> Json
| JString : list ascii -> Json
| JArray  : list Json -> Json
| JObject : list (list ascii * Json) -> Json.


(* ------------------------------------------------------------------------- *)
(* 2. Character classes (decidable, executable)                               *)
(* ------------------------------------------------------------------------- *)

Definition is_digitb (c : ascii) : bool :=
  Ascii.eqb c "0"%char || Ascii.eqb c "1"%char || Ascii.eqb c "2"%char
  || Ascii.eqb c "3"%char || Ascii.eqb c "4"%char || Ascii.eqb c "5"%char
  || Ascii.eqb c "6"%char || Ascii.eqb c "7"%char || Ascii.eqb c "8"%char
  || Ascii.eqb c "9"%char.

Definition is_digit1_9b (c : ascii) : bool :=
  Ascii.eqb c "1"%char || Ascii.eqb c "2"%char || Ascii.eqb c "3"%char
  || Ascii.eqb c "4"%char || Ascii.eqb c "5"%char || Ascii.eqb c "6"%char
  || Ascii.eqb c "7"%char || Ascii.eqb c "8"%char || Ascii.eqb c "9"%char.

Definition is_wsb (c : ascii) : bool :=
  Ascii.eqb c "032"%char || Ascii.eqb c "009"%char
  || Ascii.eqb c "010"%char || Ascii.eqb c "013"%char.

(* A string char is any char that is neither the quote nor the backslash. *)
Definition is_string_charb (c : ascii) : bool :=
  negb (Ascii.eqb c "034"%char || Ascii.eqb c "092"%char).

(* ------------------------------------------------------------------------- *)
(* 3. Named nonterminals                                                      *)
(* ------------------------------------------------------------------------- *)

Inductive json_nt : Type -> Type :=
| NT_value : json_nt Json.

(* ------------------------------------------------------------------------- *)
(* 4. Combinator helpers over ascii / unit / json_nt                          *)
(* ------------------------------------------------------------------------- *)

Definition char (c : ascii) : Spec ascii unit json_nt unit :=
  Map (fun _ : ascii => tt) (Tok (fun c' => c' = c)).

Fixpoint lit (s : string) : Spec ascii unit json_nt unit :=
  match s with
  | EmptyString => Pure tt
  | String c s' => Map (fun _ : unit * unit => tt) (Seq (char c) (lit s'))
  end.

(* ws := *( space / tab / lf / cr ) — skipped, discarded. *)
Definition ws : Spec ascii unit json_nt unit :=
  Map (fun _ : list ascii => tt) (Many (Tok (fun c => is_wsb c = true))).

(* ------------------------------------------------------------------------- *)
(* 5. number := [ minus ] int                                                  *)
(*    int    := zero / ( digit1-9 *digit )                                     *)
(* ------------------------------------------------------------------------- *)

Definition digit_val (c : ascii) : nat :=
  if Ascii.eqb c "0"%char then 0
  else if Ascii.eqb c "1"%char then 1
  else if Ascii.eqb c "2"%char then 2
  else if Ascii.eqb c "3"%char then 3
  else if Ascii.eqb c "4"%char then 4
  else if Ascii.eqb c "5"%char then 5
  else if Ascii.eqb c "6"%char then 6
  else if Ascii.eqb c "7"%char then 7
  else if Ascii.eqb c "8"%char then 8
  else if Ascii.eqb c "9"%char then 9
  else 0.

Definition digits_to_nat (cs : list ascii) : nat :=
  List.fold_left (fun acc c => 10 * acc + digit_val c) cs 0.

Definition digit_spec : Spec ascii unit json_nt ascii :=
  Tok (fun c => is_digitb c = true).

Definition digit1_9_spec : Spec ascii unit json_nt ascii :=
  Tok (fun c => is_digit1_9b c = true).

(* int : nat, rejecting leading zeros (per RFC 8259). *)
Definition int_spec : Spec ascii unit json_nt nat :=
  Alt (Map (fun _ : unit => 0) (char "0"))
      (Map (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p))
           (Seq digit1_9_spec (Many digit_spec))).

Definition number_spec : Spec ascii unit json_nt Z :=
  Bind (Alt (Map (fun _ : unit => true) (char "-")) (Pure false))
    (fun neg : bool =>
       Map (fun n : nat => if neg then Z.opp (Z.of_nat n) else Z.of_nat n) int_spec).

(* ------------------------------------------------------------------------- *)
(* 6. string := " *char "  (no escape sequences in this slice)                *)
(* ------------------------------------------------------------------------- *)

Definition string_char_spec : Spec ascii unit json_nt ascii :=
  Tok (fun c => is_string_charb c = true).

Definition string_spec : Spec ascii unit json_nt (list ascii) :=
  Bind (char "034"%char) (fun _ : unit =>
    Bind (Many string_char_spec) (fun cs : list ascii =>
      Bind (char "034"%char) (fun _ : unit => Pure cs))).

(* ------------------------------------------------------------------------- *)
(* 7. member / members / object / elements / array                            *)
(* ------------------------------------------------------------------------- *)

Definition member_spec : Spec ascii unit json_nt (list ascii * Json) :=
  Bind string_spec (fun s : list ascii =>
    Bind ws (fun _ : unit =>
      Bind (char ":") (fun _ : unit =>
        Bind ws (fun _ : unit =>
          Map (fun v : Json => (s, v)) (Call NT_value))))).

(* members := ε | member ws *( "," ws member ws ) *)
Definition members_spec : Spec ascii unit json_nt (list (list ascii * Json)) :=
  Alt (Pure (@nil (list ascii * Json)))
    (Bind member_spec (fun m =>
       Bind ws (fun _ : unit =>
         Map (fun rest : list (list ascii * Json) => m :: rest)
             (Many (Map snd (Seq (char ",") (Bind ws (fun _ : unit =>
               Bind member_spec (fun m' => Bind ws (fun _ : unit => Pure m')))))))))).

Definition object_spec : Spec ascii unit json_nt (list (list ascii * Json)) :=
  Bind (char "{") (fun _ =>
    Bind ws (fun _ =>
      Bind members_spec (fun ms =>
        Bind ws (fun _ =>
          Bind (char "}") (fun _ => Pure ms))))).

(* elements := ε | value ws *( "," ws value ws ) *)
Definition elements_spec : Spec ascii unit json_nt (list Json) :=
  Alt (Pure (@nil Json))
    (Bind (Call NT_value) (fun v =>
       Bind ws (fun _ : unit =>
         Map (fun rest : list Json => v :: rest)
             (Many (Map snd (Seq (char ",") (Bind ws (fun _ : unit =>
               Bind (Call NT_value) (fun v' => Bind ws (fun _ : unit => Pure v')))))))))).

Definition array_spec : Spec ascii unit json_nt (list Json) :=
  Bind (char "[") (fun _ =>
    Bind ws (fun _ =>
      Bind elements_spec (fun vs =>
        Bind ws (fun _ =>
          Bind (char "]") (fun _ => Pure vs))))).

(* ------------------------------------------------------------------------- *)
(* 8. value := false / null / true / object / array / number / string          *)
(* ------------------------------------------------------------------------- *)

Definition value_spec : Spec ascii unit json_nt Json :=
  Alt (Map (fun _ : unit => JNull) (lit "null"))
    (Alt (Alt (Map (fun b : bool => JBool b)
                    (Alt (Map (fun _ : unit => true) (lit "true"))
                         (Map (fun _ : unit => false) (lit "false"))))
              (Map JString string_spec))
         (Alt (Map JNumber number_spec)
              (Alt (Map JArray array_spec)
                   (Map JObject object_spec)))).

Definition json_grammar : Grammar ascii unit json_nt :=
  fun A n => match n in json_nt A' return Spec ascii unit json_nt A' with
             | NT_value => value_spec
             end.

(* The whole-document form: ws value ws. *)
Definition json_text : Spec ascii unit json_nt Json :=
  Bind ws (fun _ => Bind (Call NT_value) (fun v => Bind ws (fun _ => Pure v))).

(* ------------------------------------------------------------------------- *)
(* 9. Example: a hand-built derivation for the document `null`                *)
(* ------------------------------------------------------------------------- *)

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => @nil ascii
  | String c s' => c :: list_of_string s'
  end.
Definition d_null : denote json_grammar (list_of_string "null") json_text tt 0 JNull tt 4.
Proof.
  unfold json_text, ws, value_spec, lit, char.
  repeat (econstructor; simpl; try reflexivity).
Defined.

(* ------------------------------------------------------------------------- *)
(* 10. Executable recursive-descent parser (fuel-bounded; total)              *)
(* ------------------------------------------------------------------------- *)

(* Skip leading whitespace. *)
Fixpoint skip_ws (w : list ascii) : list ascii :=
  match w with
  | c :: rest => if is_wsb c then skip_ws rest else w
  | [] => @nil ascii
  end.

(* Match a literal keyword; return the remaining input. *)
Fixpoint parse_lit (s : string) (w : list ascii) : option (list ascii) :=
  match s, w with
  | EmptyString, _ => Some w
  | String c s', c' :: rest => if Ascii.eqb c c' then parse_lit s' rest else None
  | _, _ => None
  end.

(* Consume string chars until the closing quote. *)
Fixpoint parse_string_chars (w : list ascii) : option (list ascii * list ascii) :=
  match w with
  | [] => None
  | c :: rest =>
      if Ascii.eqb c "034"%char then Some ([], rest)
      else if is_string_charb c then
        match parse_string_chars rest with
        | Some (cs, rest') => Some (c :: cs, rest')
        | None => None
        end
      else None
  end.

(* Parse a string literal (opening quote consumed). *)
Definition parse_string (w : list ascii) : option (list ascii * list ascii) :=
  match w with
  | c :: rest => if Ascii.eqb c "034"%char then parse_string_chars rest else None
  | [] => None
  end.

(* Collect a maximal run of digits. *)
Fixpoint take_digits (w : list ascii) : list ascii * list ascii :=
  match w with
  | c :: rest => if is_digitb c then let '(ds, rest') := take_digits rest in (c :: ds, rest')
                else ([], w)
  | [] => ([], [])
  end.

(* number := [ minus ] int  (integers; no leading zero) *)
Definition parse_number (w : list ascii) : option (Z * list ascii) :=
  match w with
  | [] => None
  | c :: rest =>
      if Ascii.eqb c "-"%char then
        match rest with
        | [] => None
        | d :: rest' =>
            if Ascii.eqb d "0"%char then Some (Z.of_nat 0, rest')
            else if is_digit1_9b d then
              let '(ds, rest'') := take_digits rest' in
              Some (Z.opp (Z.of_nat (digits_to_nat (d :: ds))), rest'')
            else None
        end
      else if Ascii.eqb c "0"%char then Some (Z.of_nat 0, rest)
      else if is_digit1_9b c then
        let '(ds, rest') := take_digits rest in
        Some (Z.of_nat (digits_to_nat (c :: ds)), rest')
      else None
  end.

(* The mutually recursive core: value / object / array / members / elements. *)
Fixpoint parse_value (fuel : nat) (w : list ascii) : option (Json * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match w with
      | [] => None
      | c :: rest =>
          if Ascii.eqb c "{"%char then
            match parse_object fuel' rest with
            | Some (ms, rest') => Some (JObject ms, rest')
            | None => None
            end
          else if Ascii.eqb c "["%char then
            match parse_array fuel' rest with
            | Some (vs, rest') => Some (JArray vs, rest')
            | None => None
            end
          else if Ascii.eqb c "034"%char then
            match parse_string (c :: rest) with
            | Some (s, rest') => Some (JString s, rest')
            | None => None
            end
          else if Ascii.eqb c "t"%char then
            match parse_lit "rue" rest with
            | Some rest' => Some (JBool true, rest')
            | None => None
            end
          else if Ascii.eqb c "f"%char then
            match parse_lit "alse" rest with
            | Some rest' => Some (JBool false, rest')
            | None => None
            end
          else if Ascii.eqb c "n"%char then
            match parse_lit "ull" rest with
            | Some rest' => Some (JNull, rest')
            | None => None
            end
          else if is_digitb c || Ascii.eqb c "-"%char then
            match parse_number w with
            | Some (n, rest') => Some (JNumber n, rest')
            | None => None
            end
          else None
      end
  end

with parse_object (fuel : nat) (w : list ascii) : option ((list (list ascii * Json)) * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match parse_members fuel' (skip_ws w) with
      | None => None
      | Some (ms, rest) =>
          match skip_ws rest with
          | c :: rest' => if Ascii.eqb c "}"%char then Some (ms, rest') else None
          | [] => None
          end
      end
  end

with parse_array (fuel : nat) (w : list ascii) : option ((list Json) * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match parse_elements fuel' (skip_ws w) with
      | None => None
      | Some (vs, rest) =>
          match skip_ws rest with
          | c :: rest' => if Ascii.eqb c "]"%char then Some (vs, rest') else None
          | [] => None
          end
      end
  end

with parse_members (fuel : nat) (w : list ascii) : option ((list (list ascii * Json)) * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match w with
      | [] => None
      | c :: _ =>
          if Ascii.eqb c "}"%char then Some ([], w)
          else match parse_string w with
               | None => None
               | Some (s, rest1) =>
                   match skip_ws rest1 with
                   | c' :: rest2 =>
                       if Ascii.eqb c' ":"%char then
                         match parse_value fuel' (skip_ws rest2) with
                         | None => None
                         | Some (v, rest3) =>
                             match parse_members_more fuel' (skip_ws rest3) with
                             | Some (ms, rest4) => Some ((s, v) :: ms, rest4)
                             | None => None
                             end
                         end
                       else None
                   | [] => None
                   end
               end
      end
  end

with parse_members_more (fuel : nat) (w : list ascii) : option ((list (list ascii * Json)) * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match w with
      | [] => None
      | c :: rest =>
          if Ascii.eqb c "}"%char then Some ([], w)
          else if Ascii.eqb c ","%char then
            match parse_string (skip_ws rest) with
            | None => None
            | Some (s, rest1) =>
                match skip_ws rest1 with
                | c' :: rest2 =>
                    if Ascii.eqb c' ":"%char then
                      match parse_value fuel' (skip_ws rest2) with
                      | None => None
                      | Some (v, rest3) =>
                          match parse_members_more fuel' (skip_ws rest3) with
                          | Some (ms, rest4) => Some ((s, v) :: ms, rest4)
                          | None => None
                          end
                      end
                    else None
                | [] => None
                end
            end
          else None
      end
  end

with parse_elements (fuel : nat) (w : list ascii) : option ((list Json) * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match w with
      | [] => None
      | c :: _ =>
          if Ascii.eqb c "]"%char then Some ([], w)
          else match parse_value fuel' w with
               | None => None
               | Some (v, rest) =>
                   match parse_elements_more fuel' (skip_ws rest) with
                   | Some (vs, rest') => Some (v :: vs, rest')
                   | None => None
                   end
               end
      end
  end

with parse_elements_more (fuel : nat) (w : list ascii) : option ((list Json) * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match w with
      | [] => None
      | c :: rest =>
          if Ascii.eqb c "]"%char then Some ([], w)
          else if Ascii.eqb c ","%char then
            match parse_value fuel' (skip_ws rest) with
            | None => None
            | Some (v, rest) =>
                match parse_elements_more fuel' (skip_ws rest) with
                | Some (vs, rest') => Some (v :: vs, rest')
                | None => None
                end
            end
          else None
      end
  end.

(* Whole-document parse: skip leading ws, parse one value, require trailing
   whitespace only. *)
Definition parse_json (w : list ascii) : option Json :=
  match parse_value (S (S (List.length w))) (skip_ws w) with
  | Some (v, rest) => match skip_ws rest with [] => Some v | _ => None end
  | None => None
  end.

(* ------------------------------------------------------------------------- *)
(* 11. Acceptance: parse RFC 8259 examples                                    *)
(* ------------------------------------------------------------------------- *)

(* An object `{"a":1}` written out as a char list (string literal escaping is
   awkward in Coq; the parser itself accepts ordinary input). *)
Definition obj_input : list ascii :=
  ["{"%char; "034"%char; "a"%char; "034"%char; ":"%char; "1"%char; "}"%char].

Eval compute in (parse_json (list_of_string "null")).
Eval compute in (parse_json (list_of_string "true")).
Eval compute in (parse_json (list_of_string "123")).
Eval compute in (parse_json (list_of_string "-42")).
Eval compute in (parse_json (list_of_string "[1,2,3]")).
Eval compute in (parse_json obj_input).
Eval compute in (parse_json (list_of_string "[true, null]")).

(* ------------------------------------------------------------------------- *)
(* 13. Soundness: the parser only produces denotations                        *)
(* ------------------------------------------------------------------------- *)

(* The repetition tails, for members-more / elements-more soundness. *)
Definition members_rest_spec : Spec ascii unit json_nt (list (list ascii * Json)) :=
  Many (Map snd (Seq (char ",") (Bind ws (fun _ : unit =>
    Bind member_spec (fun m => Bind ws (fun _ : unit => Pure m)))))).
Definition elements_rest_spec : Spec ascii unit json_nt (list Json) :=
  Many (Map snd (Seq (char ",") (Bind ws (fun _ : unit =>
    Bind (Call NT_value) (fun v => Bind ws (fun _ : unit => Pure v)))))).

Lemma nth_error_app_cons (x : ascii) (prefix rest : list ascii) :
  nth_error (prefix ++ x :: rest) (List.length prefix) = Some x.
Proof.
  induction prefix as [| p ps IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma char_sound (c : ascii) (prefix rest : list ascii) :
  denote json_grammar (prefix ++ c :: rest) (char c) tt (List.length prefix) tt tt (S (List.length prefix)).
Proof.
  unfold char. apply d_map with (a := c). apply d_tok.
  - exact (nth_error_app_cons c prefix rest).
  - reflexivity.
Qed.

(* The skipped whitespace run. *)
Fixpoint ws_part (w : list ascii) : list ascii :=
  match w with
  | c :: rest => if is_wsb c then c :: ws_part rest else []
  | [] => []
  end.

Lemma ws_part_skip (w : list ascii) : ws_part w ++ skip_ws w = w.
Proof.
  induction w as [| c w' IH]; simpl.
  - reflexivity.
  - destruct (is_wsb c) eqn:E; simpl.
    + rewrite IH. reflexivity.
    + reflexivity.
Qed.

Lemma length_ws_part_skip (w : list ascii) :
  List.length w = List.length (ws_part w) + List.length (skip_ws w).
Proof. rewrite <- (ws_part_skip w) at 1. rewrite length_app. reflexivity. Qed.
(* The ws run at the head of `w`, with a trailing `rest` suffix. *)
Lemma skip_ws_many_sound (prefix w rest : list ascii) :
  denote json_grammar (prefix ++ w ++ rest) (Many (Tok (fun c => is_wsb c = true)))
    tt (List.length prefix) (ws_part w) tt (List.length prefix + List.length (ws_part w)).
Proof.
  revert prefix rest. induction w as [| c w' IH]; intros prefix rest; simpl.
  - rewrite Nat.add_0_r. apply d_many_nil.
  - destruct (is_wsb c) eqn:Ews.
    + apply d_many_cons with (γ' := tt) (j := S (List.length prefix)).
      * apply d_tok; [ exact (nth_error_app_cons c prefix (w' ++ rest)) | exact Ews ].
      * replace (prefix ++ c :: w' ++ rest) with ((prefix ++ [c]) ++ w' ++ rest) by (rewrite <- app_assoc; simpl; reflexivity).
        replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
        replace (List.length prefix + List.length (c :: ws_part w')) with (List.length (prefix ++ [c]) + List.length (ws_part w')) by (rewrite length_app; simpl; lia).
        apply (IH (prefix ++ [c]) rest).
    + rewrite Nat.add_0_r. apply d_many_nil.
Qed.

Lemma skip_ws_sound (prefix w rest : list ascii) :
  denote json_grammar (prefix ++ w ++ rest) ws tt (List.length prefix) tt tt (List.length prefix + List.length (ws_part w)).
Proof.
  unfold ws. apply d_map with (a := ws_part w). apply skip_ws_many_sound.
Qed.

(* ws at a suffix position: if `m` is a suffix of `l`, the ws run at the head
   of `m` (position `length l - length m`) consumes `ws_part m`. *)
Lemma skip_ws_mid_sound (l m : list ascii) :
  { pre : list ascii & pre ++ m = l } ->
  denote json_grammar l ws tt (List.length l - List.length m) tt tt (List.length l - List.length m + List.length (ws_part m)).
Proof.
  intros [pre Hpre].
  replace (List.length l - List.length m) with (List.length pre) by (rewrite <- Hpre; rewrite length_app; lia).
  replace l with (pre ++ m ++ @nil ascii) by (rewrite <- Hpre; rewrite app_nil_r; reflexivity).
  apply (skip_ws_sound pre m (@nil ascii)).
Qed.

(* The "ws · char c · Pure a" tail at the head of `m`: consumes `ws_part m`,
   then `c`, then yields `a`. Input is `prefix ++ m`; `rest` follows `c`. *)
Lemma ws_char_pure_sound (c : ascii) (A : Type) (a : A) (prefix m rest : list ascii) :
  skip_ws m = c :: rest ->
  denote json_grammar (prefix ++ m) (Bind ws (fun _ => Bind (char c) (fun _ => Pure a))) tt (List.length prefix) a tt (List.length prefix + List.length m - List.length rest).
Proof.
  intros Hskip.
  apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (ws_part m)).
  - replace (prefix ++ m) with (prefix ++ m ++ @nil ascii) by (rewrite app_nil_r; reflexivity).
    apply (skip_ws_sound prefix m (@nil ascii)).
  - apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length m - List.length rest).
    + replace (prefix ++ m) with ((prefix ++ ws_part m) ++ c :: rest) by (rewrite <- app_assoc; rewrite <- Hskip; rewrite (ws_part_skip m); reflexivity).
      replace (List.length prefix + List.length (ws_part m)) with (List.length (prefix ++ ws_part m)) by (rewrite length_app; reflexivity).
      replace (List.length prefix + List.length m - List.length rest) with (S (List.length (prefix ++ ws_part m))) by (rewrite length_app; rewrite (length_ws_part_skip m); rewrite Hskip; simpl; lia).
      apply (char_sound c (prefix ++ ws_part m) rest).
    + apply d_pure.
Qed.
Lemma parse_lit_sound (s : string) (prefix w rest : list ascii) :
  parse_lit s w = Some rest ->
  denote json_grammar (prefix ++ w) (lit s) tt (List.length prefix) tt tt (List.length prefix + List.length w - List.length rest).
Proof.
  revert prefix w rest.
  induction s as [| c s' IH]; intros prefix w rest Hparse; simpl in Hparse.
  - injection Hparse as Hrest. subst rest.
    cbn [lit]. replace (List.length prefix + List.length w - List.length w) with (List.length prefix) by lia.
    apply d_pure.
  - destruct w as [| c' w']; [discriminate |].
    destruct (Ascii.eqb c c') eqn:Eeq; [| discriminate].
    apply (Ascii.eqb_eq c c') in Eeq. subst c'.
    cbn [lit].
    apply d_map with (a := (tt, tt)). apply d_seq with (γ' := tt) (j := S (List.length prefix)).
    * apply (char_sound c prefix w').
    * replace ((prefix ++ c :: w')) with ((prefix ++ [c]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
      replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
      replace (List.length prefix + List.length (c :: w') - List.length rest) with (List.length (prefix ++ [c]) + List.length w' - List.length rest) by (rewrite length_app; simpl; lia).
      apply (IH (prefix ++ [c]) w' rest Hparse).
Qed.

Lemma parse_string_chars_sound (prefix w cs rest : list ascii) :
  parse_string_chars w = Some (cs, rest) ->
  denote json_grammar (prefix ++ w) (Many string_char_spec) tt (List.length prefix) cs tt (List.length prefix + List.length cs).
Proof.
  revert prefix cs rest.
  induction w as [| c w' IH]; intros prefix cs rest Hparse; simpl in Hparse.
  - discriminate.
  - destruct (Ascii.eqb c "034"%char) eqn:Equote.
    + injection Hparse as Hcs Hrest. subst cs rest.
      rewrite Nat.add_0_r. apply d_many_nil.
    + destruct (is_string_charb c) eqn:Echar; [| discriminate].
      destruct (parse_string_chars w') as [[cs' rest'] |] eqn:Erec; [| discriminate].
      injection Hparse as Hcs Hrest. subst cs rest.
      apply d_many_cons with (γ' := tt) (j := S (List.length prefix)).
      * apply d_tok; [ exact (nth_error_app_cons c prefix w') | exact Echar ].
      * replace (prefix ++ c :: w') with ((prefix ++ [c]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
        replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
        replace (List.length prefix + List.length (c :: cs')) with (List.length (prefix ++ [c]) + List.length cs') by (rewrite length_app; simpl; lia).
        apply (IH (prefix ++ [c]) cs' rest' eq_refl).
Qed.

(* Shape of a parsed string content. *)
Lemma parse_string_chars_shape (w cs rest : list ascii) :
  parse_string_chars w = Some (cs, rest) -> w = cs ++ "034"%char :: rest.
Proof.
  revert cs rest.
  induction w as [| c w' IH]; intros cs rest Hparse; simpl in Hparse.
  - discriminate.
  - destruct (Ascii.eqb c "034"%char) eqn:Equote.
    + apply (Ascii.eqb_eq c "034"%char) in Equote. subst c.
      injection Hparse as Hcs Hrest. subst cs rest. reflexivity.
    + destruct (is_string_charb c) eqn:Echar; [| discriminate].
      destruct (parse_string_chars w') as [[cs' rest']|] eqn:Erec; [| discriminate].
      injection Hparse as Hcs Hrest. subst cs rest.
      simpl. f_equal. apply (IH cs' rest' eq_refl).
Qed.

Lemma digit1_9_sound (c : ascii) (prefix rest : list ascii) :
  is_digit1_9b c = true ->
  denote json_grammar (prefix ++ c :: rest) digit1_9_spec tt (List.length prefix) c tt (S (List.length prefix)).
Proof.
  intros Hd. unfold digit1_9_spec. apply d_tok.
  - exact (nth_error_app_cons c prefix rest).
  - exact Hd.
Qed.

Lemma take_digits_sound (prefix w : list ascii) :
  denote json_grammar (prefix ++ w) (Many digit_spec) tt (List.length prefix) (fst (take_digits w)) tt (List.length prefix + List.length (fst (take_digits w))).
Proof.
  revert prefix. induction w as [| c w' IH]; intros prefix; simpl.
  - rewrite Nat.add_0_r. apply d_many_nil.
  - destruct (is_digitb c) eqn:Ed.
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
  - destruct (is_digitb c) eqn:Ed.
    + destruct (take_digits w') as [ds' rest'] eqn:Erec.
      injection Htake as Hds Hrest. subst ds rest.
      simpl. f_equal. apply (IH ds' rest' eq_refl).
    + injection Htake as Hds Hrest. subst ds rest. reflexivity.
Qed.

Lemma number_sound (prefix w : list ascii) (n : Z) (rest : list ascii) :
  parse_number w = Some (n, rest) ->
  denote json_grammar (prefix ++ w) number_spec tt (List.length prefix) n tt (List.length prefix + List.length w - List.length rest).
Proof.
  unfold parse_number, number_spec.
  intros Hparse.
  destruct w as [| c w']; [discriminate |].
  destruct (Ascii.eqb c "-"%char) eqn:Eminus.
  - apply (Ascii.eqb_eq c "-"%char) in Eminus. subst c.
    destruct w' as [| d w'']; [discriminate |].
    destruct (Ascii.eqb d "0"%char) eqn:Ezero.
    + apply (Ascii.eqb_eq d "0"%char) in Ezero. subst d.
      injection Hparse as Hn Hrest. subst n rest.
      apply d_bind with (a := true) (γ' := tt) (j := S (List.length prefix)).
      * apply d_alt_l. apply d_map with (a := tt). apply (char_sound "-"%char prefix ("0"%char :: w'')).
      * apply d_map with (a := 0%nat). apply d_alt_l. apply d_map with (a := tt).
        replace (prefix ++ "-"%char :: "0"%char :: w'') with ((prefix ++ ["-"%char]) ++ "0"%char :: w'') by (rewrite <- app_assoc; simpl; reflexivity).
        replace (S (List.length prefix)) with (List.length (prefix ++ ["-"%char])) by (rewrite length_app; simpl; lia).
        replace (List.length prefix + List.length ("-"%char :: "0"%char :: w'') - List.length w'') with (S (List.length (prefix ++ ["-"%char]))) by (rewrite length_app; simpl; lia).
        apply (char_sound "0"%char (prefix ++ ["-"%char]) w'').
    + destruct (is_digit1_9b d) eqn:E19; [| discriminate].
      destruct (take_digits w'') as [ds rest''] eqn:Eds.
      injection Hparse as Hn Hrest. subst n rest.
      apply d_bind with (a := true) (γ' := tt) (j := S (List.length prefix)).
      * apply d_alt_l. apply d_map with (a := tt). apply (char_sound "-"%char prefix (d :: w'')).
      * apply d_map with (a := digits_to_nat (d :: ds)). apply d_alt_r.
        apply d_map with (a := (d, ds)).
        apply d_seq with (γ' := tt) (j := S (S (List.length prefix))).
        -- replace (prefix ++ "-"%char :: d :: w'') with ((prefix ++ ["-"%char]) ++ d :: w'') by (rewrite <- app_assoc; simpl; reflexivity).
           replace (S (List.length prefix)) with (List.length (prefix ++ ["-"%char])) by (rewrite length_app; simpl; lia).
           apply (digit1_9_sound d (prefix ++ ["-"%char]) w'' E19).
        -- replace (prefix ++ "-"%char :: d :: w'') with ((prefix ++ ["-"%char; d]) ++ w'') by (rewrite <- app_assoc; simpl; reflexivity).
           replace (S (S (List.length prefix))) with (List.length (prefix ++ ["-"%char; d])) by (rewrite length_app; simpl; lia).
           replace (List.length prefix + List.length ("-"%char :: d :: w'') - List.length rest'') with (List.length (prefix ++ ["-"%char; d]) + List.length ds) by (rewrite (take_digits_shape w'' ds rest'' Eds); simpl; rewrite !length_app; simpl; lia).
           pose proof (take_digits_sound (prefix ++ ["-"%char; d]) w'') as Hdig.
           rewrite Eds in Hdig. simpl in Hdig. apply Hdig.
  - destruct (Ascii.eqb c "0"%char) eqn:Ezero.
    + apply (Ascii.eqb_eq c "0"%char) in Ezero. subst c.
      injection Hparse as Hn Hrest. subst n rest.
      apply d_bind with (a := false) (γ' := tt) (j := List.length prefix).
      * apply d_alt_r. apply d_pure.
      * apply d_map with (a := 0%nat). apply d_alt_l. apply d_map with (a := tt).
        replace (List.length prefix + List.length ("0"%char :: w') - List.length w') with (S (List.length prefix)) by (simpl; lia).
        apply (char_sound "0"%char prefix w').
    + destruct (is_digit1_9b c) eqn:E19; [| discriminate].
      destruct (take_digits w') as [ds rest'] eqn:Eds.
      injection Hparse as Hn Hrest. subst n rest.
      apply d_bind with (a := false) (γ' := tt) (j := List.length prefix).
      * apply d_alt_r. apply d_pure.
      * apply d_map with (a := digits_to_nat (c :: ds)). apply d_alt_r.
        apply d_map with (a := (c, ds)).
        apply d_seq with (γ' := tt) (j := S (List.length prefix)).
        -- apply (digit1_9_sound c prefix w' E19).
        -- replace (prefix ++ c :: w') with ((prefix ++ [c]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
           replace (List.length prefix + List.length (c :: w') - List.length rest') with (List.length (prefix ++ [c]) + List.length ds) by (rewrite (take_digits_shape w' ds rest' Eds); simpl; rewrite !length_app; simpl; lia).
           replace (S (List.length prefix)) with (List.length (prefix ++ [c])) by (rewrite length_app; simpl; lia).
           pose proof (take_digits_sound (prefix ++ [c]) w') as Hdig.
           rewrite Eds in Hdig. simpl in Hdig. apply Hdig.
Qed.

Lemma parse_string_sound (prefix w s rest : list ascii) :
  parse_string w = Some (s, rest) ->
  denote json_grammar (prefix ++ w) string_spec tt (List.length prefix) s tt (List.length prefix + List.length w - List.length rest).
Proof.
  unfold parse_string, string_spec.
  intros Hparse.
  destruct w as [| c w']; [discriminate |].
  destruct (Ascii.eqb c "034"%char) eqn:Equote; [| discriminate].
  apply (Ascii.eqb_eq c "034"%char) in Equote. subst c.
  destruct (parse_string_chars w') as [[s' rest'] |] eqn:Echars; [| discriminate].
  injection Hparse as Hs Hrest. subst s rest.
  apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix)).
  - apply (char_sound "034"%char prefix w').
  - apply d_bind with (a := s') (γ' := tt) (j := S (List.length prefix) + List.length s').
    + replace (prefix ++ "034"%char :: w') with ((prefix ++ ["034"%char]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
      replace (S (List.length prefix)) with (List.length (prefix ++ ["034"%char])) by (rewrite length_app; simpl; lia).
      apply (parse_string_chars_sound (prefix ++ ["034"%char]) w' s' rest' Echars).
    + apply d_bind with (a := tt) (γ' := tt) (j := S (S (List.length prefix) + List.length s')).
      * pose proof (parse_string_chars_shape w' s' rest' Echars) as Hshape.
        rewrite Hshape.
        replace (prefix ++ "034"%char :: s' ++ "034"%char :: rest') with ((prefix ++ "034"%char :: s') ++ "034"%char :: rest') by (rewrite app_comm_cons; rewrite app_assoc; reflexivity).
        replace (S (List.length prefix) + List.length s') with (List.length (prefix ++ "034"%char :: s')) by (rewrite !length_app; simpl; lia).
        apply (char_sound "034"%char (prefix ++ "034"%char :: s') rest').
      * pose proof (parse_string_chars_shape w' s' rest' Echars) as Hshape.
        replace (List.length prefix + List.length ("034"%char :: w') - List.length rest') with (S (S (List.length prefix) + List.length s')) by (rewrite Hshape; simpl; rewrite !length_app; simpl; lia).
        apply d_pure.
Qed.

(* Body specs for the recursive descent: `parse_object`/`parse_array` parse the
   *body* (members/elements plus the closing bracket), while `object_spec`/
   `array_spec` include the opening bracket (consumed by `parse_value`). *)
Definition object_body_spec : Spec ascii unit json_nt (list (list ascii * Json)) :=
  Bind ws (fun _ => Bind members_spec (fun ms => Bind ws (fun _ => Bind (char "}") (fun _ => Pure ms)))).
Definition array_body_spec : Spec ascii unit json_nt (list Json) :=
  Bind ws (fun _ => Bind elements_spec (fun vs => Bind ws (fun _ => Bind (char "]") (fun _ => Pure vs)))).

(* Suffix composition, used to thread the parser's remaining input. *)
Lemma suffix_compose (a b c : list ascii) :
  { pre : list ascii & pre ++ b = a } -> { pre2 : list ascii & pre2 ++ c = b } -> { pre3 : list ascii & pre3 ++ c = a }.
Proof.
  intros [p1 H1] [p2 H2]. exists (p1 ++ p2). rewrite <- app_assoc. rewrite H2. exact H1.
Qed.

Lemma skip_ws_suffix (w : list ascii) : { pre : list ascii & pre ++ skip_ws w = w }.
Proof. exists (ws_part w). apply ws_part_skip. Qed.

(* Leaf-parser shapes: the result is a suffix of the input. *)
Lemma parse_lit_shape (s : string) (w rest : list ascii) :
  parse_lit s w = Some rest -> { pre : list ascii & pre ++ rest = w }.
Proof.
  revert w rest. induction s as [| c s' IH]; intros w rest Hparse; simpl in Hparse.
  - injection Hparse as Hr. subst rest. exists (@nil ascii). reflexivity.
  - destruct w as [| c' w']; [discriminate |].
    destruct (Ascii.eqb c c') eqn:E; [| discriminate].
    apply (Ascii.eqb_eq c c') in E. subst c'.
    destruct (IH w' rest Hparse) as [pre Hpre]. exists (c :: pre). simpl. f_equal. exact Hpre.
Qed.

Lemma parse_string_shape (w s rest : list ascii) :
  parse_string w = Some (s, rest) -> { pre : list ascii & pre ++ rest = w }.
Proof.
  unfold parse_string. intros Hparse.
  destruct w as [| c w']; [discriminate |].
  destruct (Ascii.eqb c "034"%char) eqn:E; [| discriminate].
  apply (Ascii.eqb_eq c "034"%char) in E. subst c.
  pose proof (parse_string_chars_shape w' s rest Hparse) as Hsh.
  exists ("034"%char :: s ++ ["034"%char]). rewrite Hsh. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma parse_number_shape (w : list ascii) (n : Z) (rest : list ascii) :
  parse_number w = Some (n, rest) -> { pre : list ascii & pre ++ rest = w }.
Proof.
  unfold parse_number. intros Hparse.
  destruct w as [| c w']; [discriminate |].
  destruct (Ascii.eqb c "-"%char) eqn:Eminus.
  - apply (Ascii.eqb_eq c "-"%char) in Eminus. subst c.
    destruct w' as [| d w'']; [discriminate |].
    destruct (Ascii.eqb d "0"%char) eqn:E0.
    + apply (Ascii.eqb_eq d "0"%char) in E0. subst d.
      injection Hparse as Hn Hr. subst n rest. exists ["-"%char; "0"%char]. reflexivity.
    + destruct (is_digit1_9b d) eqn:E19; [| discriminate].
      destruct (take_digits w'') as [ds rest''] eqn:Eds.
      injection Hparse as Hn Hr. subst n rest.
      exists ("-"%char :: d :: ds). simpl. f_equal. f_equal. symmetry. apply (take_digits_shape w'' ds rest'' Eds).
  - destruct (Ascii.eqb c "0"%char) eqn:E0.
    + apply (Ascii.eqb_eq c "0"%char) in E0. subst c.
      injection Hparse as Hn Hr. subst n rest. exists ["0"%char]. reflexivity.
    + destruct (is_digit1_9b c) eqn:E19; [| discriminate].
      destruct (take_digits w') as [ds rest'] eqn:Eds.
      injection Hparse as Hn Hr. subst n rest.
      exists (c :: ds). simpl. f_equal. symmetry. apply (take_digits_shape w' ds rest' Eds).
Qed.

(* Keep the leaf parsers abstract during the mutual soundness argument: `simpl`
   must reduce `parse_value` to its `match parse_lit/parse_string/parse_number`
   form without further unfolding those (which would desynchronise `destruct`
   over their results). `vm_compute` (the `Eval compute` gates and extraction)
   ignores opacity. *)
Opaque parse_lit parse_string parse_number.
(* The seven recursive parsers each leave a suffix. *)
Lemma parse_all_shape : forall fuel,
  (forall w v rest, parse_value fuel w = Some (v, rest) -> { pre : list ascii & pre ++ rest = w })
  * (forall w ms rest, parse_object fuel w = Some (ms, rest) -> { pre : list ascii & pre ++ rest = w })
  * (forall w vs rest, parse_array fuel w = Some (vs, rest) -> { pre : list ascii & pre ++ rest = w })
  * (forall w ms rest, parse_members fuel w = Some (ms, rest) -> { pre : list ascii & pre ++ rest = w })
  * (forall w ms rest, parse_members_more fuel w = Some (ms, rest) -> { pre : list ascii & pre ++ rest = w })
  * (forall w vs rest, parse_elements fuel w = Some (vs, rest) -> { pre : list ascii & pre ++ rest = w })
  * (forall w vs rest, parse_elements_more fuel w = Some (vs, rest) -> { pre : list ascii & pre ++ rest = w }).
Proof.
  induction fuel as [| fuel' IH]; simpl.
  - repeat split; intros; discriminate.
  - destruct IH as [[[[[[IHv IHo] IHa] IHm] IHmm] IHe] IHem].
    repeat split; intros w res rest Hparse.
    + (* value *)
      destruct w as [| c w']; [discriminate |].
      destruct (Ascii.eqb c "{"%char) eqn:E1.
      * apply (Ascii.eqb_eq c "{"%char) in E1. subst c. simpl in Hparse.
        destruct (parse_object fuel' w') as [[ms rest'] |] eqn:Eo.
        -- injection Hparse as Hr Hrest. subst res rest.
           destruct (IHo w' ms rest' Eo) as [pre Hpre]. exists ("{"%char :: pre). simpl. f_equal. exact Hpre.
        -- simpl in *; discriminate.
      * destruct (Ascii.eqb c "["%char) eqn:E2.
        -- apply (Ascii.eqb_eq c "["%char) in E2. subst c. simpl in Hparse.
           destruct (parse_array fuel' w') as [[vs rest'] |] eqn:Ea.
           ++ injection Hparse as Hr Hrest. subst res rest.
              destruct (IHa w' vs rest' Ea) as [pre Hpre]. exists ("["%char :: pre). simpl. f_equal. exact Hpre.
           ++ simpl in *; discriminate.
        -- destruct (Ascii.eqb c "034"%char) eqn:E3.
           ++ apply (Ascii.eqb_eq c "034"%char) in E3. subst c. simpl in Hparse.
              destruct (parse_string ("034"%char :: w')) as [[s rest'] |] eqn:Es.
              -- injection Hparse as Hr Hrest. subst res rest.
                 destruct (parse_string_shape ("034"%char :: w') s rest' Es) as [pre Hpre].
                 exists pre; exact Hpre.
              -- simpl in *; discriminate.
           ++ destruct (Ascii.eqb c "t"%char) eqn:E4.
              -- apply (Ascii.eqb_eq c "t"%char) in E4. subst c. simpl in Hparse.
                 destruct (parse_lit "rue" w') as [rest' |] eqn:El.
                 ++ injection Hparse as Hr Hrest. subst res rest.
                    destruct (parse_lit_shape "rue" w' rest' El) as [pre Hpre].
                    exists ("t"%char :: pre). simpl. f_equal. exact Hpre.
                 ++ simpl in *; discriminate.
              -- destruct (Ascii.eqb c "f"%char) eqn:E5.
                 ++ apply (Ascii.eqb_eq c "f"%char) in E5. subst c. simpl in Hparse.
                    destruct (parse_lit "alse" w') as [rest' |] eqn:El.
                    -- injection Hparse as Hr Hrest. subst res rest.
                       destruct (parse_lit_shape "alse" w' rest' El) as [pre Hpre].
                       exists ("f"%char :: pre). simpl. f_equal. exact Hpre.
                    -- simpl in *; discriminate.
                 ++ destruct (Ascii.eqb c "n"%char) eqn:E6.
                    -- apply (Ascii.eqb_eq c "n"%char) in E6. subst c. simpl in Hparse.
                       destruct (parse_lit "ull" w') as [rest' |] eqn:El.
                       ++ injection Hparse as Hr Hrest. subst res rest.
                          destruct (parse_lit_shape "ull" w' rest' El) as [pre Hpre].
                          exists ("n"%char :: pre). simpl. f_equal. exact Hpre.
                       ++ simpl in *; discriminate.
                    -- destruct (is_digitb c) eqn:E7; [| destruct (Ascii.eqb c "-"%char) eqn:E8; [| discriminate]].
                       ++ simpl in Hparse. destruct (parse_number (c :: w')) as [[n rest'] |] eqn:En.
                          -- injection Hparse as Hr Hrest. subst res rest.
                             exact (parse_number_shape (c :: w') n rest' En).
                          -- simpl in *; discriminate.
                       ++ simpl in Hparse. destruct (parse_number (c :: w')) as [[n rest'] |] eqn:En.
                          -- injection Hparse as Hr Hrest. subst res rest.
                             exact (parse_number_shape (c :: w') n rest' En).
                          -- simpl in *; discriminate.
    + (* object *)
      destruct (parse_members fuel' (skip_ws w)) as [[ms mrest] |] eqn:Em; [| discriminate].
      destruct (skip_ws mrest) as [| c rem] eqn:Eskip; [discriminate |].
      destruct (Ascii.eqb c "}"%char) eqn:Eclose; [| discriminate].
      apply (Ascii.eqb_eq c "}"%char) in Eclose. subst c.
      injection Hparse as Hr Hrest. subst res rem.
      destruct (IHm (skip_ws w) ms mrest Em) as [pre Hpre].
      apply (suffix_compose w mrest rest).
      * apply (suffix_compose w (skip_ws w) mrest). exact (skip_ws_suffix w). exact (existT _ pre Hpre).
      * (* rem is a suffix of mrest: mrest = ws_part mrest ++ "}" :: rem *)
        assert (Hs : ws_part mrest ++ "}"%char :: rest = mrest).
        { rewrite <- ws_part_skip. rewrite Eskip. reflexivity. }
        exists (ws_part mrest ++ ["}"%char]). rewrite <- app_assoc. simpl. exact Hs.
    + (* array *)
      destruct (parse_elements fuel' (skip_ws w)) as [[vs erest] |] eqn:Ee; [| discriminate].
      destruct (skip_ws erest) as [| c rem] eqn:Eskip; [discriminate |].
      destruct (Ascii.eqb c "]"%char) eqn:Eclose; [| discriminate].
      apply (Ascii.eqb_eq c "]"%char) in Eclose. subst c.
      injection Hparse as Hr Hrest. subst res rem.
      destruct (IHe (skip_ws w) vs erest Ee) as [pre Hpre].
      apply (suffix_compose w erest rest).
      * apply (suffix_compose w (skip_ws w) erest). exact (skip_ws_suffix w). exact (existT _ pre Hpre).
      * assert (Hs : ws_part erest ++ "]"%char :: rest = erest).
        { rewrite <- ws_part_skip. rewrite Eskip. reflexivity. }
        exists (ws_part erest ++ ("]"%char :: nil)). rewrite <- app_assoc. simpl. exact Hs.
    + (* members *)
      destruct w as [| c w']; [discriminate |].
      destruct (Ascii.eqb c "}"%char) eqn:Eclose;
      [ apply (Ascii.eqb_eq c "}"%char) in Eclose; subst c; simpl in Hparse;
        injection Hparse as Hr Hrest; subst res rest; exists (@nil ascii); reflexivity
      | simpl in Hparse;
        destruct (parse_string (c :: w')) as [[s rest1] |] eqn:Es;
        [ simpl in Hparse;
          destruct (skip_ws rest1) as [| c' rest2] eqn:Eskip1;
          [ simpl in *; discriminate
          | simpl in Hparse;
            destruct (Ascii.eqb c' ":"%char) eqn:Ecolon;
            [ simpl in Hparse;
              destruct (parse_value fuel' (skip_ws rest2)) as [[v rest3] |] eqn:Ev;
              [ simpl in Hparse;
                destruct (parse_members_more fuel' (skip_ws rest3)) as [[ms rest4] |] eqn:Emm;
                [ simpl in Hparse;
                  injection Hparse as Hr Hrest; subst res rest;
                  destruct (IHmm (skip_ws rest3) ms rest4 Emm) as [pre Hpre];
                  apply (suffix_compose (c :: w') rest3 rest4);
                  [ apply (suffix_compose (c :: w') rest1 rest3);
                    [ destruct (parse_string_shape (c :: w') s rest1 Es) as [pre1 Hpre1]; exact (existT _ pre1 Hpre1)
                    | apply (suffix_compose rest1 rest2 rest3);
                      [ assert (Hs : ws_part rest1 ++ c' :: rest2 = rest1) by (rewrite <- ws_part_skip; rewrite Eskip1; reflexivity);
                        exists (ws_part rest1 ++ [c']); rewrite <- app_assoc; simpl; exact Hs
                      | apply (suffix_compose rest2 (skip_ws rest2) rest3);
                        [ exact (skip_ws_suffix rest2)
                        | destruct (IHv (skip_ws rest2) v rest3 Ev) as [pre2 Hpre2]; exact (existT _ pre2 Hpre2) ] ] ]
                  | apply (suffix_compose rest3 (skip_ws rest3) rest4); [ exact (skip_ws_suffix rest3) | exact (existT _ pre Hpre) ] ]
                | simpl in *; discriminate ]
              | simpl in *; discriminate ]
            | simpl in *; discriminate ] ]
        | simpl in *; discriminate ] ].
    + (* members_more *)
      destruct w as [| c rest0]; [discriminate |].
      destruct (Ascii.eqb c "}"%char) eqn:Eclose;
      [ apply (Ascii.eqb_eq c "}"%char) in Eclose; subst c; simpl in Hparse;
        injection Hparse as Hr Hrest; subst res rest; exists (@nil ascii); reflexivity
      | destruct (Ascii.eqb c ","%char) eqn:Ecomma; [| discriminate];
        simpl in Hparse;
        destruct (parse_string (skip_ws rest0)) as [[s rest1] |] eqn:Es;
        [ simpl in Hparse;
          destruct (skip_ws rest1) as [| c' rest2] eqn:Eskip1;
          [ simpl in *; discriminate
          | simpl in Hparse;
            destruct (Ascii.eqb c' ":"%char) eqn:Ecolon;
            [ simpl in Hparse;
              destruct (parse_value fuel' (skip_ws rest2)) as [[v rest3] |] eqn:Ev;
              [ simpl in Hparse;
                destruct (parse_members_more fuel' (skip_ws rest3)) as [[ms rest4] |] eqn:Emm;
                [ simpl in Hparse;
                  injection Hparse as Hr Hrest; subst res rest;
                  destruct (IHmm (skip_ws rest3) ms rest4 Emm) as [pre Hpre];
                  apply (suffix_compose (c :: rest0) rest3 rest4);
                  [ apply (suffix_compose (c :: rest0) rest1 rest3);
                    [ apply (suffix_compose (c :: rest0) (skip_ws rest0) rest1);
                      [ apply (suffix_compose (c :: rest0) rest0 (skip_ws rest0));
                        [ exists [c]; reflexivity
                        | exact (skip_ws_suffix rest0) ]
                      | destruct (parse_string_shape (skip_ws rest0) s rest1 Es) as [pre1 Hpre1]; exact (existT _ pre1 Hpre1) ]
                    | apply (suffix_compose rest1 rest2 rest3);
                      [ assert (Hs : ws_part rest1 ++ c' :: rest2 = rest1) by (rewrite <- ws_part_skip; rewrite Eskip1; reflexivity);
                        exists (ws_part rest1 ++ [c']); rewrite <- app_assoc; simpl; exact Hs
                      | apply (suffix_compose rest2 (skip_ws rest2) rest3);
                        [ exact (skip_ws_suffix rest2)
                        | destruct (IHv (skip_ws rest2) v rest3 Ev) as [pre2 Hpre2]; exact (existT _ pre2 Hpre2) ] ] ]
                  | apply (suffix_compose rest3 (skip_ws rest3) rest4); [ exact (skip_ws_suffix rest3) | exact (existT _ pre Hpre) ] ]
                | simpl in *; discriminate ]
              | simpl in *; discriminate ]
            | simpl in *; discriminate ] ]
        | simpl in *; discriminate ] ].
    + (* elements *)
      destruct w as [| c w']; [discriminate |].
      destruct (Ascii.eqb c "]"%char) eqn:Eclose;
      [ apply (Ascii.eqb_eq c "]"%char) in Eclose; subst c; simpl in Hparse;
        injection Hparse as Hr Hrest; subst res rest; exists (@nil ascii); reflexivity
      | simpl in Hparse;
        destruct (parse_value fuel' (c :: w')) as [[v rest0] |] eqn:Ev;
        [ simpl in Hparse;
          destruct (parse_elements_more fuel' (skip_ws rest0)) as [[vs rest1] |] eqn:Eem;
          [ simpl in Hparse;
            injection Hparse as Hr Hrest; subst res rest;
            destruct (IHem (skip_ws rest0) vs rest1 Eem) as [pre Hpre];
            apply (suffix_compose (c :: w') rest0 rest1);
            [ destruct (IHv (c :: w') v rest0 Ev) as [pre1 Hpre1]; exact (existT _ pre1 Hpre1)
            | apply (suffix_compose rest0 (skip_ws rest0) rest1); [ exact (skip_ws_suffix rest0) | exact (existT _ pre Hpre) ] ]
          | simpl in *; discriminate ]
        | simpl in *; discriminate ] ].
    + (* elements_more *)
      destruct w as [| c rest0]; [discriminate |].
      destruct (Ascii.eqb c "]"%char) eqn:Eclose;
      [ apply (Ascii.eqb_eq c "]"%char) in Eclose; subst c; simpl in Hparse;
        injection Hparse as Hr Hrest; subst res rest; exists (@nil ascii); reflexivity
      | destruct (Ascii.eqb c ","%char) eqn:Ecomma; [| discriminate];
        simpl in Hparse;
        destruct (parse_value fuel' (skip_ws rest0)) as [[v rest1] |] eqn:Ev;
        [ simpl in Hparse;
          destruct (parse_elements_more fuel' (skip_ws rest1)) as [[vs rest2] |] eqn:Eem;
          [ simpl in Hparse;
            injection Hparse as Hr Hrest; subst res rest;
            destruct (IHem (skip_ws rest1) vs rest2 Eem) as [pre Hpre];
            apply (suffix_compose (c :: rest0) rest1 rest2);
            [ apply (suffix_compose (c :: rest0) (skip_ws rest0) rest1);
              [ apply (suffix_compose (c :: rest0) rest0 (skip_ws rest0));
                [ exists [c]; reflexivity
                | exact (skip_ws_suffix rest0) ]
              | destruct (IHv (skip_ws rest0) v rest1 Ev) as [pre1 Hpre1]; exact (existT _ pre1 Hpre1) ]
            | apply (suffix_compose rest1 (skip_ws rest1) rest2); [ exact (skip_ws_suffix rest1) | exact (existT _ pre Hpre) ] ]
          | simpl in *; discriminate ]
        | simpl in *; discriminate ] ].
Qed.

(* Mutual soundness of the seven recursive functions, by induction on fuel. *)
Lemma parse_all_sound : forall fuel,
  (forall prefix w v rest, parse_value fuel w = Some (v, rest) ->
      denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt (List.length prefix + List.length w - List.length rest))
  * (forall prefix w ms rest, parse_object fuel w = Some (ms, rest) ->
      denote json_grammar (prefix ++ w) object_body_spec tt (List.length prefix) ms tt (List.length prefix + List.length w - List.length rest))
  * (forall prefix w vs rest, parse_array fuel w = Some (vs, rest) ->
      denote json_grammar (prefix ++ w) array_body_spec tt (List.length prefix) vs tt (List.length prefix + List.length w - List.length rest))
  * (forall prefix w ms rest, parse_members fuel w = Some (ms, rest) ->
      denote json_grammar (prefix ++ w) members_spec tt (List.length prefix) ms tt (List.length prefix + List.length w - List.length rest))
  * (forall prefix w ms rest, parse_members_more fuel w = Some (ms, rest) ->
      denote json_grammar (prefix ++ w) members_rest_spec tt (List.length prefix) ms tt (List.length prefix + List.length w - List.length rest))
  * (forall prefix w vs rest, parse_elements fuel w = Some (vs, rest) ->
      denote json_grammar (prefix ++ w) elements_spec tt (List.length prefix) vs tt (List.length prefix + List.length w - List.length rest))
  * (forall prefix w vs rest, parse_elements_more fuel w = Some (vs, rest) ->
      denote json_grammar (prefix ++ w) elements_rest_spec tt (List.length prefix) vs tt (List.length prefix + List.length w - List.length rest)).
Proof.
  induction fuel as [| fuel' IH]; simpl.
  - repeat split; intros; discriminate.
  - destruct IH as [[[[[[IHv IHo] IHa] IHm] IHmm] IHe] IHem].
    destruct (parse_all_shape fuel') as [[[[[[Sv So] Sa] Sm] Smm] Se] Sem].
    repeat split; intros prefix w res rest Hparse.
    + (* parse_value *)
      destruct w as [| c w']; [discriminate |].
      destruct (Ascii.eqb c "{"%char) eqn:Ebrace.
      * apply (Ascii.eqb_eq c "{"%char) in Ebrace. subst c.
        destruct (parse_object fuel' w') as [[ms rest'] |] eqn:Eobj; [| discriminate].
        injection Hparse as Hres Hrest. subst res rest.
        unfold value_spec. apply d_alt_r. apply d_alt_r. apply d_alt_r. apply d_alt_r.
        apply d_map. apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix)).
        -- apply (char_sound "{"%char prefix w').
        -- replace (prefix ++ "{"%char :: w') with ((prefix ++ ["{"%char]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
           replace (S (List.length prefix)) with (List.length (prefix ++ ["{"%char])) by (rewrite length_app; simpl; lia).
           replace (List.length prefix + List.length ("{"%char :: w') - List.length rest') with (List.length (prefix ++ ["{"%char]) + List.length w' - List.length rest') by (rewrite length_app; simpl; lia).
           apply (IHo (prefix ++ ["{"%char]) w' ms rest' Eobj).
      * destruct (Ascii.eqb c "["%char) eqn:Ebrk.
        -- apply (Ascii.eqb_eq c "["%char) in Ebrk. subst c.
           destruct (parse_array fuel' w') as [[vs rest'] |] eqn:Earr; [| discriminate].
           injection Hparse as Hres Hrest. subst res rest.
           unfold value_spec. apply d_alt_r. apply d_alt_r. apply d_alt_r. apply d_alt_l.
           apply d_map. apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix)).
           ++ apply (char_sound "["%char prefix w').
           ++ replace (prefix ++ "["%char :: w') with ((prefix ++ ["["%char]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
              replace (S (List.length prefix)) with (List.length (prefix ++ ["["%char])) by (rewrite length_app; simpl; lia).
              replace (List.length prefix + List.length ("["%char :: w') - List.length rest') with (List.length (prefix ++ ["["%char]) + List.length w' - List.length rest') by (rewrite length_app; simpl; lia).
              apply (IHa (prefix ++ ["["%char]) w' vs rest' Earr).
        -- destruct (Ascii.eqb c "034"%char) eqn:Equote.
           ++ apply (Ascii.eqb_eq c "034"%char) in Equote. subst c.
              destruct (parse_string ("034"%char :: w')) as [[s rest'] |] eqn:Estr; [| discriminate].
              injection Hparse as Hres Hrest. subst res rest.
              unfold value_spec. apply d_alt_r. apply d_alt_l. apply d_alt_r. apply d_map.
              apply (parse_string_sound prefix ("034"%char :: w') s rest' Estr).
           ++ destruct (Ascii.eqb c "t"%char) eqn:Et.
              -- apply (Ascii.eqb_eq c "t"%char) in Et. subst c.
                 destruct (parse_lit "rue" w') as [rest' |] eqn:Elit; [| discriminate].
                 injection Hparse as Hres Hrest. subst res rest.
                 unfold value_spec. apply d_alt_r. apply d_alt_l. apply d_alt_l. apply d_map.
                 apply d_alt_l. apply d_map with (a := tt).
                 apply d_map with (a := (tt, tt)).
                 apply d_seq with (γ' := tt) (j := S (List.length prefix)).
                 - apply (char_sound "t"%char prefix w').
                 - replace (prefix ++ "t"%char :: w') with ((prefix ++ ["t"%char]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
                   replace (S (List.length prefix)) with (List.length (prefix ++ ["t"%char])) by (rewrite length_app; simpl; lia).
                   replace (List.length prefix + List.length ("t"%char :: w') - List.length rest') with (List.length (prefix ++ ["t"%char]) + List.length w' - List.length rest') by (rewrite length_app; simpl; lia).
                   apply (parse_lit_sound "rue" (prefix ++ ["t"%char]) w' rest' Elit).
              -- destruct (Ascii.eqb c "f"%char) eqn:Ef.
                 ++ apply (Ascii.eqb_eq c "f"%char) in Ef. subst c.
                    destruct (parse_lit "alse" w') as [rest' |] eqn:Elit; [| discriminate].
                    injection Hparse as Hres Hrest. subst res rest.
                    unfold value_spec. apply d_alt_r. apply d_alt_l. apply d_alt_l. apply d_map.
                    apply d_alt_r. apply d_map with (a := tt).
                    apply d_map with (a := (tt, tt)).
                    apply d_seq with (γ' := tt) (j := S (List.length prefix)).
                    - apply (char_sound "f"%char prefix w').
                    - replace (prefix ++ "f"%char :: w') with ((prefix ++ ["f"%char]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
                      replace (S (List.length prefix)) with (List.length (prefix ++ ["f"%char])) by (rewrite length_app; simpl; lia).
                      replace (List.length prefix + List.length ("f"%char :: w') - List.length rest') with (List.length (prefix ++ ["f"%char]) + List.length w' - List.length rest') by (rewrite length_app; simpl; lia).
                      apply (parse_lit_sound "alse" (prefix ++ ["f"%char]) w' rest' Elit).
                 ++ destruct (Ascii.eqb c "n"%char) eqn:En.
                    -- apply (Ascii.eqb_eq c "n"%char) in En. subst c.
                       destruct (parse_lit "ull" w') as [rest' |] eqn:Elit; [| discriminate].
                       injection Hparse as Hres Hrest. subst res rest.
                       unfold value_spec. apply d_alt_l. apply d_map with (a := tt).
                       apply d_map with (a := (tt, tt)).
                       apply d_seq with (γ' := tt) (j := S (List.length prefix)).
                       - apply (char_sound "n"%char prefix w').
                       - replace (prefix ++ "n"%char :: w') with ((prefix ++ ["n"%char]) ++ w') by (rewrite <- app_assoc; simpl; reflexivity).
                         replace (S (List.length prefix)) with (List.length (prefix ++ ["n"%char])) by (rewrite length_app; simpl; lia).
                         replace (List.length prefix + List.length ("n"%char :: w') - List.length rest') with (List.length (prefix ++ ["n"%char]) + List.length w' - List.length rest') by (rewrite length_app; simpl; lia).
                         apply (parse_lit_sound "ull" (prefix ++ ["n"%char]) w' rest' Elit).
                    -- destruct (is_digitb c) eqn:Ed; [| destruct (Ascii.eqb c "-"%char) eqn:Eminus; [| discriminate]].
                       ++ destruct (parse_number (c :: w')) as [[n rest'] |] eqn:Enum; [| discriminate].
                          injection Hparse as Hres Hrest. subst res rest.
                          unfold value_spec. apply d_alt_r. apply d_alt_r. apply d_alt_l. apply d_map.
                          apply (number_sound prefix (c :: w') n rest' Enum).
                       ++ destruct (parse_number (c :: w')) as [[n rest'] |] eqn:Enum; [| discriminate].
                          injection Hparse as Hres Hrest. subst res rest.
                          unfold value_spec. apply d_alt_r. apply d_alt_r. apply d_alt_l. apply d_map.
                          apply (number_sound prefix (c :: w') n rest' Enum).
    + (* parse_object *)
      destruct (parse_members fuel' (skip_ws w)) as [[ms mrest] |] eqn:Emem; [| discriminate].
      destruct (skip_ws mrest) as [| c rem] eqn:Eskip; [discriminate |].
      destruct (Ascii.eqb c "}"%char) eqn:Eclose; [| discriminate].
      apply (Ascii.eqb_eq c "}"%char) in Eclose. subst c.
      injection Hparse as Hres Hrest. subst res rem.
      destruct (Sm (skip_ws w) ms mrest Emem) as [pre Hpre].
      unfold object_body_spec.
      apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (ws_part w)).
      * replace (prefix ++ w) with (prefix ++ w ++ @nil ascii) by (rewrite app_nil_r; reflexivity).
        apply (skip_ws_sound prefix w (@nil ascii)).
      * apply d_bind with (a := ms) (γ' := tt) (j := List.length prefix + List.length w - List.length mrest).
        -- replace (prefix ++ w) with ((prefix ++ ws_part w) ++ skip_ws w) by (rewrite <- app_assoc; rewrite (ws_part_skip w); reflexivity).
           replace (List.length prefix + List.length (ws_part w)) with (List.length (prefix ++ ws_part w)) by (rewrite length_app; reflexivity).
           replace (List.length prefix + List.length w - List.length mrest) with (List.length (prefix ++ ws_part w) + List.length (skip_ws w) - List.length mrest) by (rewrite length_app; pose proof (length_ws_part_skip w) as Hl; lia).
           apply (IHm (prefix ++ ws_part w) (skip_ws w) ms mrest Emem).
        -- replace (prefix ++ w) with ((prefix ++ ws_part w ++ pre) ++ mrest) by (rewrite <- app_assoc; rewrite <- app_assoc; rewrite Hpre; rewrite (ws_part_skip w); reflexivity).
           replace (List.length prefix + List.length w - List.length mrest) with (List.length (prefix ++ ws_part w ++ pre)) by (rewrite !length_app; rewrite (length_ws_part_skip w); rewrite <- Hpre; rewrite length_app; lia).
           replace (List.length prefix + List.length w - List.length rest) with (List.length (prefix ++ ws_part w ++ pre) + List.length mrest - List.length rest) by (rewrite !length_app; rewrite (length_ws_part_skip w); rewrite <- Hpre; rewrite length_app; lia).
           apply (ws_char_pure_sound "}"%char (list (list ascii * Json)) ms (prefix ++ ws_part w ++ pre) mrest rest Eskip).
    + (* parse_array *)
      destruct (parse_elements fuel' (skip_ws w)) as [[vs erest] |] eqn:Eel; [| discriminate].
      destruct (skip_ws erest) as [| c rem] eqn:Eskip; [discriminate |].
      destruct (Ascii.eqb c "]"%char) eqn:Eclose; [| discriminate].
      apply (Ascii.eqb_eq c "]"%char) in Eclose. subst c.
      injection Hparse as Hres Hrest. subst res rem.
      destruct (Se (skip_ws w) vs erest Eel) as [pre Hpre].
      unfold array_body_spec.
      apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (ws_part w)).
      * replace (prefix ++ w) with (prefix ++ w ++ @nil ascii) by (rewrite app_nil_r; reflexivity).
        apply (skip_ws_sound prefix w (@nil ascii)).
      * apply d_bind with (a := vs) (γ' := tt) (j := List.length prefix + List.length w - List.length erest).
        -- replace (prefix ++ w) with ((prefix ++ ws_part w) ++ skip_ws w) by (rewrite <- app_assoc; rewrite (ws_part_skip w); reflexivity).
           replace (List.length prefix + List.length (ws_part w)) with (List.length (prefix ++ ws_part w)) by (rewrite length_app; reflexivity).
           replace (List.length prefix + List.length w - List.length erest) with (List.length (prefix ++ ws_part w) + List.length (skip_ws w) - List.length erest) by (rewrite length_app; pose proof (length_ws_part_skip w) as Hl; lia).
           apply (IHe (prefix ++ ws_part w) (skip_ws w) vs erest Eel).
        -- replace (prefix ++ w) with ((prefix ++ ws_part w ++ pre) ++ erest) by (rewrite <- app_assoc; rewrite <- app_assoc; rewrite Hpre; rewrite (ws_part_skip w); reflexivity).
           replace (List.length prefix + List.length w - List.length erest) with (List.length (prefix ++ ws_part w ++ pre)) by (rewrite !length_app; rewrite (length_ws_part_skip w); rewrite <- Hpre; rewrite length_app; lia).
           replace (List.length prefix + List.length w - List.length rest) with (List.length (prefix ++ ws_part w ++ pre) + List.length erest - List.length rest) by (rewrite !length_app; rewrite (length_ws_part_skip w); rewrite <- Hpre; rewrite length_app; lia).
           apply (ws_char_pure_sound "]"%char (list Json) vs (prefix ++ ws_part w ++ pre) erest rest Eskip).
    + (* parse_members *)
      destruct w as [| c w']; [discriminate |].
      destruct (Ascii.eqb c "}"%char) eqn:Eclose.
      * apply (Ascii.eqb_eq c "}"%char) in Eclose. subst c.
        injection Hparse as Hres Hrest. subst res rest.
        unfold members_spec. apply d_alt_l.
        replace (List.length prefix + List.length ("}"%char :: w') - List.length ("}"%char :: w')) with (List.length prefix) by (simpl; lia).
        apply d_pure.
      * destruct (parse_string (c :: w')) as [[s rest1] |] eqn:Es; [| simpl in *; discriminate].
        destruct (skip_ws rest1) as [| c' rest2] eqn:Eskip1; [simpl in *; discriminate |].
        destruct (Ascii.eqb c' ":"%char) eqn:Ecolon; [| simpl in *; discriminate].
        apply (Ascii.eqb_eq c' ":"%char) in Ecolon. subst c'.
        assert (Hl : List.length rest1 = List.length (ws_part rest1) + 1 + List.length rest2) by (rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite length_app; simpl; lia).
        destruct (parse_value fuel' (skip_ws rest2)) as [[v rest3] |] eqn:Ev; [| simpl in *; discriminate].
        destruct (parse_members_more fuel' (skip_ws rest3)) as [[ms rest4] |] eqn:Emm; [| simpl in *; discriminate].
        simpl in Hparse.
        injection Hparse as Hres Hrest. subst res rest.
        destruct (parse_string_shape (c :: w') s rest1 Es) as [p1 Hp1].
        destruct (Sv (skip_ws rest2) v rest3 Ev) as [X HX].
        unfold members_spec. apply d_alt_r.
        apply d_bind with (a := (s, v)) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest3).
        -- (* member_spec *)
           unfold member_spec.
           apply d_bind with (a := s) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest1).
           ++ apply (parse_string_sound prefix (c :: w') s rest1 Es).
           ++ apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest1 + List.length (ws_part rest1)).
              replace (List.length prefix + List.length (c :: w')) with (List.length (prefix ++ (c :: w'))) by (rewrite length_app; reflexivity).
              apply (skip_ws_mid_sound (prefix ++ (c :: w')) rest1).
              exists (prefix ++ p1). rewrite <- Hp1. rewrite <- !app_assoc. reflexivity.
              apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest1 + List.length (ws_part rest1) + 1).
              ++ assert (Heq : prefix ++ (c :: w') = (prefix ++ p1 ++ ws_part rest1) ++ ":"%char :: rest2) by (rewrite <- Hp1; rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite !app_assoc; reflexivity).
                 rewrite Heq.
                 replace (List.length prefix + List.length (c :: w') - List.length rest1 + List.length (ws_part rest1)) with (List.length (prefix ++ p1 ++ ws_part rest1)) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; lia).
                 replace (List.length (prefix ++ p1 ++ ws_part rest1) + 1) with (S (List.length (prefix ++ p1 ++ ws_part rest1))) by lia.
                 apply (char_sound ":"%char (prefix ++ p1 ++ ws_part rest1) rest2).
              ++ apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest1 + List.length (ws_part rest1) + 1 + List.length (ws_part rest2)).
                 replace (List.length prefix + List.length (c :: w')) with (List.length (prefix ++ (c :: w'))) by (rewrite length_app; reflexivity).
                 replace (List.length (prefix ++ (c :: w')) - List.length rest1 + List.length (ws_part rest1) + 1) with (List.length (prefix ++ (c :: w')) - List.length rest2) by (assert (Hle : List.length rest1 <= List.length (prefix ++ c :: w')) by (rewrite <- Hp1; rewrite !length_app; lia); lia).
                 apply (skip_ws_mid_sound (prefix ++ (c :: w')) rest2).
                 exists (prefix ++ p1 ++ ws_part rest1 ++ [":"%char]).
                 rewrite <- Hp1. rewrite <- (ws_part_skip rest1) at 2. rewrite Eskip1. rewrite <- !app_assoc. simpl. reflexivity.
                 assert (Heq2 : prefix ++ (c :: w') = (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) ++ skip_ws rest2) by (rewrite <- Hp1; rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite <- !app_assoc; simpl; rewrite (ws_part_skip rest2); reflexivity).
                 rewrite Heq2.
                 replace (List.length prefix + List.length (c :: w') - List.length rest1 + List.length (ws_part rest1) + 1 + List.length (ws_part rest2)) with (List.length (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2)) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; simpl; rewrite Hl; lia).
                 replace (List.length prefix + List.length (c :: w') - List.length rest3) with (List.length (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) + List.length (skip_ws rest2) - List.length rest3) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; simpl; pose proof (length_ws_part_skip rest2) as Hl2; lia).
                 apply d_map with (a := v). apply d_call. cbn [json_grammar]. apply (IHv (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) (skip_ws rest2) v rest3 Ev).
        -- apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest3 + List.length (ws_part rest3)).
           replace (List.length prefix + List.length (c :: w')) with (List.length (prefix ++ (c :: w'))) by (rewrite length_app; reflexivity).
           apply (skip_ws_mid_sound (prefix ++ (c :: w')) rest3).
           exists (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X).
           symmetry. rewrite <- Hp1. rewrite <- (ws_part_skip rest1) at 1. rewrite Eskip1. rewrite <- (ws_part_skip rest2) at 1. rewrite <- HX. rewrite <- !app_assoc. simpl. reflexivity.
           assert (Heq3 : prefix ++ (c :: w') = (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3) ++ skip_ws rest3) by (rewrite <- Hp1; rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite <- (ws_part_skip rest2) at 1; rewrite <- HX; rewrite <- (ws_part_skip rest3) at 1; rewrite <- !app_assoc; simpl; reflexivity).
           rewrite Heq3.
           replace (List.length prefix + List.length (c :: w') - List.length rest3 + List.length (ws_part rest3)) with (List.length (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3)) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; rewrite Hl; rewrite (length_ws_part_skip rest2); rewrite <- HX; rewrite length_app; simpl; lia).
           replace (List.length prefix + List.length (c :: w') - List.length rest4) with (List.length (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3) + List.length (skip_ws rest3) - List.length rest4) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; rewrite Hl; rewrite (length_ws_part_skip rest2); rewrite <- HX; rewrite length_app; simpl; pose proof (length_ws_part_skip rest3) as Hl3; lia).
           apply d_map. apply (IHmm (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3) (skip_ws rest3) ms rest4 Emm).
    + (* parse_members_more *)
      destruct w as [| c rest0]; [discriminate |].
      destruct (Ascii.eqb c "}"%char) eqn:Eclose.
      * apply (Ascii.eqb_eq c "}"%char) in Eclose. subst c. simpl in Hparse.
        injection Hparse as Hr Hrest. subst res rest.
        unfold members_rest_spec.
        replace (List.length prefix + List.length ("}"%char :: rest0) - List.length ("}"%char :: rest0)) with (List.length prefix) by (simpl; lia).
        apply d_many_nil.
      * destruct (Ascii.eqb c ","%char) eqn:Ecomma; [| simpl in *; discriminate].
        apply (Ascii.eqb_eq c ","%char) in Ecomma. subst c.
        destruct (parse_string (skip_ws rest0)) as [[s rest1] |] eqn:Es; [| simpl in *; discriminate].
        destruct (skip_ws rest1) as [| c' rest2] eqn:Eskip1; [simpl in *; discriminate |].
        destruct (Ascii.eqb c' ":"%char) eqn:Ecolon; [| simpl in *; discriminate].
        apply (Ascii.eqb_eq c' ":"%char) in Ecolon. subst c'.
        assert (Hl : List.length rest1 = List.length (ws_part rest1) + 1 + List.length rest2) by (rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite length_app; simpl; lia).
        destruct (parse_value fuel' (skip_ws rest2)) as [[v rest3] |] eqn:Ev; [| simpl in *; discriminate].
        destruct (parse_members_more fuel' (skip_ws rest3)) as [[ms rest4] |] eqn:Emm; [| simpl in *; discriminate].
        simpl in Hparse.
        injection Hparse as Hr Hrest. subst res rest.
        destruct (parse_string_shape (skip_ws rest0) s rest1 Es) as [p1 Hp1].
        destruct (Sv (skip_ws rest2) v rest3 Ev) as [X HX].
        assert (HleR3 : List.length rest3 <= List.length (skip_ws rest0)) by (assert (H1 : List.length rest3 <= List.length (skip_ws rest2)) by (rewrite <- HX; rewrite length_app; lia); assert (H2 : List.length (skip_ws rest2) <= List.length rest2) by (pose proof (length_ws_part_skip rest2) as Hl2; lia); assert (H3 : List.length rest2 <= List.length (skip_ws rest0)) by (rewrite <- Hp1; rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite !length_app; simpl; lia); lia).
        unfold members_rest_spec.
        apply d_many_cons with (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest3) + List.length (ws_part rest3)).
        apply d_map with (a := (tt, (s, v))).
        apply d_seq with (γ' := tt) (j := S (List.length prefix)).
        -- apply (char_sound ","%char prefix rest0).
        -- apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0)).
           ++ replace (S (List.length prefix)) with (List.length (prefix ++ ","%char :: rest0) - List.length rest0) by (rewrite !length_app; simpl; lia).
              apply (skip_ws_mid_sound (prefix ++ (","%char :: rest0)) rest0).
              exists (prefix ++ [","%char]). rewrite <- app_assoc. simpl. reflexivity.
           ++ apply d_bind with (a := (s, v)) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest3)).
              -- (* member_spec *)
                 unfold member_spec.
                 apply d_bind with (a := s) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)).
                 ++ replace (prefix ++ (","%char :: rest0)) with ((prefix ++ [","%char] ++ ws_part rest0) ++ skip_ws rest0) by (rewrite <- !app_assoc; rewrite ws_part_skip; reflexivity).
                    replace (S (List.length prefix) + List.length (ws_part rest0)) with (List.length (prefix ++ [","%char] ++ ws_part rest0)) by (rewrite !length_app; simpl; lia).
                    replace (List.length (prefix ++ (","%char :: rest0)) - List.length rest1) with (List.length (prefix ++ [","%char] ++ ws_part rest0) + List.length (skip_ws rest0) - List.length rest1) by (rewrite !length_app; simpl; pose proof (length_ws_part_skip rest0) as Hl0; lia).
                    replace (List.length (prefix ++ [","%char] ++ ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)) with (List.length (prefix ++ [","%char] ++ ws_part rest0) + List.length (skip_ws rest0) - List.length rest1) by (assert (Hle : List.length rest1 <= List.length (skip_ws rest0)) by (rewrite <- Hp1; rewrite length_app; lia); lia).
                    apply (parse_string_sound (prefix ++ [","%char] ++ ws_part rest0) (skip_ws rest0) s rest1 Es).
                 ++ apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)).
                    replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)) with (List.length (prefix ++ (","%char :: rest0)) - List.length rest1) by (rewrite !length_app; simpl; pose proof (length_ws_part_skip rest0) as Hl0; assert (Hle : List.length rest1 <= List.length (skip_ws rest0)) by (rewrite <- Hp1; rewrite length_app; lia); lia).
                    apply (skip_ws_mid_sound (prefix ++ (","%char :: rest0)) rest1).
                    exists (prefix ++ [","%char] ++ ws_part rest0 ++ p1).
                    rewrite <- !app_assoc. rewrite Hp1. rewrite (ws_part_skip rest0). simpl. reflexivity.
                    -- apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1) + 1).
                       ++ replace (prefix ++ (","%char :: rest0)) with ((prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1) ++ ":"%char :: rest2) by (symmetry; rewrite <- !app_assoc; rewrite <- Eskip1; rewrite (ws_part_skip rest1); rewrite Hp1; rewrite (ws_part_skip rest0); simpl; reflexivity).
                          replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)) with (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1)) by (rewrite !length_app; simpl; rewrite <- Hp1; rewrite length_app; simpl; lia).
                          replace (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1) + 1) with (S (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1))) by lia.
                          apply (char_sound ":"%char (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1) rest2).
                       ++ apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1) + 1 + List.length (ws_part rest2)).
                          replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1) + 1) with (List.length (prefix ++ (","%char :: rest0)) - List.length rest2) by (rewrite !length_app; simpl; assert (Hp1l : List.length (skip_ws rest0) = List.length p1 + List.length rest1) by (rewrite <- Hp1; rewrite length_app; reflexivity); assert (Hl0 := length_ws_part_skip rest0); lia).
                          apply (skip_ws_mid_sound (prefix ++ (","%char :: rest0)) rest2).
                          exists (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char]).
                          rewrite <- !app_assoc. simpl. rewrite <- Eskip1. rewrite (ws_part_skip rest1). rewrite Hp1. rewrite (ws_part_skip rest0). simpl. reflexivity.
                          -- apply d_map. apply d_call. cbn [json_grammar].
                             assert (Heq : prefix ++ (","%char :: rest0) = (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) ++ skip_ws rest2) by (symmetry; rewrite <- !app_assoc; rewrite (ws_part_skip rest2); simpl; rewrite <- Eskip1; rewrite (ws_part_skip rest1); rewrite Hp1; rewrite (ws_part_skip rest0); simpl; reflexivity).
                             rewrite Heq.
                             replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1) + 1 + List.length (ws_part rest2)) with (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2)) by (rewrite !length_app; simpl; assert (Hp1l : List.length (skip_ws rest0) = List.length p1 + List.length rest1) by (rewrite <- Hp1; rewrite length_app; reflexivity); lia).
                             replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest3)) with (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) + List.length (skip_ws rest2) - List.length rest3) by (rewrite !length_app; simpl; assert (Hp1l : List.length (skip_ws rest0) = List.length p1 + List.length rest1) by (rewrite <- Hp1; rewrite length_app; reflexivity); assert (Hle : List.length rest3 <= List.length (skip_ws rest2)) by (rewrite <- HX; rewrite length_app; lia); pose proof (length_ws_part_skip rest2) as Hl2; lia).
                             apply (IHv (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) (skip_ws rest2) v rest3 Ev).
              -- (* ws before recursion, then IHmm *)
                 apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest3) + List.length (ws_part rest3)).
                 replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest3)) with (List.length (prefix ++ (","%char :: rest0)) - List.length rest3) by (rewrite !length_app; simpl; pose proof (length_ws_part_skip rest0) as Hl0; lia).
                 apply (skip_ws_mid_sound (prefix ++ (","%char :: rest0)) rest3).
                    exists (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X).
                    rewrite <- !app_assoc. simpl. rewrite HX. rewrite (ws_part_skip rest2). rewrite <- Eskip1. rewrite (ws_part_skip rest1). rewrite Hp1. rewrite (ws_part_skip rest0). simpl. reflexivity.
                 ++ apply d_pure.
                 replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest3) + List.length (ws_part rest3)) with (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3)) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; rewrite Hl; rewrite (length_ws_part_skip rest2); rewrite <- HX; rewrite length_app; simpl; lia).
                 replace (List.length prefix + List.length (","%char :: rest0) - List.length rest4) with (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3) + List.length (skip_ws rest3) - List.length rest4) by (rewrite !length_app; simpl; assert (Hp1l : List.length (skip_ws rest0) = List.length p1 + List.length rest1) by (rewrite <- Hp1; rewrite length_app; reflexivity); assert (HXl : List.length (skip_ws rest2) = List.length X + List.length rest3) by (rewrite <- HX; rewrite length_app; reflexivity); pose proof (length_ws_part_skip rest0) as Hl0; pose proof (length_ws_part_skip rest2) as Hl2; pose proof (length_ws_part_skip rest3) as Hl3; lia).
                 assert (Heq : prefix ++ (","%char :: rest0) = (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3) ++ skip_ws rest3) by (symmetry; rewrite <- !app_assoc; rewrite (ws_part_skip rest3); rewrite HX; rewrite (ws_part_skip rest2); simpl; rewrite <- Eskip1; rewrite (ws_part_skip rest1); rewrite Hp1; rewrite (ws_part_skip rest0); simpl; reflexivity).
                 rewrite Heq.
                 apply (IHmm (prefix ++ [","%char] ++ ws_part rest0 ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2 ++ X ++ ws_part rest3) (skip_ws rest3) ms rest4 Emm).
    + (* parse_elements *)
      destruct w as [| c w']; [discriminate |].
      destruct (Ascii.eqb c "]"%char) eqn:Eclose.
      * apply (Ascii.eqb_eq c "]"%char) in Eclose. subst c. simpl in Hparse.
        injection Hparse as Hr Hrest. subst res rest.
        unfold elements_spec. apply d_alt_l.
        replace (List.length prefix + List.length ("]"%char :: w') - List.length ("]"%char :: w')) with (List.length prefix) by (simpl; lia).
        apply d_pure.
      * destruct (parse_value fuel' (c :: w')) as [[v rest0] |] eqn:Ev; [| simpl in *; discriminate].
        destruct (parse_elements_more fuel' (skip_ws rest0)) as [[vs rest1] |] eqn:Eem; [| simpl in *; discriminate].
        simpl in Hparse.
        injection Hparse as Hr Hrest. subst res rest.
        destruct (Sv (c :: w') v rest0 Ev) as [X HX].
        unfold elements_spec. apply d_alt_r.
        apply d_bind with (a := v) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest0).
        -- apply d_call. cbn [json_grammar]. apply (IHv prefix (c :: w') v rest0 Ev).
        -- apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length (c :: w') - List.length rest0 + List.length (ws_part rest0)).
           ++ replace (List.length prefix + List.length (c :: w') - List.length rest0) with (List.length (prefix ++ (c :: w')) - List.length rest0) by (rewrite length_app; reflexivity).
              apply (skip_ws_mid_sound (prefix ++ (c :: w')) rest0).
              exists (prefix ++ X). rewrite <- HX. rewrite <- !app_assoc. reflexivity.
           ++ replace (prefix ++ (c :: w')) with ((prefix ++ X ++ ws_part rest0) ++ skip_ws rest0) by (rewrite <- HX; rewrite <- !app_assoc; rewrite (ws_part_skip rest0); reflexivity).
              replace (List.length prefix + List.length (c :: w') - List.length rest0 + List.length (ws_part rest0)) with (List.length (prefix ++ X ++ ws_part rest0)) by (rewrite !length_app; assert (HXl : List.length X + List.length rest0 = List.length (c :: w')) by (rewrite <- HX; rewrite length_app; reflexivity); lia).
              replace (List.length prefix + List.length (c :: w') - List.length rest1) with (List.length (prefix ++ X ++ ws_part rest0) + List.length (skip_ws rest0) - List.length rest1) by (rewrite !length_app; assert (HXl : List.length X + List.length rest0 = List.length (c :: w')) by (rewrite <- HX; rewrite length_app; reflexivity); pose proof (length_ws_part_skip rest0) as Hl0; assert (Hle : List.length rest1 <= List.length (skip_ws rest0)) by (destruct (Sem (skip_ws rest0) vs rest1 Eem) as [pre Hpre]; rewrite <- Hpre; rewrite length_app; lia); lia).
              apply d_map. apply (IHem (prefix ++ X ++ ws_part rest0) (skip_ws rest0) vs rest1 Eem).
    + (* parse_elements_more *)
      destruct w as [| c rest0]; [discriminate |].
      destruct (Ascii.eqb c "]"%char) eqn:Eclose.
      * apply (Ascii.eqb_eq c "]"%char) in Eclose. subst c. simpl in Hparse.
        injection Hparse as Hr Hrest. subst res rest.
        unfold elements_rest_spec.
        replace (List.length prefix + List.length ("]"%char :: rest0) - List.length ("]"%char :: rest0)) with (List.length prefix) by (simpl; lia).
        apply d_many_nil.
      * destruct (Ascii.eqb c ","%char) eqn:Ecomma; [| simpl in *; discriminate].
        apply (Ascii.eqb_eq c ","%char) in Ecomma. subst c.
        destruct (parse_value fuel' (skip_ws rest0)) as [[v rest1] |] eqn:Ev; [| simpl in *; discriminate].
        destruct (parse_elements_more fuel' (skip_ws rest1)) as [[vs rest2] |] eqn:Eem; [| simpl in *; discriminate].
        simpl in Hparse.
        injection Hparse as Hr Hrest. subst res rest.
        destruct (Sv (skip_ws rest0) v rest1 Ev) as [X HX].
        unfold elements_rest_spec.
        apply d_many_cons with (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)).
        apply d_map with (a := (tt, v)).
        apply d_seq with (γ' := tt) (j := S (List.length prefix)).
        -- apply (char_sound ","%char prefix rest0).
        -- apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0)).
           ++ replace (S (List.length prefix)) with (List.length (prefix ++ ","%char :: rest0) - List.length rest0) by (rewrite !length_app; simpl; lia).
              apply (skip_ws_mid_sound (prefix ++ (","%char :: rest0)) rest0).
              exists (prefix ++ [","%char]). rewrite <- app_assoc. simpl. reflexivity.
           ++ apply d_bind with (a := v) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)).
              -- apply d_call. cbn [json_grammar].
                 replace (prefix ++ (","%char :: rest0)) with ((prefix ++ [","%char] ++ ws_part rest0) ++ skip_ws rest0) by (rewrite <- !app_assoc; rewrite ws_part_skip; reflexivity).
                 replace (S (List.length prefix) + List.length (ws_part rest0)) with (List.length (prefix ++ [","%char] ++ ws_part rest0)) by (rewrite !length_app; simpl; lia).
                 replace (List.length (prefix ++ [","%char] ++ ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)) with (List.length (prefix ++ [","%char] ++ ws_part rest0) + List.length (skip_ws rest0) - List.length rest1) by (assert (Hle : List.length rest1 <= List.length (skip_ws rest0)) by (rewrite <- HX; rewrite length_app; lia); lia).
                 apply (IHv (prefix ++ [","%char] ++ ws_part rest0) (skip_ws rest0) v rest1 Ev).
              -- apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)).
                 ++ replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)) with (List.length (prefix ++ (","%char :: rest0)) - List.length rest1) by (rewrite !length_app; simpl; pose proof (length_ws_part_skip rest0) as Hl0; assert (Hle : List.length rest1 <= List.length (skip_ws rest0)) by (rewrite <- HX; rewrite length_app; lia); lia).
                    apply (skip_ws_mid_sound (prefix ++ (","%char :: rest0)) rest1).
                    exists (prefix ++ [","%char] ++ ws_part rest0 ++ X).
                    rewrite <- !app_assoc. rewrite HX. rewrite (ws_part_skip rest0). simpl. reflexivity.
                 ++ apply d_pure.
                 ++ replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)) with (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ X ++ ws_part rest1)) by (rewrite !length_app; rewrite <- HX; rewrite length_app; simpl; lia).
                    replace (List.length prefix + List.length (","%char :: rest0) - List.length rest2) with (List.length (prefix ++ [","%char] ++ ws_part rest0 ++ X ++ ws_part rest1) + List.length (skip_ws rest1) - List.length rest2) by (rewrite !length_app; simpl; assert (HXl : List.length X + List.length rest1 = List.length (skip_ws rest0)) by (rewrite <- HX; rewrite length_app; reflexivity); pose proof (length_ws_part_skip rest0) as Hl0; pose proof (length_ws_part_skip rest1) as Hl1; assert (Hle : List.length rest2 <= List.length (skip_ws rest1)) by (destruct (Sem (skip_ws rest1) vs rest2 Eem) as [pre Hpre]; rewrite <- Hpre; rewrite length_app; lia); lia).
                    assert (Heq : prefix ++ (","%char :: rest0) = (prefix ++ [","%char] ++ ws_part rest0 ++ X ++ ws_part rest1) ++ skip_ws rest1) by (rewrite <- !app_assoc; rewrite (ws_part_skip rest1); rewrite HX; rewrite (ws_part_skip rest0); simpl; reflexivity).
                    rewrite Heq.
                    apply (IHem (prefix ++ [","%char] ++ ws_part rest0 ++ X ++ ws_part rest1) (skip_ws rest1) vs rest2 Eem).
Qed.
(* Whole-document soundness. *)
Lemma parse_json_sound (w : list ascii) (v : Json) :
  parse_json w = Some v ->
  denote json_grammar w json_text tt 0 v tt (List.length w).
Proof.
  intros H.
  unfold parse_json in H.
  destruct (parse_value (S (S (List.length w))) (skip_ws w)) as [[v' rest] |] eqn:Ev; [| discriminate].
  destruct (skip_ws rest) as [| c tl] eqn:Eskip; [| discriminate].
  injection H as Hv. subst v.
  assert (Hws : ws_part rest = rest) by (symmetry; rewrite <- (ws_part_skip rest) at 1; rewrite Eskip; apply app_nil_r).
  destruct (parse_all_shape (S (S (List.length w)))) as [[[[[[Sv _] _] _] _] _] _].
  destruct (Sv (skip_ws w) v' rest Ev) as [pre Hpre].
  destruct (parse_all_sound (S (S (List.length w)))) as [[[[[[IHv _] _] _] _] _] _].
  unfold json_text.
  apply d_bind with (a := tt) (γ' := tt) (j := List.length (ws_part w)).
  ++ replace 0 with (List.length w - List.length w) by lia.
     replace (List.length (ws_part w)) with (List.length w - List.length w + List.length (ws_part w)) by lia.
     apply (skip_ws_mid_sound w w).
     exists (@nil ascii). reflexivity.
  ++ apply d_bind with (a := v') (γ' := tt) (j := List.length (ws_part w) + List.length (skip_ws w) - List.length rest).
     -- apply d_call. cbn [json_grammar].
        exact (eq_rect (ws_part w ++ skip_ws w) (fun x : list ascii => denote json_grammar x value_spec tt (Datatypes.length (ws_part w)) v' tt (Datatypes.length (ws_part w) + Datatypes.length (skip_ws w) - Datatypes.length rest)) (IHv (ws_part w) (skip_ws w) v' rest Ev) w (ws_part_skip w)).
     -- apply d_bind with (a := tt) (γ' := tt) (j := List.length (ws_part w) + List.length (skip_ws w) - List.length rest + List.length (ws_part rest)).
        ++ replace (List.length (ws_part w) + List.length (skip_ws w) - List.length rest) with (List.length w - List.length rest) by (rewrite (length_ws_part_skip w); lia).
           apply (skip_ws_mid_sound w rest).
           exists (ws_part w ++ pre).
           rewrite <- !app_assoc. rewrite Hpre. apply ws_part_skip.
        ++ replace (List.length (ws_part w) + List.length (skip_ws w) - List.length rest + List.length (ws_part rest)) with (List.length w) by (pose proof (length_ws_part_skip w) as Hl; rewrite Hws; assert (Hle : List.length rest <= List.length (skip_ws w)) by (rewrite <- Hpre; rewrite length_app; lia); lia).
           apply d_pure.
Qed.

(* ------------------------------------------------------------------------- *)
(* 12. Extraction: the parser compiles to OCaml                                *)
(* ------------------------------------------------------------------------- *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlNatBigInt ExtrOcamlZBigInt ExtrOcamlChar.
(* nat and Z both extract to Big_int_Z.big_int (= Zarith Z.t), so of_nat is
   the identity. Without this the default of_nat recurses on the numeric value. *)
Extract Constant Z.of_nat => "(fun n -> n)".
Extraction Language OCaml.
Extraction "json.ml" parse_json.
