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
From Coq.Program Require Import Equality.

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
(* Generic tail-recursive repetition loop (worker/wrapper).
   `sep_by` is the natural recursion; `sep_by_loop` is the tail-recursive
   accumulator version that extracts to a loop.  Both parse `*( sep ws elem ws )`
   followed by the `closer` char (consumed by the caller), e.g. `}` for members,
   `]` for elements.  The loop accumulates the parsed elements reversed and
   un-reverses them at the closer. *)
Section SepBy.
  Variable A : Type.
  Variable elem : nat -> list ascii -> option (A * list ascii).
  Variable sep closer : ascii.

  Fixpoint sep_by (fuel : nat) (w : list ascii) : option (list A * list ascii) :=
    match fuel with
    | O => None
    | S fuel' =>
        match w with
        | [] => None
        | c :: rest =>
            if Ascii.eqb c closer then Some (@nil A, w)
            else if Ascii.eqb c sep then
              match elem fuel' (skip_ws rest) with
              | None => None
              | Some (a, rest2) =>
                  match sep_by fuel' (skip_ws rest2) with
                  | None => None
                  | Some (xs, rest3) => Some (a :: xs, rest3)
                  end
              end
            else None
        end
    end.

  Fixpoint sep_by_loop (fuel : nat) (acc : list A) (w : list ascii) : option (list A * list ascii) :=
    match fuel with
    | O => None
    | S fuel' =>
        match w with
        | [] => None
        | c :: rest =>
            if Ascii.eqb c closer then Some (rev_append acc (@nil A), w)
            else if Ascii.eqb c sep then
              match elem fuel' (skip_ws rest) with
              | None => None
              | Some (a, rest2) => sep_by_loop fuel' (a :: acc) (skip_ws rest2)
              end
            else None
        end
    end.

  Lemma sep_by_loop_equiv : forall (fuel : nat) (acc : list A) (w : list ascii),
    sep_by_loop fuel acc w =
    match sep_by fuel w with
    | None => None
    | Some (xs, rest) => Some (rev_append acc xs, rest)
    end.
  Proof.
    intros fuel acc w. revert acc w.
    induction fuel as [| fuel' IH]; intros acc w; simpl.
    - reflexivity.
    - destruct w as [| c rest]; [reflexivity |].
      destruct (Ascii.eqb c closer) eqn:Ecl; [reflexivity |].
      destruct (Ascii.eqb c sep) eqn:Esep; [| reflexivity].
      destruct (elem fuel' (skip_ws rest)) as [e |] eqn:Ee; [| reflexivity].
      destruct e as [a rest2].
      rewrite IH.
      destruct (sep_by fuel' (skip_ws rest2)) as [es |] eqn:Es; [| reflexivity].
      destruct es as [xs rest3]. reflexivity.
  Qed.
  Hypothesis elem_mono : forall (fuel fuel' : nat) (w : list ascii) (r : A * list ascii),
    fuel <= fuel' -> elem fuel w = Some r -> elem fuel' w = Some r.

  Lemma sep_by_mono (fuel fuel' : nat) (w : list ascii) (r : list A * list ascii) :
    fuel <= fuel' -> sep_by fuel w = Some r -> sep_by fuel' w = Some r.
  Proof.
    revert w r fuel'.
    induction fuel as [| f IH]; intros w r fuel' Hle H.
    { cbn [sep_by] in H. discriminate. }
    destruct fuel' as [| f']; [lia |].
    assert (Hle' : f <= f') by lia.
    cbn [sep_by] in H.
    destruct w as [| c rest]; cbn [sep_by] in H; try discriminate.
    cbn [sep_by].
    destruct (Ascii.eqb c closer) eqn:E1.
    + exact H.
    + destruct (Ascii.eqb c sep) eqn:E2.
      * destruct (elem f (skip_ws rest)) as [[a rest2] |] eqn:Ee; try discriminate.
        rewrite (elem_mono f f' (skip_ws rest) (a, rest2) Hle' Ee).
        destruct (sep_by f (skip_ws rest2)) as [[xs rest3] |] eqn:Es; try discriminate.
        rewrite (IH (skip_ws rest2) (xs, rest3) f' Hle' Es). cbn. exact H.
      * discriminate.
  Qed.

End SepBy.

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
(* One member: string ws ":" ws value.  The input `w` is already ws-skipped by
   the caller (`sep_by` passes `skip_ws rest`). *)
Definition parse_member (fuel : nat) (w : list ascii) : option ((list ascii * Json) * list ascii) :=
  match parse_string w with
  | None => None
  | Some (s, rest1) =>
      match skip_ws rest1 with
      | c' :: rest2 =>
          if Ascii.eqb c' ":"%char then
            match parse_value fuel (skip_ws rest2) with
            | Some (v, rest3) => Some ((s, v), rest3)
            | None => None
            end
          else None
      | [] => None
      end
  end.


(* Whole-document parse: skip leading ws, parse one value, require trailing
   whitespace only. *)
Definition parse_json (w : list ascii) : option Json :=
  match parse_value (3 * List.length w + 2) (skip_ws w) with
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
(* The generic loop leaves a suffix of its input. *)
Lemma sep_by_shape (A : Type) (elem_parser : nat -> list ascii -> option (A * list ascii)) (sep closer : ascii) :
  (forall (fuel : nat) (w : list ascii) (a : A) (rest : list ascii),
     elem_parser fuel w = Some (a, rest) -> { pre : list ascii & pre ++ rest = w }) ->
  forall (fuel : nat) (w : list ascii) (xs : list A) (rest : list ascii),
    sep_by A elem_parser sep closer fuel w = Some (xs, rest) -> { pre : list ascii & pre ++ rest = w }.
Proof.
  intros Helem_shape.
  induction fuel as [| f IH]; intros w xs rest H.
  - cbn [sep_by] in H. discriminate.
  - cbn [sep_by] in H.
    destruct w as [| c rest0]; [discriminate |].
    destruct (Ascii.eqb c closer) eqn:Eclose.
    + apply (Ascii.eqb_eq c closer) in Eclose. subst c.
      simpl in H. injection H as Hxs Hrest. subst xs rest.
      exists (@nil ascii). reflexivity.
    + destruct (Ascii.eqb c sep) eqn:Esep; [| simpl in *; discriminate].
      apply (Ascii.eqb_eq c sep) in Esep. subst c.
      destruct (elem_parser f (skip_ws rest0)) as [[a rest1] |] eqn:Ee; [| simpl in *; discriminate].
      destruct (sep_by A elem_parser sep closer f (skip_ws rest1)) as [[xs' rest2] |] eqn:Es; [| simpl in *; discriminate].
      simpl in H. injection H as Hxs Hrest. subst xs rest.
      destruct (Helem_shape f (skip_ws rest0) a rest1 Ee) as [X HX].
      destruct (IH (skip_ws rest1) xs' rest2 Es) as [Y HY].
      apply (suffix_compose (sep :: rest0) rest1 rest2).
      + apply (suffix_compose (sep :: rest0) (skip_ws rest0) rest1).
        * apply (suffix_compose (sep :: rest0) rest0 (skip_ws rest0)).
          -- exists [sep]. reflexivity.
          -- exact (skip_ws_suffix rest0).
        * exact (existT _ X HX).
      + apply (suffix_compose rest1 (skip_ws rest1) rest2).
        * exact (skip_ws_suffix rest1).
        * exact (existT _ Y HY).
Qed.


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

(* The generic loop is sound for `Many (Map snd (Seq (char sep) (Bind ws
   (Bind elem (Bind ws (Pure))))))`. Instantiated alongside `sep_by_complete`. *)
Lemma sep_by_sound (A : Type) (elem : Spec ascii unit json_nt A)
  (elem_parser : nat -> list ascii -> option (A * list ascii)) (sep closer : ascii) :
  forall (fuel : nat),
    (forall (fuel' : nat), fuel' < fuel -> forall (prefix w : list ascii) (a : A) (rest : list ascii),
       elem_parser fuel' w = Some (a, rest) ->
       denote json_grammar (prefix ++ w) elem tt (List.length prefix) a tt (List.length prefix + List.length w - List.length rest)) ->
    (forall (fuel : nat) (w : list ascii) (a : A) (rest : list ascii),
       elem_parser fuel w = Some (a, rest) -> { pre : list ascii & pre ++ rest = w }) ->
    forall (prefix w : list ascii) (xs : list A) (rest : list ascii),
      sep_by A elem_parser sep closer fuel w = Some (xs, rest) ->
      denote json_grammar (prefix ++ w)
        (Many (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a : A => Bind ws (fun _ : unit => Pure a)))))))
        tt (List.length prefix) xs tt (List.length prefix + List.length w - List.length rest).
Proof.
  apply (@well_founded_induction_type nat lt lt_wf
    (fun fuel : nat =>
      (forall (fuel' : nat), fuel' < fuel -> forall (prefix w : list ascii) (a : A) (rest : list ascii),
         elem_parser fuel' w = Some (a, rest) ->
         denote json_grammar (prefix ++ w) elem tt (List.length prefix) a tt (List.length prefix + List.length w - List.length rest)) ->
      (forall (fuel : nat) (w : list ascii) (a : A) (rest : list ascii),
         elem_parser fuel w = Some (a, rest) -> { pre : list ascii & pre ++ rest = w }) ->
      forall (prefix w : list ascii) (xs : list A) (rest : list ascii),
        sep_by A elem_parser sep closer fuel w = Some (xs, rest) ->
        denote json_grammar (prefix ++ w)
          (Many (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a : A => Bind ws (fun _ : unit => Pure a)))))))
          tt (List.length prefix) xs tt (List.length prefix + List.length w - List.length rest))).
  intros fuel IH Hsnd Hshape prefix w xs rest H.
  destruct fuel as [| f].
  - cbn [sep_by] in H. discriminate.
  - cbn [sep_by] in H.
    destruct w as [| c rest0]; [discriminate |].
    destruct (Ascii.eqb c closer) eqn:Eclose.
    * apply (Ascii.eqb_eq c closer) in Eclose. subst c. simpl in H.
      injection H as Hxs Hrest. subst xs rest.
      replace (List.length prefix + List.length (closer :: rest0) - List.length (closer :: rest0)) with (List.length prefix) by (simpl; lia).
      apply d_many_nil.
    * destruct (Ascii.eqb c sep) eqn:Esep; [| simpl in *; discriminate].
      apply (Ascii.eqb_eq c sep) in Esep. subst c.
      destruct (elem_parser f (skip_ws rest0)) as [[a rest1] |] eqn:Ee; [| simpl in *; discriminate].
      destruct (sep_by A elem_parser sep closer f (skip_ws rest1)) as [[xs' rest2] |] eqn:Es; [| simpl in *; discriminate].
      simpl in H. injection H as Hxs Hrest. subst xs rest.
      destruct (Hshape f (skip_ws rest0) a rest1 Ee) as [X HX].
      apply d_many_cons with (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)).
      apply d_map with (a := (tt, a)).
      apply d_seq with (γ' := tt) (j := S (List.length prefix)).
      -- apply (char_sound sep prefix rest0).
      -- apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0)).
         ++ replace (S (List.length prefix)) with (List.length (prefix ++ sep :: rest0) - List.length rest0) by (rewrite !length_app; simpl; lia).
            apply (skip_ws_mid_sound (prefix ++ (sep :: rest0)) rest0).
            exists (prefix ++ [sep]). rewrite <- app_assoc. simpl. reflexivity.
         ++ apply d_bind with (a := a) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)).
            -- replace (prefix ++ (sep :: rest0)) with ((prefix ++ [sep] ++ ws_part rest0) ++ skip_ws rest0) by (rewrite <- !app_assoc; rewrite ws_part_skip; reflexivity).
               replace (S (List.length prefix) + List.length (ws_part rest0)) with (List.length (prefix ++ [sep] ++ ws_part rest0)) by (rewrite !length_app; simpl; lia).
               replace (List.length (prefix ++ [sep] ++ ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)) with (List.length (prefix ++ [sep] ++ ws_part rest0) + List.length (skip_ws rest0) - List.length rest1) by (assert (Hle : List.length rest1 <= List.length (skip_ws rest0)) by (rewrite <- HX; rewrite length_app; lia); lia).
               apply (Hsnd f (Nat.lt_succ_diag_r f) (prefix ++ [sep] ++ ws_part rest0) (skip_ws rest0) a rest1 Ee).
            -- apply d_bind with (a := tt) (γ' := tt) (j := S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)).
               ++ replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1)) with (List.length (prefix ++ (sep :: rest0)) - List.length rest1) by (rewrite !length_app; simpl; pose proof (length_ws_part_skip rest0) as Hl0; assert (Hle : List.length rest1 <= List.length (skip_ws rest0)) by (rewrite <- HX; rewrite length_app; lia); lia).
                  apply (skip_ws_mid_sound (prefix ++ (sep :: rest0)) rest1).
                  exists (prefix ++ [sep] ++ ws_part rest0 ++ X).
                  rewrite <- !app_assoc. rewrite HX. rewrite (ws_part_skip rest0). simpl. reflexivity.
               ++ apply d_pure.
               ++ replace (S (List.length prefix) + List.length (ws_part rest0) + (List.length (skip_ws rest0) - List.length rest1) + List.length (ws_part rest1)) with (List.length (prefix ++ [sep] ++ ws_part rest0 ++ X ++ ws_part rest1)) by (rewrite !length_app; rewrite <- HX; rewrite length_app; simpl; lia).
                  replace (List.length prefix + List.length (sep :: rest0) - List.length rest2) with (List.length (prefix ++ [sep] ++ ws_part rest0 ++ X ++ ws_part rest1) + List.length (skip_ws rest1) - List.length rest2) by (rewrite !length_app; simpl; assert (HXl : List.length X + List.length rest1 = List.length (skip_ws rest0)) by (rewrite <- HX; rewrite length_app; reflexivity); pose proof (length_ws_part_skip rest0) as Hl0; pose proof (length_ws_part_skip rest1) as Hl1; assert (Hle : List.length rest2 <= List.length (skip_ws rest1)) by (destruct (sep_by_shape A elem_parser sep closer Hshape f (skip_ws rest1) xs' rest2 Es) as [pre Hpre]; rewrite <- Hpre; rewrite length_app; lia); lia).
                  assert (Heq : prefix ++ (sep :: rest0) = (prefix ++ [sep] ++ ws_part rest0 ++ X ++ ws_part rest1) ++ skip_ws rest1) by (rewrite <- !app_assoc; rewrite (ws_part_skip rest1); rewrite HX; rewrite (ws_part_skip rest0); simpl; reflexivity).
                  rewrite Heq.
                  apply (IH f (Nat.lt_succ_diag_r f) (fun fuel' Hlt => Hsnd fuel' (Nat.lt_trans fuel' f (S f) Hlt (Nat.lt_succ_diag_r f))) Hshape (prefix ++ [sep] ++ ws_part rest0 ++ X ++ ws_part rest1) (skip_ws rest1) xs' rest2 Es).
Qed.

(* The hand-written tail functions are extensionally the generic loop:
   `parse_elements_more` is `sep_by` with the value parser as the element. *)
Lemma parse_elements_more_equiv_sep_by : forall (fuel : nat) (w : list ascii),
  parse_elements_more fuel w = sep_by Json parse_value ","%char "]"%char fuel w.
Proof.
  intros fuel w. revert w.
  induction fuel as [| f IH]; intros w; simpl.
  - reflexivity.
  - destruct w as [| c rest]; [reflexivity |].
    destruct (Ascii.eqb c "]"%char) eqn:E1; [reflexivity |].
    destruct (Ascii.eqb c ","%char) eqn:E2; [| reflexivity].
    destruct (parse_value f (skip_ws rest)) as [[v rest1] |] eqn:Ev; [| reflexivity].
    rewrite IH. reflexivity.
Qed.
(* Same for members: `parse_members_more` is `sep_by` with `parse_member`. *)
Lemma parse_members_more_equiv_sep_by : forall (fuel : nat) (w : list ascii),
  parse_members_more fuel w = sep_by (list ascii * Json) parse_member ","%char "}"%char fuel w.
Proof.
  intros fuel w. revert w.
  induction fuel as [| f IH]; intros w; simpl.
  - reflexivity.
  - destruct w as [| c rest]; [reflexivity |].
    unfold parse_member.
    destruct (Ascii.eqb c "}"%char) eqn:E1; [reflexivity |].
    destruct (Ascii.eqb c ","%char) eqn:E2; [| reflexivity].
    destruct (parse_string (skip_ws rest)) as [[s rest1] |] eqn:Es; [| reflexivity].
    destruct (skip_ws rest1) as [| c' rest2] eqn:Ew; [reflexivity |].
    destruct (Ascii.eqb c' ":"%char) eqn:E3; [| reflexivity].
    destruct (parse_value f (skip_ws rest2)) as [[v rest3] |] eqn:Ev; [| reflexivity].
    rewrite IH. reflexivity.
Qed.

(* Bridge: a value_spec denotation is a Call NT_value denotation. *)
Lemma value_sound_call (prefix w : list ascii) (v : Json) (j : nat) :
  denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt j ->
  denote json_grammar (prefix ++ w) (Call NT_value) tt (List.length prefix) v tt j.
Proof.
  intros H. apply d_call. cbn [json_grammar]. exact H.
Qed.

(* parse_member is sound for member_spec, given the value parser's soundness at the
   same fuel; and its result is a suffix of its input, given the value shape. *)
Lemma parse_member_sound (fuel : nat) :
  (forall (prefix w : list ascii) (v : Json) (rest : list ascii),
     parse_value fuel w = Some (v, rest) ->
     denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt (List.length prefix + List.length w - List.length rest)) ->
  forall (prefix w : list ascii) (m : list ascii * Json) (rest : list ascii),
    parse_member fuel w = Some (m, rest) ->
    denote json_grammar (prefix ++ w) member_spec tt (List.length prefix) m tt (List.length prefix + List.length w - List.length rest).
Proof.
  intros Hv prefix w m rest H.
  unfold parse_member in H.
  destruct (parse_string w) as [[s rest1] |] eqn:Es; [| discriminate].
  destruct (skip_ws rest1) as [| c' rest2] eqn:Eskip1; [discriminate |].
  destruct (Ascii.eqb c' ":"%char) eqn:Ecolon; [| discriminate].
  apply (Ascii.eqb_eq c' ":"%char) in Ecolon. subst c'.
  destruct (parse_value fuel (skip_ws rest2)) as [[v rest3] |] eqn:Ev; [| discriminate].
  simpl in H. injection H as Hm Hrest. subst m rest.
  destruct (parse_string_shape w s rest1 Es) as [p1 Hp1].
  assert (Hl : List.length rest1 = List.length (ws_part rest1) + 1 + List.length rest2) by (rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite length_app; simpl; lia).
  unfold member_spec.
  apply d_bind with (a := s) (γ' := tt) (j := List.length prefix + List.length w - List.length rest1).
  - apply (parse_string_sound prefix w s rest1 Es).
  - apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1)).
    + replace (List.length prefix + List.length w) with (List.length (prefix ++ w)) by (rewrite length_app; reflexivity).
      apply (skip_ws_mid_sound (prefix ++ w) rest1).
      exists (prefix ++ p1). rewrite <- Hp1. rewrite <- !app_assoc. reflexivity.
    + apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1) + 1).
      * assert (Heq : prefix ++ w = (prefix ++ p1 ++ ws_part rest1) ++ ":"%char :: rest2) by (rewrite <- Hp1; rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite !app_assoc; reflexivity).
        rewrite Heq.
        replace (List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1)) with (List.length (prefix ++ p1 ++ ws_part rest1)) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; lia).
        replace (List.length (prefix ++ p1 ++ ws_part rest1) + 1) with (S (List.length (prefix ++ p1 ++ ws_part rest1))) by lia.
        apply (char_sound ":"%char (prefix ++ p1 ++ ws_part rest1) rest2).
      * apply d_bind with (a := tt) (γ' := tt) (j := List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1) + 1 + List.length (ws_part rest2)).
        -- replace (List.length prefix + List.length w) with (List.length (prefix ++ w)) by (rewrite length_app; reflexivity).
           replace (List.length (prefix ++ w) - List.length rest1 + List.length (ws_part rest1) + 1) with (List.length (prefix ++ w) - List.length rest2) by (assert (Hle : List.length rest1 <= List.length (prefix ++ w)) by (rewrite <- Hp1; rewrite !length_app; lia); lia).
           apply (skip_ws_mid_sound (prefix ++ w) rest2).
           exists (prefix ++ p1 ++ ws_part rest1 ++ [":"%char]).
           rewrite <- Hp1. rewrite <- (ws_part_skip rest1) at 2. rewrite Eskip1. rewrite <- !app_assoc. simpl. reflexivity.
        -- apply d_map with (a := v). apply d_call. cbn [json_grammar].
           assert (Heq2 : prefix ++ w = (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) ++ skip_ws rest2) by (rewrite <- Hp1; rewrite <- (ws_part_skip rest1) at 1; rewrite Eskip1; rewrite <- !app_assoc; simpl; rewrite (ws_part_skip rest2); reflexivity).
           rewrite Heq2.
           replace (List.length prefix + List.length w - List.length rest1 + List.length (ws_part rest1) + 1 + List.length (ws_part rest2)) with (List.length (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2)) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; simpl; rewrite Hl; lia).
           replace (List.length prefix + List.length w - List.length rest3) with (List.length (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) + List.length (skip_ws rest2) - List.length rest3) by (rewrite !length_app; rewrite <- Hp1; rewrite length_app; simpl; pose proof (length_ws_part_skip rest2) as Hl2; lia).
           apply (Hv (prefix ++ p1 ++ ws_part rest1 ++ [":"%char] ++ ws_part rest2) (skip_ws rest2) v rest3 Ev).
Qed.

Lemma parse_member_shape (fuel : nat) :
  (forall (w : list ascii) (v : Json) (rest : list ascii),
     parse_value fuel w = Some (v, rest) -> { pre : list ascii & pre ++ rest = w }) ->
  forall (w : list ascii) (m : list ascii * Json) (rest : list ascii),
    parse_member fuel w = Some (m, rest) -> { pre : list ascii & pre ++ rest = w }.
Proof.
  intros Hv w m rest H.
  unfold parse_member in H.
  destruct (parse_string w) as [[s rest1] |] eqn:Es; [| discriminate].
  destruct (skip_ws rest1) as [| c' rest2] eqn:Eskip1; [discriminate |].
  destruct (Ascii.eqb c' ":"%char) eqn:Ecolon; [| discriminate].
  apply (Ascii.eqb_eq c' ":"%char) in Ecolon. subst c'.
  destruct (parse_value fuel (skip_ws rest2)) as [[v rest3] |] eqn:Ev; [| discriminate].
  simpl in H. injection H as Hm Hrest. subst m rest.
  destruct (parse_string_shape w s rest1 Es) as [p1 Hp1].
  destruct (Hv (skip_ws rest2) v rest3 Ev) as [X HX].
  apply (suffix_compose w rest2 rest3).
  + apply (suffix_compose w rest1 rest2).
    * exact (existT _ p1 Hp1).
    * apply (suffix_compose rest1 (":"%char :: rest2) rest2).
      -- exists (ws_part rest1). transitivity (ws_part rest1 ++ skip_ws rest1).
         ++ rewrite Eskip1. reflexivity.
         ++ apply (ws_part_skip rest1).
      -- exists [":"%char]. simpl. reflexivity.
  + apply (suffix_compose rest2 (skip_ws rest2) rest3).
    * exact (skip_ws_suffix rest2).
    * exact (existT _ X HX).
Qed.

(* Mutual soundness of the seven recursive functions, by strong induction on fuel. *)
#[local] Definition sound_7 (fuel : nat) : Type :=
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
  apply (@well_founded_induction_type nat lt lt_wf sound_7).
  intros fuel IH.
  destruct fuel as [| fuel']; simpl.
  - repeat split; intros; discriminate.
  - destruct (IH fuel' (Nat.lt_succ_diag_r fuel')) as [[[[[[IHv IHo] IHa] IHm] IHmm] IHe] IHem].
    destruct (parse_all_shape fuel') as [[[[[[Sv So] Sa] Sm] Smm] Se] Sem].
    repeat split; intros prefix w res rest Hparse; cbn [parse_value parse_object parse_array parse_members parse_members_more parse_elements parse_elements_more] in Hparse.
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
      apply (sep_by_sound (list ascii * Json) member_spec parse_member ","%char "}"%char (S fuel')
        (fun m Hlt prefix w mm rest H => parse_member_sound m (fst (fst (fst (fst (fst (fst (IH m Hlt))))))) prefix w mm rest H)
        (fun m w mm rest H => parse_member_shape m (fst (fst (fst (fst (fst (fst (parse_all_shape m))))))) w mm rest H)
        prefix w res rest).
      rewrite <- (parse_members_more_equiv_sep_by (S fuel') w). exact Hparse.
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
      apply (sep_by_sound Json (Call NT_value) parse_value ","%char "]"%char (S fuel')
        (fun m Hlt prefix w v rest H => value_sound_call prefix w v (List.length prefix + List.length w - List.length rest)
          (fst (fst (fst (fst (fst (fst (IH m Hlt)))))) prefix w v rest H))
        (fun fuel w v rest H => fst (fst (fst (fst (fst (fst (parse_all_shape fuel)))))) w v rest H)
        prefix w res rest).
      rewrite <- (parse_elements_more_equiv_sep_by (S fuel') w). exact Hparse.
Qed.
(* Whole-document soundness. *)
Lemma parse_json_sound (w : list ascii) (v : Json) :
  parse_json w = Some v ->
  denote json_grammar w json_text tt 0 v tt (List.length w).
Proof.
  intros H.
  unfold parse_json in H.
  destruct (parse_value (3 * List.length w + 2) (skip_ws w)) as [[v' rest] |] eqn:Ev; [| discriminate].
  destruct (skip_ws rest) as [| c tl] eqn:Eskip; [| discriminate].
  injection H as Hv. subst v.
  assert (Hws : ws_part rest = rest) by (symmetry; rewrite <- (ws_part_skip rest) at 1; rewrite Eskip; apply app_nil_r).
  destruct (parse_all_shape (3 * List.length w + 2)) as [[[[[[Sv _] _] _] _] _] _].
  destruct (Sv (skip_ws w) v' rest Ev) as [pre Hpre].
  destruct (parse_all_sound (3 * List.length w + 2)) as [[[[[[IHv _] _] _] _] _] _].
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
(* 14. Completeness: every denotation is accepted                            *)
(* ------------------------------------------------------------------------- *)

(* char x at the head of (prefix ++ c :: w) forces x = c. *)
Lemma char_denote_eq (x c : ascii) (prefix w : list ascii) (a : unit) (γ' : unit) (j : nat) :
  denote json_grammar (prefix ++ c :: w) (char x) tt (List.length prefix) a γ' j ->
  x = c.
Proof.
  intros Hd. unfold char in Hd.
  pose proof (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) ascii unit (fun _ : ascii => tt) (Tok (fun c' : ascii => c' = x)) tt γ' (List.length prefix) j a) Hd) as Hm.
  destruct Hm as [t [Ea Htok]].
  pose proof (fst (denote_tok_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (fun c' : ascii => c' = x) t tt γ' (List.length prefix) j) Htok) as Ht.
  destruct Ht as [[[Eg Ej] Hnth] HP].
  simpl in HP.
  rewrite (nth_error_app_cons c prefix w) in Hnth. injection Hnth as Hct.
  rewrite <- Hct in HP. exact (eq_sym HP).
Qed.

(* digit1-9 characters are not whitespace. *)
Lemma digit_no_ws (c : ascii) : is_digit1_9b c = true -> is_wsb c = false.
Proof.
  unfold is_digit1_9b, is_wsb.
  intro H.
  repeat (apply orb_true_iff in H; destruct H as [H | H]).
  all: apply Ascii.eqb_eq in H; subst c; compute; reflexivity.
Qed.

(* char x at the head of (prefix ++ c :: w): full positional info. *)
Lemma char_denote_full (x c : ascii) (prefix w : list ascii) (a : unit) (γ' : unit) (j : nat) :
  denote json_grammar (prefix ++ c :: w) (char x) tt (List.length prefix) a γ' j ->
  x = c /\ a = tt /\ γ' = tt /\ j = S (List.length prefix).
Proof.
  intros Hd. unfold char in Hd.
  pose proof (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) ascii unit (fun _ : ascii => tt) (Tok (fun c' : ascii => c' = x)) tt γ' (List.length prefix) j a) Hd) as Hm.
  destruct Hm as [t [Ea Htok]].
  pose proof (fst (denote_tok_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (fun c' : ascii => c' = x) t tt γ' (List.length prefix) j) Htok) as Ht.
  destruct Ht as [[[Eg Ej] Hnth] HP].
  rewrite (nth_error_app_cons c prefix w) in Hnth. injection Hnth as Hct.
  rewrite <- Hct in HP.
  split; [exact (eq_sym HP) | split; [exact Ea | split; [exact Eg | exact Ej]]].
Qed.

(* char x at an arbitrary position i in the full input w. *)
Lemma char_denote_nth (w : list ascii) (x : ascii) (i j : nat) (a : unit) (γ' : unit) :
  denote json_grammar w (char x) tt i a γ' j ->
  nth_error w i = Some x /\ a = tt /\ γ' = tt /\ j = S i.
Proof.
  intros Hd. unfold char in Hd.
  pose proof (fst (denote_map_iff ascii unit json_nt json_grammar w ascii unit (fun _ : ascii => tt) (Tok (fun c' : ascii => c' = x)) tt γ' i j a) Hd) as Hm.
  destruct Hm as [t [Ea Htok]].
  pose proof (fst (denote_tok_iff ascii unit json_nt json_grammar w (fun c' : ascii => c' = x) t tt γ' i j) Htok) as Ht.
  destruct Ht as [[[Eg Ej] Hnth] HP].
  rewrite HP in Hnth.
  split; [exact Hnth | split; [exact Ea | split; [exact Eg | exact Ej]]].
Qed.
(* A value cannot start with a whitespace character. *)
(* lit (String x s) at the head of (prefix ++ c :: w) forces x = c. *)
Lemma lit_head (x : ascii) (s : string) (prefix w : list ascii) (c : ascii) (a : unit) (γ' : unit) (j : nat) :
  denote json_grammar (prefix ++ c :: w) (lit (String x s)) tt (List.length prefix) a γ' j ->
  x = c.
Proof.
  intros Hd. unfold lit in Hd.
  apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char x) (lit s)) tt γ' (List.length prefix) j a)) in Hd.
  destruct Hd as [p [Ea Hseq]].
  apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit unit (char x) (lit s) tt γ' (List.length prefix) j p)) in Hseq.
  destruct Hseq as [γ1 [j1 [a1 [b1 [[E Hc] _]]]]].
  exact (char_denote_eq x c prefix w a1 γ1 j1 Hc).
Qed.

(* Bind (char x) f at the head forces x = c. *)
Lemma bind_char_head (x : ascii) (B : Type) (f : unit -> Spec ascii unit json_nt B) (prefix w : list ascii) (c : ascii) (b : B) (γ' : unit) (j : nat) :
  denote json_grammar (prefix ++ c :: w) (Bind (char x) f) tt (List.length prefix) b γ' j ->
  x = c.
Proof.
  intros Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit B (char x) f tt γ' (List.length prefix) j b)) in Hd.
  destruct Hd as [γ1 [j1 [a [Hc _]]]].
  exact (char_denote_eq x c prefix w a γ1 j1 Hc).
Qed.

(* number_spec cannot start with whitespace. *)
Lemma number_no_ws (prefix w : list ascii) (c : ascii) (n : Z) (j : nat) :
  is_wsb c = true ->
  denote json_grammar (prefix ++ c :: w) number_spec tt (List.length prefix) n tt j -> False.
Proof.
  intros Hws Hd.
  unfold number_spec in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ c :: w) bool Z (Alt (Map (fun _ : unit => true) (char "-"%char)) (Pure false)) (fun neg : bool => Map (fun n0 : nat => if neg then Z.opp (Z.of_nat n0) else Z.of_nat n0) int_spec) tt tt (List.length prefix) j n)) in Hd.
  destruct Hd as [γ1 [j1 [neg [Hneg Hn]]]].
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) bool (Map (fun _ : unit => true) (char "-"%char)) (Pure false) tt γ1 (List.length prefix) j1 neg)) in Hneg.
  destruct Hneg as [Hdash | Hfalse].
  - apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit bool (fun _ : unit => true) (char "-"%char) tt γ1 (List.length prefix) j1 neg)) in Hdash.
    destruct Hdash as [u [E Hc]].
    apply (char_denote_eq "-"%char c prefix w u γ1 j1) in Hc. subst c. simpl in Hws. discriminate.
  - apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ c :: w) bool false tt (List.length prefix) neg γ1 j1)) in Hfalse.
    destruct Hfalse as [[Eneg Eg] Ej]. subst neg.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) nat Z (fun n0 : nat => Z.of_nat n0) int_spec γ1 tt j1 j n)) in Hn.
    destruct Hn as [n0 [En Hint]].
    unfold int_spec in Hint.
    apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) nat (Map (fun _ : unit => 0) (char "0"%char)) (Map (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec))) γ1 tt j1 j n0)) in Hint.
    destruct Hint as [Hz | Hd1].
    + apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit nat (fun _ : unit => 0) (char "0"%char) γ1 tt j1 j n0)) in Hz.
      destruct Hz as [u [Ez Hc0]].
      rewrite Eg in Hc0. rewrite Ej in Hc0.
      apply (char_denote_eq "0"%char c prefix w u tt j) in Hc0. subst c. simpl in Hws. discriminate.
    + apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (ascii * list ascii) nat (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec)) γ1 tt j1 j n0)) in Hd1.
      destruct Hd1 as [p [Ed Hseq]].
      apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ c :: w) ascii (list ascii) digit1_9_spec (Many digit_spec) γ1 tt j1 j p)) in Hseq.
      destruct Hseq as [γ2 [j2 [a2 [b2 [[Eseq Hd1'] _]]]]].
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (fun c' : ascii => is_digit1_9b c' = true) a2 γ1 γ2 j1 j2)) in Hd1'.
      destruct Hd1' as [[[Egt Ejt] Hnth] HP].
      rewrite Ej in Hnth. rewrite (nth_error_app_cons c prefix w) in Hnth. inversion Hnth. subst. simpl in HP.
      rewrite (digit_no_ws a2 HP) in Hws. discriminate.
Qed.

(* A value cannot start with a whitespace character. *)
Lemma value_no_ws (prefix : list ascii) (c : ascii) (w : list ascii) (v : Json) (j : nat) :
  is_wsb c = true ->
  denote json_grammar (prefix ++ c :: w) value_spec tt (List.length prefix) v tt j -> False.
Proof.
  intros Hws Hd.
  unfold value_spec in Hd.
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json (Map (fun _ : unit => JNull) (lit "null")) _ tt tt (List.length prefix) j v)) in Hd.
  destruct Hd as [Hd | Hd].
  - apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit Json (fun _ : unit => JNull) (lit "null") tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [unull [Enull Hlitnull]].
    apply (lit_head "n"%char "ull" prefix w c unull tt j) in Hlitnull. subst c. simpl in Hws. discriminate.
  - apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [Hd | Hd].
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) bool Json (fun b : bool => JBool b) _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [bb [Ebool Hb0]].
        apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) bool _ _ tt tt (List.length prefix) j bb)) in Hb0.
        destruct Hb0 as [Htrue0 | Hfalse0].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit bool (fun _ : unit => true) (lit "true") tt tt (List.length prefix) j bb)) in Htrue0.
           destruct Htrue0 as [utrue [Etrue Hlittrue]].
           apply (lit_head "t"%char "rue" prefix w c utrue tt j) in Hlittrue. subst c. simpl in Hws. discriminate.
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit bool (fun _ : unit => false) (lit "false") tt tt (List.length prefix) j bb)) in Hfalse0.
           destruct Hfalse0 as [ufalse [Efalse Hlitfalse]].
           apply (lit_head "f"%char "alse" prefix w c ufalse tt j) in Hlitfalse. subst c. simpl in Hws. discriminate.
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list ascii) Json JString string_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [ss [Estr Hs0]].
        apply (bind_char_head "034"%char (list ascii) (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) prefix w c ss tt j) in Hs0.
        subst c. simpl in Hws. discriminate.
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Z Json JNumber number_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [nn [Enum Hn0]]. subst v.
        exact (number_no_ws prefix w c nn j Hws Hn0).
      * apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [Hd | Hd].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list Json) Json JArray array_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [vv [Earr Ha0]].
           apply (bind_char_head "091"%char (list Json) (fun _ : unit => Bind ws (fun _ : unit => Bind elements_spec (fun vs : list Json => Bind ws (fun _ : unit => Bind (char "093"%char) (fun _ : unit => Pure vs))))) prefix w c vv tt j) in Ha0.
           subst c. simpl in Hws. discriminate.
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list (list ascii * Json)) Json JObject object_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [mm [Eobj Ho0]].
           apply (bind_char_head "123"%char (list (list ascii * Json)) (fun _ : unit => Bind ws (fun _ : unit => Bind members_spec (fun ms : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "125"%char) (fun _ : unit => Pure ms))))) prefix w c mm tt j) in Ho0.
           subst c. simpl in Hws. discriminate.
Qed.

(* A members/elements/rest derivation whose input begins with a whitespace
   character is forced to the empty branch. *)
Lemma members_ws_empty (prefix w : list ascii) (c : ascii) (ms : list (list ascii * Json)) (j : nat) :
  is_wsb c = true ->
  denote json_grammar (prefix ++ c :: w) members_spec tt (List.length prefix) ms tt j ->
  ms = @nil (list ascii * Json) /\ j = List.length prefix.
Proof.
  intros Hws Hd. unfold members_spec in Hd.
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list (list ascii * Json)) (Pure (@nil (list ascii * Json))) _ tt tt (List.length prefix) j ms)) in Hd.
  destruct Hd as [Hnil | Hcons].
  - apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list (list ascii * Json)) (@nil (list ascii * Json)) tt (List.length prefix) ms tt j)) in Hnil.
    destruct Hnil as [[Ems Eg] Ej]. subst. split; reflexivity.
  - apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list ascii * Json) (list (list ascii * Json)) member_spec _ tt tt (List.length prefix) j ms)) in Hcons.
    destruct Hcons as [γ1 [j1 [m [Hmem _]]]].
    unfold member_spec in Hmem.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list ascii) (list ascii * Json) string_spec _ tt γ1 (List.length prefix) j1 m)) in Hmem.
    destruct Hmem as [γ2 [j2 [s [Hs _]]]].
    apply (bind_char_head "034"%char (list ascii) (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) prefix w c s γ2 j2) in Hs.
    subst c. simpl in Hws. discriminate.
Qed.

Lemma members_rest_ws_empty (prefix w : list ascii) (c : ascii) (ms : list (list ascii * Json)) (j : nat) :
  is_wsb c = true ->
  denote json_grammar (prefix ++ c :: w) members_rest_spec tt (List.length prefix) ms tt j ->
  ms = @nil (list ascii * Json) /\ j = List.length prefix.
Proof.
  intros Hws Hd. unfold members_rest_spec in Hd.
  apply (fst (denote_many_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list ascii * Json) (Map snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind member_spec (fun m : list ascii * Json => Bind ws (fun _ : unit => Pure m)))))) tt tt (List.length prefix) j ms)) in Hd.
  destruct Hd as [Hnil | Hcons].
  - destruct Hnil as [[Ems Eg] Ej]. subst. split; reflexivity.
  - destruct Hcons as [a [as' [γ' [k [[_ Hone] _]]]]].
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (unit * (list ascii * Json)) (list ascii * Json) snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind member_spec (fun m : list ascii * Json => Bind ws (fun _ : unit => Pure m))))) tt γ' (List.length prefix) k a)) in Hone.
    destruct Hone as [x [E Hseq]].
    apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit (list ascii * Json) (char ","%char) (Bind ws (fun _ : unit => Bind member_spec (fun m : list ascii * Json => Bind ws (fun _ : unit => Pure m)))) tt γ' (List.length prefix) k x)) in Hseq.
    destruct Hseq as [γ1 [j1 [a1 [b1 [[_ Hc] _]]]]].
    apply (char_denote_eq ","%char c prefix w a1 γ1 j1) in Hc. subst c. simpl in Hws. discriminate.
Qed.

Lemma elements_ws_empty (prefix w : list ascii) (c : ascii) (vs : list Json) (j : nat) :
  is_wsb c = true ->
  denote json_grammar (prefix ++ c :: w) elements_spec tt (List.length prefix) vs tt j ->
  vs = @nil Json /\ j = List.length prefix.
Proof.
  intros Hws Hd. unfold elements_spec in Hd.
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list Json) (Pure (@nil Json)) _ tt tt (List.length prefix) j vs)) in Hd.
  destruct Hd as [Hnil | Hcons].
  - apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (list Json) (@nil Json) tt (List.length prefix) vs tt j)) in Hnil.
    destruct Hnil as [[Evs Eg] Ej]. subst. split; reflexivity.
  - apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json (list Json) (Call NT_value) _ tt tt (List.length prefix) j vs)) in Hcons.
    destruct Hcons as [γ1 [j1 [v [Hv _]]]].
    apply (fst (denote_call_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json NT_value tt γ1 (List.length prefix) j1 v)) in Hv.
    cbn [json_grammar] in Hv. destruct γ1. exfalso. exact (value_no_ws prefix c w v j1 Hws Hv).
Qed.

Lemma elements_rest_ws_empty (prefix w : list ascii) (c : ascii) (vs : list Json) (j : nat) :
  is_wsb c = true ->
  denote json_grammar (prefix ++ c :: w) elements_rest_spec tt (List.length prefix) vs tt j ->
  vs = @nil Json /\ j = List.length prefix.
Proof.
  intros Hws Hd. unfold elements_rest_spec in Hd.
  apply (fst (denote_many_iff ascii unit json_nt json_grammar (prefix ++ c :: w) Json (Map snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind (Call NT_value) (fun v : Json => Bind ws (fun _ : unit => Pure v)))))) tt tt (List.length prefix) j vs)) in Hd.
  destruct Hd as [Hnil | Hcons].
  - destruct Hnil as [[Evs Eg] Ej]. subst. split; reflexivity.
  - destruct Hcons as [a [as' [γ' [k [[_ Hone] _]]]]].
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ c :: w) (unit * Json) Json snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind (Call NT_value) (fun v : Json => Bind ws (fun _ : unit => Pure v))))) tt γ' (List.length prefix) k a)) in Hone.
    destruct Hone as [x [E Hseq]].
    apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ c :: w) unit Json (char ","%char) (Bind ws (fun _ : unit => Bind (Call NT_value) (fun v : Json => Bind ws (fun _ : unit => Pure v)))) tt γ' (List.length prefix) k x)) in Hseq.
    destruct Hseq as [γ1 [j1 [a1 [b1 [[_ Hc] _]]]]].
    apply (char_denote_eq ","%char c prefix w a1 γ1 j1) in Hc. subst c. simpl in Hws. discriminate.
Qed.

Lemma nth_error_self_none (w : list ascii) : nth_error w (List.length w) = None.
Proof. induction w; simpl; [reflexivity | exact IHw]. Qed.
(* Leaf parser completeness: a denotation of a literal forces parse_lit to
   succeed. *)
Transparent parse_lit.

Lemma skipn_length_app (A : Type) (l m : list A) : skipn (List.length l) (l ++ m) = m.
Proof.
  induction l; simpl; [reflexivity | exact IHl].
Qed.

Lemma parse_lit_complete (s : string) (prefix w : list ascii) (j : nat) :
  denote json_grammar (prefix ++ w) (lit s) tt (List.length prefix) tt tt j ->
  parse_lit s w = Some (skipn j (prefix ++ w)).
Proof.
  revert prefix w j. induction s as [| c s' IH]; intros prefix w j Hd.
  - apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) unit tt tt (List.length prefix) tt tt j)) in Hd.
    destruct Hd as [[_ _] Ej]. subst j. simpl. rewrite (skipn_length_app ascii prefix w). reflexivity.
  - simpl in Hd.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char c) (lit s')) tt tt (List.length prefix) j tt)) in Hd.
    destruct Hd as [p [Emap Hseq]].
    apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char c) (lit s') tt tt (List.length prefix) j p)) in Hseq.
    destruct Hseq as [γ1 [j1 [a [b [[Eseq Hc] Hl]]]]].
    destruct w as [| c' rest].
    + rewrite app_nil_r in Hc. unfold char in Hc.
      apply (fst (denote_map_iff ascii unit json_nt json_grammar prefix ascii unit (fun _ : ascii => tt) (Tok (fun x : ascii => x = c)) tt γ1 (List.length prefix) j1 a)) in Hc.
      destruct Hc as [t [Emap2 Htok]].
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar prefix (fun x : ascii => x = c) t tt γ1 (List.length prefix) j1)) in Htok.
      destruct Htok as [[[Eg Ej] Hnth] HP].
      rewrite (nth_error_self_none prefix) in Hnth. discriminate.
    + apply (char_denote_full c c' prefix rest a γ1 j1) in Hc.
      destruct Hc as [Ecc [Ea [Eg Ej]]]. subst c. subst γ1. subst j1. destruct b.
      replace (prefix ++ c' :: rest) with ((prefix ++ [c']) ++ rest) in Hl by (rewrite <- app_assoc; simpl; reflexivity).
      replace (S (List.length prefix)) with (List.length (prefix ++ [c'])) in Hl by (rewrite length_app; simpl; lia).
      simpl. destruct (Ascii.eqb c' c') eqn:E.
      * simpl. rewrite (IH (prefix ++ [c']) rest j Hl).
        replace (prefix ++ c' :: rest) with ((prefix ++ [c']) ++ rest) by (rewrite <- app_assoc; simpl; reflexivity).
        reflexivity.
      * exfalso. assert (Ht : Ascii.eqb c' c' = true) by apply Ascii.eqb_refl. rewrite Ht in E. discriminate.
Qed.

Transparent parse_value parse_object parse_array parse_members parse_members_more parse_elements parse_elements_more.

Transparent parse_string_chars parse_string.

Lemma skipn_cons_head (A : Type) (w : list A) (i : nat) (c : A) :
  nth_error w i = Some c -> skipn i w = c :: skipn (S i) w.
Proof.
  revert w. induction i as [| i' IH]; intros w H.
  - destruct w as [| c' rest]; simpl in *; [discriminate |].
    injection H as Hc. subst c'. reflexivity.
  - destruct w as [| c' rest]; simpl in *; [discriminate |].
    apply IH. exact H.
Qed.

Lemma skipn_prefix_cons (prefix rest : list ascii) (c : ascii) :
  skipn (S (List.length prefix)) (prefix ++ c :: rest) = rest.
Proof.
  induction prefix as [| p ps IH]; simpl; [reflexivity | exact IH].
Qed.
Lemma parse_string_chars_complete (w : list ascii) (i j : nat) (cs : list ascii) :
  denote json_grammar w (Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) tt i cs tt j ->
  parse_string_chars (skipn i w) = Some (cs, skipn j w).
Proof.
  revert w i j. induction cs as [| c cs' IH]; intros w i j Hd.
  - apply (fst (denote_bind_iff ascii unit json_nt json_grammar w (list ascii) (list ascii) (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs)) tt tt i j (@nil ascii))) in Hd.
    destruct Hd as [γ1 [j1 [a [Hmany Hclose]]]].
    apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii string_char_spec tt γ1 i j1 a)) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[Ea Eg] Ej]. subst a γ1 j1.
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar w unit (list ascii) (char "034"%char) (fun _ : unit => Pure (@nil ascii)) tt tt i j (@nil ascii))) in Hclose.
      destruct Hclose as [γ2 [j2 [u [Hq Hpure]]]].
      apply (char_denote_nth w "034"%char i j2 u γ2) in Hq.
      destruct Hq as [Hnth [Ea2 [Eg2 Ej2]]]. subst u γ2 j2.
      apply (fst (denote_pure_iff ascii unit json_nt json_grammar w (list ascii) (@nil ascii) tt (S i) (@nil ascii) tt j)) in Hpure.
      destruct Hpure as [[_ _] Ej]. subst j.
      rewrite (skipn_cons_head ascii w i "034"%char Hnth). simpl. reflexivity.
    + destruct Hcons as [x [as' [γ'' [k [[E _] _]]]]].
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar w unit (list ascii) (char "034"%char) (fun _ : unit => Pure a) γ1 tt j1 j (@nil ascii))) in Hclose.
      destruct Hclose as [γ2 [j2 [u [Hq Hpure]]]].
      apply (fst (denote_pure_iff ascii unit json_nt json_grammar w (list ascii) a γ2 j2 (@nil ascii) tt j)) in Hpure.
      destruct Hpure as [[Ea2 Eg2] Ej2]. subst a. discriminate.
  - apply (fst (denote_bind_iff ascii unit json_nt json_grammar w (list ascii) (list ascii) (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs)) tt tt i j (c :: cs'))) in Hd.
    destruct Hd as [γ1 [j1 [a [Hmany Hclose]]]].
    apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii string_char_spec tt γ1 i j1 a)) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[Ea Eg] Ej].
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar w unit (list ascii) (char "034"%char) (fun _ : unit => Pure a) γ1 tt j1 j (c :: cs'))) in Hclose.
      destruct Hclose as [γ2 [j2 [u [Hq Hpure]]]].
      apply (fst (denote_pure_iff ascii unit json_nt json_grammar w (list ascii) a γ2 j2 (c :: cs') tt j)) in Hpure.
      destruct Hpure as [[Ea2 Eg2] Ej2]. subst a. discriminate.
    + destruct Hcons as [x [as' [γ'' [k [[E Hone] Htail]]]]].
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar w unit (list ascii) (char "034"%char) (fun _ : unit => Pure a) γ1 tt j1 j (c :: cs'))) in Hclose.
      destruct Hclose as [γ2 [j2 [u [Hquote Hpure]]]].
      apply (fst (denote_pure_iff ascii unit json_nt json_grammar w (list ascii) a γ2 j2 (c :: cs') tt j)) in Hpure.
      destruct Hpure as [[Epp Egp] Ejp].
      subst a. inversion Epp. subst x as' γ2 j2. destruct u.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar w (fun c0 : ascii => is_string_charb c0 = true) c tt γ'' i k)) in Hone.
      destruct Hone as [[[Eg2 Ej2] Hnth] HP].
      subst γ''. subst k.
      assert (Htail' : denote json_grammar w (Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) tt (S i) cs' tt j).
      { apply (d_bind ascii unit json_nt json_grammar w (list ascii) (list ascii) (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs)) tt γ1 tt (S i) j1 j cs' cs' Htail).
        apply (d_bind ascii unit json_nt json_grammar w unit (list ascii) (char "034"%char) (fun _ : unit => Pure cs') γ1 tt tt j1 j j tt cs' Hquote).
        apply (d_pure ascii unit json_nt json_grammar w (list ascii) cs' tt j). }
      specialize (IH w (S i) j Htail') as Hr.
      rewrite (skipn_cons_head ascii w i c Hnth).

      simpl.
      destruct (Ascii.eqb c "034"%char) eqn:E.
      * exfalso. simpl in HP.
        unfold is_string_charb in HP. apply Ascii.eqb_eq in E. subst c. simpl in HP. discriminate.
      * simpl. destruct (is_string_charb c) eqn:Ec.
        -- simpl in Hr. rewrite Hr. reflexivity.
        -- discriminate.
Qed.

Lemma parse_string_complete (prefix w : list ascii) (s : list ascii) (j : nat) :
  denote json_grammar (prefix ++ w) string_spec tt (List.length prefix) s tt j ->
  parse_string w = Some (s, skipn j (prefix ++ w)).
Proof.
  intros Hd. unfold string_spec in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii) (char "034"%char) (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) tt tt (List.length prefix) j s)) in Hd.
  destruct Hd as [γ1 [j1 [u [Hq Hbody]]]].
  destruct w as [| c0 rest].
  - rewrite (app_nil_r prefix) in Hq. apply (char_denote_nth prefix "034"%char (List.length prefix) j1 u γ1) in Hq.
    destruct Hq as [Hnth _]. rewrite (nth_error_self_none prefix) in Hnth. discriminate.
  - apply (char_denote_full "034"%char c0 prefix rest u γ1 j1) in Hq.
    destruct Hq as [E [Ea [Eg Ej]]]. subst c0. subst u. subst γ1. subst j1.
    specialize (parse_string_chars_complete (prefix ++ "034"%char :: rest) (S (List.length prefix)) j s Hbody) as Hsc.
    rewrite (skipn_prefix_cons prefix rest "034"%char) in Hsc.
    unfold parse_string. simpl. exact Hsc.
Qed.

(** Completeness for the digit-run leaf: `take_digits` (maximal run) agrees with
    a `Many digit_spec` denotation *provided the next position is not a digit*.
    That proviso is exactly what the trailing `ws`/`,`/`]`/`}` context supplies
    at every call site, so the greedy parser and the non-deterministic spec
    agree on the value. *)

Lemma nth_error_skipn_head (w : list ascii) (i : nat) :
  nth_error (skipn i w) 0 = nth_error w i.
Proof.
  revert w. induction i as [| i' IH]; intros w.
  - reflexivity.
  - destruct w as [| c rest]; simpl; [reflexivity | exact (IH rest)].
Qed.

Lemma take_digits_none (w : list ascii) :
  (forall c : ascii, nth_error w 0 = Some c -> is_digitb c = false) ->
  take_digits w = (@nil ascii, w).
Proof.
  induction w as [| c rest IH]; intros Hnd; simpl.
  - reflexivity.
  - assert (Hc : is_digitb c = false) by (apply Hnd; reflexivity).
    rewrite Hc. reflexivity.
Qed.

Lemma take_digits_complete (w : list ascii) (i j : nat) (ds : list ascii) :
  denote json_grammar w (Many digit_spec) tt i ds tt j ->
  (forall c : ascii, nth_error w j = Some c -> is_digitb c = false) ->
  take_digits (skipn i w) = (ds, skipn j w).
Proof.
  revert w i j. induction ds as [| d ds' IH]; intros w i j Hd Hnd.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii digit_spec tt tt i j (@nil ascii))) in Hd.
    destruct Hd as [Hnil | Hcons].
    + destruct Hnil as [[_ Eg] Ej]. subst.
      apply take_digits_none. intros c Hc.
      rewrite nth_error_skipn_head in Hc. eapply Hnd. exact Hc.
    + destruct Hcons as [a [as' [γ'' [k [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii digit_spec tt tt i j (d :: ds'))) in Hd.
    destruct Hd as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
      injection E as Ea Eas'. subst a as'.
      unfold digit_spec in Hone.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar w (fun c : ascii => is_digitb c = true) d tt γ'' i k)) in Hone.
      destruct Hone as [[[Eg Ej] Hnth] HP].
      subst γ''. subst k.
      specialize (IH w (S i) j Htail Hnd).
      rewrite (skipn_cons_head ascii w i d Hnth).
      cbn [take_digits]. rewrite HP.
      destruct (take_digits (skipn (S i) w)) as [ds1 rest1] eqn:Etd.
      simpl. rewrite IH in Etd. congruence.
Qed.

(* char x at the head of `w` (input `prefix ++ w`): exposes the head and the
   position of the following input. *)
Lemma char_head_cons (x : ascii) (prefix w : list ascii) (u : unit) (γ' : unit) (j : nat) :
  denote json_grammar (prefix ++ w) (char x) tt (List.length prefix) u γ' j ->
  { rest : list ascii & w = x :: rest /\ γ' = tt /\ j = S (List.length prefix) }.
Proof.
  intros Hd.
  apply (char_denote_nth (prefix ++ w) x (List.length prefix) j u γ') in Hd.
  destruct Hd as [Hnth [_ [Eg Ej]]].
  destruct w as [| c rest].
  - rewrite app_nil_r in Hnth. rewrite (nth_error_self_none prefix) in Hnth. discriminate.
  - rewrite (nth_error_app_cons c prefix rest) in Hnth. injection Hnth as Hcx. subst c.
    exists rest. split; [reflexivity | split; [exact Eg | exact Ej]].
Qed.

Lemma nth_error_app_cons2 (x : ascii) (prefix rest : list ascii) :
  nth_error (prefix ++ x :: rest) (S (List.length prefix)) = nth_error rest 0.
Proof.
  induction prefix as [| p ps IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma skipn_prefix_cons2 (prefix rest : list ascii) (a b : ascii) :
  skipn (S (S (List.length prefix))) (prefix ++ a :: b :: rest) = rest.
Proof.
  induction prefix as [| p ps IH]; simpl; [reflexivity | exact IH].
Qed.

(** Number leaf completeness: a `number_spec` denotation whose next position
    is not a digit forces `parse_number` to succeed with exactly that value
    and the corresponding remaining input. *)
Transparent parse_number take_digits.
Lemma parse_number_complete (prefix w : list ascii) (n : Z) (j : nat) :
  denote json_grammar (prefix ++ w) number_spec tt (List.length prefix) n tt j ->
  (forall c : ascii, nth_error (prefix ++ w) j = Some c -> is_digitb c = false) ->
  parse_number w = Some (n, skipn j (prefix ++ w)).
Proof.
  intros Hd Hnd. unfold number_spec in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) bool Z
    (Alt (Map (fun _ : unit => true) (char "-"%char)) (Pure false))
    (fun neg : bool => Map (fun n0 : nat => if neg then Z.opp (Z.of_nat n0) else Z.of_nat n0) int_spec)
    tt tt (List.length prefix) j n)) in Hd.
  destruct Hd as [γ1 [j1 [neg [Hneg Hn]]]].
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) bool
    (Map (fun _ : unit => true) (char "-"%char)) (Pure false) tt γ1 (List.length prefix) j1 neg)) in Hneg.
  destruct Hneg as [Hdash | Hfalse].
  - (* ---------- negative ---------- *)
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool
      (fun _ : unit => true) (char "-"%char) tt γ1 (List.length prefix) j1 neg)) in Hdash.
    destruct Hdash as [u [Eneg Hc]].
    subst neg.
    apply (char_head_cons "-"%char prefix w u γ1 j1) in Hc.
    destruct Hc as [rest1 [Ew [Eg Ej]]]. subst γ1. subst j1. subst w.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ "-"%char :: rest1) nat Z
      (fun n0 : nat => Z.opp (Z.of_nat n0)) int_spec tt tt (S (List.length prefix)) j n)) in Hn.
    destruct Hn as [n0 [En Hint]].
    unfold int_spec in Hint.
    apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ "-"%char :: rest1) nat
      (Map (fun _ : unit => 0) (char "0"%char))
      (Map (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec)))
      tt tt (S (List.length prefix)) j n0)) in Hint.
    destruct Hint as [Hz | Hd1].
    + (* -0 *)
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ "-"%char :: rest1) unit nat
        (fun _ : unit => 0) (char "0"%char) tt tt (S (List.length prefix)) j n0)) in Hz.
      destruct Hz as [u0 [Ez Hc0]].
      replace (prefix ++ "-"%char :: rest1) with ((prefix ++ ["-"%char]) ++ rest1) in Hc0 by (rewrite <- app_assoc; simpl; reflexivity).
      replace (S (List.length prefix)) with (List.length (prefix ++ ["-"%char])) in Hc0 by (rewrite length_app; simpl; lia).
      apply (char_head_cons "0"%char (prefix ++ ["-"%char]) rest1 u0 tt j) in Hc0.
      destruct Hc0 as [rest0 [Ew0 [Eg0 Ej0]]]. subst rest1. subst j.
      replace (List.length (prefix ++ ["-"%char])) with (S (List.length prefix)) by (rewrite length_app; simpl; lia).
      subst n0. simpl in En. subst n.
      rewrite (skipn_prefix_cons2 prefix rest0 "-"%char "0"%char).
      unfold parse_number. simpl.
      destruct (Ascii.eqb "0"%char "0"%char) eqn:E00.
      * simpl. reflexivity.
      * exfalso. assert (Ht : Ascii.eqb "0"%char "0"%char = true) by apply Ascii.eqb_refl. rewrite Ht in E00. discriminate.
    + (* - digit1-9 ... *)
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ "-"%char :: rest1) (ascii * list ascii) nat
        (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p))
        (Seq digit1_9_spec (Many digit_spec)) tt tt (S (List.length prefix)) j n0)) in Hd1.
      destruct Hd1 as [p [En0 Hseq]].
      apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ "-"%char :: rest1) ascii (list ascii)
        digit1_9_spec (Many digit_spec) tt tt (S (List.length prefix)) j p)) in Hseq.
      destruct Hseq as [γ2 [j2 [d [ds [[Ep Hd1'] Hmany]]]]].
      subst p. simpl in En0.
      unfold digit1_9_spec in Hd1'.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar (prefix ++ "-"%char :: rest1)
        (fun c : ascii => is_digit1_9b c = true) d tt γ2 (S (List.length prefix)) j2)) in Hd1'.
      destruct Hd1' as [[[Egt Ejt] Hnth] HP].
      subst γ2. subst j2.
      rewrite (nth_error_app_cons2 "-"%char prefix rest1) in Hnth.
      destruct rest1 as [| d' rest1']; [simpl in Hnth; discriminate | simpl in Hnth; injection Hnth as Hdd; subst d'].
      pose proof (take_digits_complete (prefix ++ "-"%char :: d :: rest1') (S (S (List.length prefix))) j ds Hmany Hnd) as Htd.
      rewrite (skipn_prefix_cons2 prefix rest1' "-"%char d) in Htd.
      subst n0. simpl in En. subst n.
      unfold parse_number. simpl.
      destruct (Ascii.eqb d "0"%char) eqn:E0.
      * exfalso. apply Ascii.eqb_eq in E0. subst d. simpl in HP. discriminate.
      * destruct (is_digit1_9b d) eqn:E19.
        -- rewrite Htd. simpl. reflexivity.
        -- discriminate.
  - (* ---------- non-negative ---------- *)
    apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) bool false tt (List.length prefix) neg γ1 j1)) in Hfalse.
    destruct Hfalse as [[Eneg Eg] Ej]. subst neg. subst γ1. subst j1.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) nat Z
      (fun n0 : nat => Z.of_nat n0) int_spec tt tt (List.length prefix) j n)) in Hn.
    destruct Hn as [n0 [En Hint]].
    unfold int_spec in Hint.
    apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) nat
      (Map (fun _ : unit => 0) (char "0"%char))
      (Map (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec)))
      tt tt (List.length prefix) j n0)) in Hint.
    destruct Hint as [Hz | Hd1].
    + (* 0 *)
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit nat
        (fun _ : unit => 0) (char "0"%char) tt tt (List.length prefix) j n0)) in Hz.
      destruct Hz as [u0 [Ez Hc0]].
      apply (char_head_cons "0"%char prefix w u0 tt j) in Hc0.
      destruct Hc0 as [rest0 [Ew0 [Eg0 Ej0]]]. subst w. subst j.
      subst n0. simpl in En. subst n.
      rewrite (skipn_prefix_cons prefix rest0 "0"%char).
      unfold parse_number. simpl.
      destruct (Ascii.eqb "0"%char "-"%char) eqn:E0m.
      * exfalso. apply Ascii.eqb_eq in E0m. discriminate.
      * simpl. destruct (Ascii.eqb "0"%char "0"%char) eqn:E00.
        -- simpl. reflexivity.
        -- exfalso. assert (Ht : Ascii.eqb "0"%char "0"%char = true) by apply Ascii.eqb_refl. rewrite Ht in E00. discriminate.
    + (* digit1-9 ... *)
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (ascii * list ascii) nat
        (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p))
        (Seq digit1_9_spec (Many digit_spec)) tt tt (List.length prefix) j n0)) in Hd1.
      destruct Hd1 as [p [En0 Hseq]].
      apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) ascii (list ascii)
        digit1_9_spec (Many digit_spec) tt tt (List.length prefix) j p)) in Hseq.
      destruct Hseq as [γ2 [j2 [d [ds [[Ep Hd1'] Hmany]]]]].
      subst p. simpl in En0.
      unfold digit1_9_spec in Hd1'.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar (prefix ++ w)
        (fun c : ascii => is_digit1_9b c = true) d tt γ2 (List.length prefix) j2)) in Hd1'.
      destruct Hd1' as [[[Egt Ejt] Hnth] HP].
      subst γ2. subst j2.
      destruct w as [| d' rest0].
      - rewrite app_nil_r in Hnth. rewrite (nth_error_self_none prefix) in Hnth. discriminate.
      - rewrite (nth_error_app_cons d' prefix rest0) in Hnth. injection Hnth as Hdd. subst d'.
      pose proof (take_digits_complete (prefix ++ d :: rest0) (S (List.length prefix)) j ds Hmany Hnd) as Htd.
      rewrite (skipn_prefix_cons prefix rest0 d) in Htd.
      subst n0. simpl in En. subst n.
      unfold parse_number. simpl.
      destruct (Ascii.eqb d "-"%char) eqn:E0m.
      * exfalso. apply Ascii.eqb_eq in E0m. subst d. simpl in HP. discriminate.
      * simpl. destruct (Ascii.eqb d "0"%char) eqn:E0.
        -- exfalso. apply Ascii.eqb_eq in E0. subst d. simpl in HP. discriminate.
        -- destruct (is_digit1_9b d) eqn:E19.
           ++ rewrite Htd. simpl. reflexivity.
           ++ discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* Mutual completeness: value / object / array, well-founded on input length.  *)
(* ------------------------------------------------------------------------- *)

Lemma wf_lt_length : well_founded (fun (w w' : list ascii) => List.length w < List.length w').
Proof.
  intro w. remember (List.length w) as n eqn:Hn.
  revert w Hn. induction n as [n IH] using (well_founded_induction lt_wf).
  intros w Hn. constructor. intros w' Hlt.
  rewrite <- Hn in Hlt. apply (IH (List.length w') Hlt w' eq_refl).
Qed.

Lemma digit1_9_digit (c : ascii) : is_digit1_9b c = true -> is_digitb c = true.
Proof.
  unfold is_digitb, is_digit1_9b. intro H.
  destruct (Ascii.eqb c "0") eqn:E0.
  - simpl. reflexivity.
  - simpl. exact H.
Qed.

Lemma number_head (prefix w : list ascii) (n : Z) (j : nat) :
  denote json_grammar (prefix ++ w) number_spec tt (List.length prefix) n tt j ->
  { c : ascii & { rest : list ascii & w = c :: rest /\ (is_digitb c || Ascii.eqb c "-")%bool = true } }.
Proof.
  intros Hd. unfold number_spec in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) bool Z (Alt (Map (fun _ : unit => true) (char "-")) (Pure false)) (fun neg : bool => Map (fun n0 : nat => if neg then Z.opp (Z.of_nat n0) else Z.of_nat n0) int_spec) tt tt (List.length prefix) j n)) in Hd.
  destruct Hd as [γ1 [j1 [neg [Hneg Hn]]]].
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) bool (Map (fun _ : unit => true) (char "-")) (Pure false) tt γ1 (List.length prefix) j1 neg)) in Hneg.
  destruct Hneg as [Hdash | Hfalse].
  - apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => true) (char "-") tt γ1 (List.length prefix) j1 neg)) in Hdash.
    destruct Hdash as [u [E Hc]].
    apply (char_head_cons "-"%char prefix w u γ1 j1) in Hc.
    destruct Hc as [rest [Ew [Eg Ej]]]. subst γ1. subst j1. destruct u.
    exists "-"%char, rest. split; [exact Ew | simpl; reflexivity].
  - apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) bool false tt (List.length prefix) neg γ1 j1)) in Hfalse.
    destruct Hfalse as [[Eneg Eg] Ej]. subst neg. subst γ1. subst j1.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) nat Z (fun n0 : nat => Z.of_nat n0) int_spec tt tt (List.length prefix) j n)) in Hn.
    destruct Hn as [n0 [En Hint]].
    unfold int_spec in Hint.
    apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) nat (Map (fun _ : unit => 0) (char "0")) (Map (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec))) tt tt (List.length prefix) j n0)) in Hint.
    destruct Hint as [Hz | Hd1].
    + apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit nat (fun _ : unit => 0) (char "0") tt tt (List.length prefix) j n0)) in Hz.
      destruct Hz as [u0 [Ez Hc0]].
      apply (char_head_cons "0"%char prefix w u0 tt j) in Hc0.
      destruct Hc0 as [rest [Ew [Eg Ej]]]. subst j. destruct u0.
      exists "0"%char, rest. split; [exact Ew | simpl; reflexivity].
    + apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (ascii * list ascii) nat (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec)) tt tt (List.length prefix) j n0)) in Hd1.
      destruct Hd1 as [p [En0 Hseq]].
      apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) ascii (list ascii) digit1_9_spec (Many digit_spec) tt tt (List.length prefix) j p)) in Hseq.
      destruct Hseq as [γ2 [j2 [d [ds [[_ Hd1'] _]]]]].
      unfold digit1_9_spec in Hd1'.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar (prefix ++ w) (fun c : ascii => is_digit1_9b c = true) d tt γ2 (List.length prefix) j2)) in Hd1'.
      destruct Hd1' as [[[Egt Ejt] Hnth] HP].
      subst γ2. subst j2.
      destruct w as [| d' rest]; [rewrite app_nil_r in Hnth; rewrite (nth_error_self_none prefix) in Hnth; discriminate | rewrite (nth_error_app_cons d' prefix rest) in Hnth; injection Hnth as Hdd; subst d'].
      exists d, rest. split; [reflexivity |].
      simpl. rewrite (digit1_9_digit d HP). reflexivity.
Qed.

Opaque parse_number.
Lemma parse_value_digit (c : ascii) (rest : list ascii) (n : Z) (r : list ascii) :
  (is_digitb c || Ascii.eqb c "-")%bool = true ->
  parse_number (c :: rest) = Some (n, r) ->
  parse_value 1 (c :: rest) = Some (JNumber n, r).
Proof.
  intros Hdigit Hnum. unfold parse_value. simpl.
  destruct (Ascii.eqb c "{") eqn:E1.
  - exfalso. apply Ascii.eqb_eq in E1. subst c. simpl in Hdigit. discriminate.
  - simpl. destruct (Ascii.eqb c "[") eqn:E2.
    + exfalso. apply Ascii.eqb_eq in E2. subst c. simpl in Hdigit. discriminate.
    + simpl. destruct (Ascii.eqb c "034") eqn:E3.
      * exfalso. apply Ascii.eqb_eq in E3. subst c. simpl in Hdigit. discriminate.
      * simpl. destruct (Ascii.eqb c "t") eqn:E4.
        -- exfalso. apply Ascii.eqb_eq in E4. subst c. simpl in Hdigit. discriminate.
        -- simpl. destruct (Ascii.eqb c "f") eqn:E5.
           ++ exfalso. apply Ascii.eqb_eq in E5. subst c. simpl in Hdigit. discriminate.
           ++ simpl. destruct (Ascii.eqb c "n") eqn:E6.
              ** exfalso. apply Ascii.eqb_eq in E6. subst c. simpl in Hdigit. discriminate.
              ** simpl. rewrite Hdigit. rewrite Hnum. simpl. reflexivity.
Qed.
Transparent parse_number.

Lemma denote_ge_json (w : list ascii) (A : Type) (s : Spec ascii unit json_nt A) (γ γ' : unit) (i j : nat) (a : A) :
  denote json_grammar w s γ i a γ' j -> i <= j.
Proof.
  intros d. induction d; simpl; lia.
Qed.


Lemma ws_not_digit (c : ascii) : is_wsb c = true -> is_digitb c = false.
Proof.
  unfold is_wsb, is_digitb. intro H.
  apply Bool.orb_prop in H. destruct H as [H | H].
  - apply Bool.orb_prop in H. destruct H as [H | H].
    + apply Bool.orb_prop in H. destruct H as [H | H].
      * apply Ascii.eqb_eq in H. subst c. reflexivity.
      * apply Ascii.eqb_eq in H. subst c. reflexivity.
    + apply Ascii.eqb_eq in H. subst c. reflexivity.
  - apply Ascii.eqb_eq in H. subst c. reflexivity.
Qed.

Lemma ws_head_char (w : list ascii) (i j : nat) (c : ascii) :
  denote json_grammar w ws tt i tt tt j ->
  i < j ->
  nth_error w i = Some c -> is_wsb c = true.
Proof.
  intros Hd Hlt Hnth. unfold ws in Hd.
  apply (fst (denote_map_iff ascii unit json_nt json_grammar w (list ascii) unit (fun _ : list ascii => tt) (Many (Tok (fun c : ascii => is_wsb c = true))) tt tt i j tt)) in Hd.
  destruct Hd as [wsl [_ Hmany]].
  destruct wsl as [| c0 wsl].
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i j (@nil ascii))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[_ _] Ej]. subst. lia.
    + destruct Hcons as [a [as' [γ'' [k [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i j (c0 :: wsl))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E Hone] _]]]]].
      injection E as Ea Eas. subst a as'.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar w (fun c : ascii => is_wsb c = true) c0 tt γ'' i k)) in Hone.
      destruct Hone as [[[_ _] Hnth'] HP].
      rewrite Hnth' in Hnth. injection Hnth as Hc. subst c0. exact HP.
Qed.
Lemma skip_ws_nonws (w : list ascii) (i : nat) (c : ascii) :
  nth_error w i = Some c -> is_wsb c = false -> skip_ws (skipn i w) = skipn i w.
Proof.
  intros Hnth Hnw.
  rewrite (skipn_cons_head ascii w i c Hnth).
  unfold skip_ws, ws_part. cbn. rewrite Hnw. reflexivity.
Qed.

Lemma ws_part_skipn (w : list ascii) (n : nat) :
  n <= List.length (ws_part w) -> skipn n (ws_part w) = ws_part (skipn n w).
Proof.
  revert n. induction w as [| c w' IH]; intros n Hn; cbn [ws_part skipn] in *.
  - destruct n; reflexivity.
  - destruct (is_wsb c) eqn:E; cbn [ws_part skipn] in Hn.
    + destruct n as [| n']; cbn [ws_part skipn].
      * rewrite E. reflexivity.
      * apply IH. assert (Hn' : n' <= List.length (ws_part w')) by (simpl in Hn; lia). exact Hn'.
    + destruct n; cbn [ws_part skipn]; [rewrite E; reflexivity | simpl in Hn; lia].
Qed.



Lemma ws_part_char_ws (w : list ascii) (m : nat) (c : ascii) :
  m < List.length (ws_part w) -> nth_error w m = Some c -> is_wsb c = true.
Proof.

  revert m c. induction w as [| c0 w' IH]; intros m c Hm Hnth; simpl in *.
  - lia.
  - destruct (is_wsb c0) eqn:E; simpl in Hm.
    + destruct m as [| m']; simpl in Hnth.
      * injection Hnth as Hc. subst c. exact E.
      * apply (IH m' c); [lia | exact Hnth].
    + lia.
Qed.

Lemma ws_denote_j (w : list ascii) (i j : nat) :
  denote json_grammar w ws tt i tt tt j ->
  j <= i + List.length (ws_part (skipn i w)).
Proof.
  intros Hd. unfold ws in Hd.
  apply (fst (denote_map_iff ascii unit json_nt json_grammar w (list ascii) unit (fun _ : list ascii => tt) (Many (Tok (fun c : ascii => is_wsb c = true))) tt tt i j tt)) in Hd.
  destruct Hd as [wsl [_ Hmany]].
  revert i j Hmany. induction wsl as [| c wsl IH]; intros i j Hmany.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i j (@nil ascii))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[_ _] Ej]. subst. lia.
    + destruct Hcons as [a [as' [γ'' [k [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i j (c :: wsl))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
      injection E as Ea Eas. subst a as'.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar w (fun c : ascii => is_wsb c = true) c tt γ'' i k)) in Hone.
      destruct Hone as [[[Eg Ej] Hnth] HP]. subst γ''. subst k.
      specialize (IH (S i) j Htail).
      rewrite (skipn_cons_head ascii w i c Hnth). simpl. rewrite HP. simpl.
      set (X := List.length (ws_part (skipn (S i) w))) in *.
      apply (Nat.le_trans j (S i + X) (i + S X) IH).
      rewrite (Nat.add_succ_comm i X). reflexivity.
Qed.

Lemma ws_concat (w : list ascii) (i k j : nat) :
  denote json_grammar w ws tt i tt tt k ->
  denote json_grammar w ws tt k tt tt j ->
  denote json_grammar w ws tt i tt tt j.
Proof.
  intros H1 H2. unfold ws in H1, H2.
  apply (fst (denote_map_iff ascii unit json_nt json_grammar w (list ascii) unit (fun _ : list ascii => tt) (Many (Tok (fun c : ascii => is_wsb c = true))) tt tt i k tt)) in H1.
  destruct H1 as [wsl1 [_ Hm1]].
  apply (fst (denote_map_iff ascii unit json_nt json_grammar w (list ascii) unit (fun _ : list ascii => tt) (Many (Tok (fun c : ascii => is_wsb c = true))) tt tt k j tt)) in H2.
  destruct H2 as [wsl2 [_ Hm2]].
  apply d_map with (a := wsl1 ++ wsl2).
  revert Hm1 Hm2. revert i k j.
  induction wsl1 as [| c wsl1 IH]; intros i k j Hm1 Hm2.
  - simpl. apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i k (@nil ascii))) in Hm1.
    destruct Hm1 as [Hnil | Hcons].
    + destruct Hnil as [[_ _] Ek]. subst. exact Hm2.
    + destruct Hcons as [a [as' [γ'' [k' [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i k (c :: wsl1))) in Hm1.
    destruct Hm1 as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k' [[E Hone] Htail]]]]].
      injection E as Ea Eas. subst a as'. destruct γ''.
      apply d_many_cons with (γ' := tt) (j := k').
      * exact Hone.
      * simpl. apply (IH k' k j Htail Hm2).
Qed.

Lemma ws_denote_ge (w : list ascii) (i j : nat) :
  denote json_grammar w ws tt i tt tt j -> i <= j.
Proof.
  intros Hd. unfold ws in Hd.
  apply (fst (denote_map_iff ascii unit json_nt json_grammar w (list ascii) unit (fun _ : list ascii => tt) (Many (Tok (fun c : ascii => is_wsb c = true))) tt tt i j tt)) in Hd.
  destruct Hd as [wsl [_ Hmany]].
  revert i j Hmany. induction wsl as [| c wsl IH]; intros i j Hmany.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i j (@nil ascii))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[_ _] Ej]. subst. lia.
    + destruct Hcons as [a [as' [γ'' [k [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt i j (c :: wsl))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E Hone] Htail]]]]].
      injection E as Ea Eas. subst a as'.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar w (fun c : ascii => is_wsb c = true) c tt γ'' i k)) in Hone.
      destruct Hone as [[[Eg Ej] Hnth] HP]. subst γ''. subst k.
      specialize (IH (S i) j Htail). lia.
Qed.

Lemma skip_ws_ws (w : list ascii) (i j : nat) :
  denote json_grammar w ws tt i tt tt j ->
  skip_ws (skipn i w) = skip_ws (skipn j w).
Proof.
  intros Hd.
  pose proof (ws_denote_j w i j Hd) as Hle.
  pose proof (ws_denote_ge w i j Hd) as Hge.
  assert (Hle' : j - i <= List.length (ws_part (skipn i w))) by lia.
  rewrite <- (skipn_length_app ascii (ws_part (skipn i w)) (skip_ws (skipn i w))).
  rewrite <- (skipn_length_app ascii (ws_part (skipn j w)) (skip_ws (skipn j w))).
  rewrite (ws_part_skip (skipn i w)). rewrite (ws_part_skip (skipn j w)).
  rewrite <- (firstn_skipn (j - i) (ws_part (skipn i w))).
  rewrite length_app. rewrite firstn_length.
  rewrite (Nat.min_l (j - i) (List.length (ws_part (skipn i w))) Hle').
  rewrite (ws_part_skipn (skipn i w) (j - i) Hle').
  rewrite (skipn_skipn (j - i) i w). replace ((j - i) + i) with j by lia.
  replace ((j - i) + List.length (ws_part (skipn j w))) with (List.length (ws_part (skipn j w)) + (j - i)) by lia.
  rewrite <- (skipn_skipn (List.length (ws_part (skipn j w))) (j - i) (skipn i w)).
  rewrite (skipn_skipn (j - i) i w). replace ((j - i) + i) with j by lia.
  reflexivity.
Qed.


Lemma ws_ws_skip (prefix w : list ascii) (j1 j3 : nat) :
  denote json_grammar (prefix ++ w) ws tt (List.length prefix) tt tt j1 ->
  denote json_grammar (prefix ++ w) ws tt j1 tt tt j3 ->
  (forall c : ascii, nth_error (prefix ++ w) j3 = Some c -> is_wsb c = false) ->
  skip_ws w = skipn j3 (prefix ++ w).
Proof.
  intros H1 H2 Hnonws.
  pose proof (ws_concat (prefix ++ w) (List.length prefix) j1 j3 H1 H2) as Hws.
  pose proof (ws_denote_j (prefix ++ w) (List.length prefix) j3 Hws) as Hle.
  rewrite (skipn_length_app ascii prefix w) in Hle.
  pose proof (ws_denote_ge (prefix ++ w) (List.length prefix) j3 Hws) as Hge_j3.
  assert (Hj3 : j3 = List.length prefix + List.length (ws_part w)).
  { assert (Hge : List.length (ws_part w) <= j3 - List.length prefix).
    { destruct (Nat.lt_ge_cases (j3 - List.length prefix) (List.length (ws_part w))) as [Hlt | Hge']; [| exact Hge'].
      exfalso.
      assert (Hltw : j3 - List.length prefix < List.length w).
      { assert (Hwslen : List.length (ws_part w) <= List.length w).
        { clear. induction w; simpl; [lia |]. destruct (is_wsb a) eqn:E; simpl; lia. }
        lia. }
      destruct (nth_error w (j3 - List.length prefix)) as [c |] eqn:E.
      - pose proof (ws_part_char_ws w (j3 - List.length prefix) c Hlt E) as Hwc.
        assert (Hnthj3 : nth_error (prefix ++ w) j3 = Some c).
        { rewrite (nth_error_app2 prefix w Hge_j3). exact E. }
        apply (Hnonws c) in Hnthj3. rewrite Hwc in Hnthj3. discriminate.

      - apply nth_error_None in E. lia. }
    lia. }
  rewrite Hj3.
  replace (prefix ++ w) with (prefix ++ ws_part w ++ skip_ws w) by (rewrite (ws_part_skip w); reflexivity).
  rewrite app_assoc.
  rewrite <- (length_app prefix (ws_part w)).
  rewrite (skipn_length_app ascii (prefix ++ ws_part w) (skip_ws w)).
  reflexivity.
Qed.

Lemma ws_skip (prefix w : list ascii) (j : nat) :
  denote json_grammar (prefix ++ w) ws tt (List.length prefix) tt tt j ->
  (forall c : ascii, nth_error (prefix ++ w) j = Some c -> is_wsb c = false) ->
  skip_ws w = skipn j (prefix ++ w).
Proof.
  intros H1 Hnonws.
  pose proof (ws_denote_j (prefix ++ w) (List.length prefix) j H1) as Hle.
  rewrite (skipn_length_app ascii prefix w) in Hle.
  pose proof (ws_denote_ge (prefix ++ w) (List.length prefix) j H1) as Hge_j.
  assert (Hj : j = List.length prefix + List.length (ws_part w)).
  { assert (Hge : List.length (ws_part w) <= j - List.length prefix).
    { destruct (Nat.lt_ge_cases (j - List.length prefix) (List.length (ws_part w))) as [Hlt | Hge']; [| exact Hge'].
      exfalso.
      assert (Hltw : j - List.length prefix < List.length w).
      { assert (Hwslen : List.length (ws_part w) <= List.length w).
        { clear. induction w; simpl; [lia |]. destruct (is_wsb a) eqn:E; simpl; lia. }
        lia. }
      destruct (nth_error w (j - List.length prefix)) as [c |] eqn:E.
      - pose proof (ws_part_char_ws w (j - List.length prefix) c Hlt E) as Hwc.
        assert (Hnthj : nth_error (prefix ++ w) j = Some c).
        { rewrite (nth_error_app2 prefix w Hge_j). exact E. }
        apply (Hnonws c) in Hnthj. rewrite Hwc in Hnthj. discriminate.
      - apply nth_error_None in E. lia. }
    lia. }
  rewrite Hj.
  replace (prefix ++ w) with (prefix ++ ws_part w ++ skip_ws w) by (rewrite (ws_part_skip w); reflexivity).
  rewrite app_assoc. rewrite <- (length_app prefix (ws_part w)).
  rewrite (skipn_length_app ascii (prefix ++ ws_part w) (skip_ws w)). reflexivity.
Qed.

Lemma ws_skip_j (prefix w : list ascii) (j : nat) :
  denote json_grammar (prefix ++ w) ws tt (List.length prefix) tt tt j ->
  (forall c : ascii, nth_error (prefix ++ w) j = Some c -> is_wsb c = false) ->
  j = List.length prefix + List.length (ws_part w).
Proof.
  intros H1 Hnonws.
  pose proof (ws_denote_j (prefix ++ w) (List.length prefix) j H1) as Hle.
  rewrite (skipn_length_app ascii prefix w) in Hle.
  pose proof (ws_denote_ge (prefix ++ w) (List.length prefix) j H1) as Hge_j.
  assert (Hge : List.length (ws_part w) <= j - List.length prefix).
  { destruct (Nat.lt_ge_cases (j - List.length prefix) (List.length (ws_part w))) as [Hlt | Hge']; [| exact Hge'].
    exfalso.
    assert (Hltw : j - List.length prefix < List.length w).
    { assert (Hwslen : List.length (ws_part w) <= List.length w) by (clear; induction w; simpl; [lia |]; destruct (is_wsb a) eqn:E; simpl; lia).
      lia. }
    destruct (nth_error w (j - List.length prefix)) as [c |] eqn:E.
    - pose proof (ws_part_char_ws w (j - List.length prefix) c Hlt E) as Hwc.
      assert (Hnthj : nth_error (prefix ++ w) j = Some c).
      { rewrite (nth_error_app2 prefix w Hge_j). exact E. }
      apply (Hnonws c) in Hnthj. rewrite Hwc in Hnthj. discriminate.
    - apply nth_error_None in E. lia. }
  lia.
Qed.
Lemma ws_skip_gen (w : list ascii) (i j : nat) :
  denote json_grammar w ws tt i tt tt j ->
  (forall c : ascii, nth_error w j = Some c -> is_wsb c = false) ->
  skip_ws (skipn i w) = skipn j w.
Proof.
  intros H1 Hnonws.
  pose proof (ws_denote_j w i j H1) as Hle.
  pose proof (ws_denote_ge w i j H1) as Hge_j.
  assert (Hj : j = i + List.length (ws_part (skipn i w))).
  { assert (Hge : List.length (ws_part (skipn i w)) <= j - i).
    { destruct (Nat.lt_ge_cases (j - i) (List.length (ws_part (skipn i w)))) as [Hlt | Hge']; [| exact Hge'].
      exfalso.
      assert (Hltw : j - i < List.length (skipn i w)).
      { assert (Hwslen : List.length (ws_part (skipn i w)) <= List.length (skipn i w)).
        { clear. induction (skipn i w); simpl; [lia |]. destruct (is_wsb a) eqn:E; simpl; lia. }
        lia. }
      assert (Hi_len : i <= List.length w) by (rewrite (skipn_length i w) in Hltw; lia).
      destruct (nth_error (skipn i w) (j - i)) as [c |] eqn:E.
      - pose proof (ws_part_char_ws (skipn i w) (j - i) c Hlt E) as Hwc.
        assert (Hnthj : nth_error w j = Some c).
        { rewrite <- (firstn_skipn i w). rewrite (nth_error_app2 (firstn i w) (skipn i w)).
          - replace (j - Datatypes.length (firstn i w)) with (j - i) by (rewrite firstn_length; rewrite (Nat.min_l i (Datatypes.length w) Hi_len); reflexivity).
            exact E.
          - rewrite firstn_length. lia. }
        apply (Hnonws c) in Hnthj. rewrite Hwc in Hnthj. discriminate.
      - apply nth_error_None in E. lia. }
    lia. }
  rewrite Hj.
  rewrite Nat.add_comm.
  rewrite <- (skipn_skipn (List.length (ws_part (skipn i w))) i w).
  rewrite <- (skipn_length_app ascii (ws_part (skipn i w)) (skip_ws (skipn i w))).
  f_equal. rewrite (ws_part_skip (skipn i w)). reflexivity.
Qed.
(* The one generic loop lemma: `sep_by A elem_parser sep closer` is complete for
   `Many (Map snd (Seq (char sep) (Bind ws (Bind elem (Bind ws (Pure)))))`.
   Instantiated once for members (`sep = ","`, `closer = "}"`) and once for
   elements (`sep = ","`, `closer = "]"`), replacing the two hand-written
   `Hfold`s in `complete_value_object_array`. *)
Lemma sep_by_complete (A : Type) (elem : Spec ascii unit json_nt A)
  (elem_parser : nat -> list ascii -> option (A * list ascii)) (sep closer : ascii) :
  (forall (fuel fuel' : nat) (w : list ascii) (r : A * list ascii),
     fuel <= fuel' -> elem_parser fuel w = Some r -> elem_parser fuel' w = Some r) ->
  (forall (prefix w : list ascii) (a : A) (j : nat),
     denote json_grammar (prefix ++ w) elem tt (List.length prefix) a tt j ->
     List.length prefix < j) ->
  is_wsb sep = false ->
  is_wsb closer = false ->
  Ascii.eqb sep closer = false ->
  is_digitb sep = false ->
  is_digitb closer = false ->
  forall (w : list ascii),
    (forall (w' : list ascii), List.length w' < List.length w -> forall (prefix : list ascii) (a : A) (j : nat),
       denote json_grammar (prefix ++ w') elem tt (List.length prefix) a tt j ->
       (forall c : ascii, nth_error (prefix ++ w') j = Some c -> is_digitb c = false) ->
       elem_parser (3 * List.length w' + 1) (skip_ws w') = Some (a, skipn j (prefix ++ w'))) ->
    forall (prefix : list ascii) (xs : list A) (j jclose : nat),
      denote json_grammar (prefix ++ w)
        (Many (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a : A => Bind ws (fun _ : unit => Pure a)))))))
        tt (List.length prefix) xs tt j ->
      denote json_grammar (prefix ++ w) ws tt j tt tt jclose ->
      nth_error (prefix ++ w) jclose = Some closer ->
      sep_by A elem_parser sep closer (3 * List.length w + 2) (skip_ws w) = Some (xs, skipn jclose (prefix ++ w)).
Proof.
  intros Helem_mono Helem_cons Hsep_nw Hcloser_nw Hsep_closer Hsep_ndigit Hcloser_ndigit.
  apply (@well_founded_induction_type (list ascii) (fun x y : list ascii => List.length x < List.length y) wf_lt_length
    (fun w : list ascii =>
      (forall (w' : list ascii), List.length w' < List.length w -> forall (prefix : list ascii) (a : A) (j : nat),
         denote json_grammar (prefix ++ w') elem tt (List.length prefix) a tt j ->
         (forall c : ascii, nth_error (prefix ++ w') j = Some c -> is_digitb c = false) ->
         elem_parser (3 * List.length w' + 1) (skip_ws w') = Some (a, skipn j (prefix ++ w'))) ->
      forall (prefix : list ascii) (xs : list A) (j jclose : nat),
        denote json_grammar (prefix ++ w)
          (Many (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a : A => Bind ws (fun _ : unit => Pure a)))))))
          tt (List.length prefix) xs tt j ->
        denote json_grammar (prefix ++ w) ws tt j tt tt jclose ->
        nth_error (prefix ++ w) jclose = Some closer ->
        sep_by A elem_parser sep closer (3 * List.length w + 2) (skip_ws w) = Some (xs, skipn jclose (prefix ++ w)))).
  intros w IH Helem_c prefix xs j jclose Hmany Hws Hnth.
  apply (fst (denote_many_iff ascii unit json_nt json_grammar (prefix ++ w) A
    (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a : A => Bind ws (fun _ : unit => Pure a))))))
    tt tt (List.length prefix) j xs)) in Hmany.
  destruct Hmany as [Hnil | Hcons].
  - (* no repetitions *)
    destruct Hnil as [[Exs _] Ej]. subst xs. subst j.
    assert (Hnonws : forall c : ascii, nth_error (prefix ++ w) jclose = Some c -> is_wsb c = false).
    { intros c Hc. rewrite Hnth in Hc. injection Hc as Hc'. subst c. exact Hcloser_nw. }
    pose proof (ws_skip prefix w jclose Hws Hnonws) as Hskip.
    replace (3 * List.length w + 2) with (S (3 * List.length w + 1)) by lia.
    cbn [sep_by].
    rewrite Hskip. rewrite (skipn_cons_head ascii (prefix ++ w) jclose closer Hnth).
    cbn [Ascii.eqb]. rewrite (proj2 (Ascii.eqb_eq closer closer) eq_refl). reflexivity.
  - (* one or more repetitions *)
    destruct Hcons as [a [xs' [γ'' [k [[Exs Hone] Htail]]]]]. subst xs.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * A) A snd
      (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a0 : A => Bind ws (fun _ : unit => Pure a0)))))
      tt γ'' (List.length prefix) k a)) in Hone.
    destruct Hone as [p [Ea Hseq]].
    apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit A (char sep)
      (Bind ws (fun _ : unit => Bind elem (fun a0 : A => Bind ws (fun _ : unit => Pure a0))))
      tt γ'' (List.length prefix) k p)) in Hseq.
    destruct Hseq as [γc [jc [u [b [[Ep Hsep] Hrest]]]]].
    apply (char_denote_nth (prefix ++ w) sep (List.length prefix) jc u γc) in Hsep.
    destruct Hsep as [Hnth_sep [Eu [Egc Ejc]]]. subst u. subst γc. subst jc.
    simpl in Ep. subst p. simpl in Ea. subst b.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit A ws
      (fun _ : unit => Bind elem (fun a0 : A => Bind ws (fun _ : unit => Pure a0)))
      tt γ'' (S (List.length prefix)) k a)) in Hrest.
    destruct Hrest as [γm [jm [u2 [Hws_sep Hrest2]]]]. destruct u2, γm.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) A A elem
      (fun a0 : A => Bind ws (fun _ : unit => Pure a0))
      tt γ'' jm k a)) in Hrest2.
    destruct Hrest2 as [γe [je [a0 [Helem Hws_after]]]]. destruct γe.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit A ws
      (fun _ : unit => Pure a0) tt γ'' je k a)) in Hws_after.
    destruct Hws_after as [γw2 [jw2 [u3 [Hws_mid Hpure]]]]. destruct u3, γw2.
    apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) A a0 tt jw2 a γ'' k)) in Hpure.
    destruct Hpure as [[Ea0 Eg] Ej]. subst a. subst k. subst γ''.
    (* now: Hnth_sep, Hws_sep (S(length prefix)..jm), Helem (jm..je, a0), Hws_mid (je..jw2),
       Htail (jw2..j, xs'), Hws (j..jclose), Hnth (jclose, closer). *)
    assert (Hjm_le : jm <= List.length (prefix ++ w)).
    { pose proof (denote_ge_json (prefix ++ w) A elem tt tt jm je a0 Helem) as Hg1.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt je jw2 tt Hws_mid) as Hg2.
      pose proof (denote_ge_json (prefix ++ w) (list A) (Many (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a1 : A => Bind ws (fun _ : unit => Pure a1))))))) tt tt jw2 j xs' Htail) as Hg3.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt j jclose tt Hws) as Hg4.
      assert (Hjc_lt : jclose < List.length (prefix ++ w)) by (apply (nth_error_Some (prefix ++ w) jclose); rewrite Hnth; discriminate).
      lia. }
    (* the element parser succeeds on the first element *)
    assert (Helem' : denote json_grammar (firstn jm (prefix ++ w) ++ skipn jm (prefix ++ w)) elem tt (List.length (firstn jm (prefix ++ w))) a0 tt je).
    { rewrite (firstn_skipn jm (prefix ++ w)). rewrite firstn_length. rewrite (Nat.min_l jm (List.length (prefix ++ w)) Hjm_le). exact Helem. }
    assert (Hlt_elem : List.length (skipn jm (prefix ++ w)) < List.length w).
    { rewrite (skipn_length jm (prefix ++ w)). rewrite length_app. rewrite length_app in Hjm_le.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt (S (List.length prefix)) jm tt Hws_sep) as Hg.
      lia. }
    assert (Hnodigit_je : forall c : ascii, nth_error (firstn jm (prefix ++ w) ++ skipn jm (prefix ++ w)) je = Some c -> is_digitb c = false).
    { intros c Hc. rewrite (firstn_skipn jm (prefix ++ w)) in Hc.
      destruct (Nat.lt_ge_cases je jw2) as [Hlt | Hge].
      - pose proof (ws_head_char (prefix ++ w) je jw2 c Hws_mid Hlt Hc) as Hwc. apply (ws_not_digit c Hwc).
      - assert (Hjej : je = jw2) by (pose proof (denote_ge_json (prefix ++ w) unit ws tt tt je jw2 tt Hws_mid) as Hg; lia). subst jw2.
        apply (fst (denote_many_iff ascii unit json_nt json_grammar (prefix ++ w) A
          (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a1 : A => Bind ws (fun _ : unit => Pure a1))))))
          tt tt je j xs')) in Htail.
        destruct Htail as [Hnil | Hcons2].
        + destruct Hnil as [[_ _] Ej]. subst j.
          destruct (Nat.lt_ge_cases je jclose) as [Hlt2 | Hge2].
          * pose proof (ws_head_char (prefix ++ w) je jclose c Hws Hlt2 Hc) as Hwc. apply (ws_not_digit c Hwc).
          * assert (Hjec : je = jclose) by (pose proof (denote_ge_json (prefix ++ w) unit ws tt tt je jclose tt Hws) as Hg; lia). subst jclose. rewrite Hnth in Hc. injection Hc as Hc'. subst c. exact Hcloser_ndigit.
        + destruct Hcons2 as [a1 [xs'' [γr [jr [[_ Hs_rest] _]]]]].
          apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * A) A snd
            (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a2 : A => Bind ws (fun _ : unit => Pure a2)))))
            tt γr je jr a1)) in Hs_rest.
          destruct Hs_rest as [p2 [_ Hseq2]].
          apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit A (char sep)
            (Bind ws (fun _ : unit => Bind elem (fun a2 : A => Bind ws (fun _ : unit => Pure a2))))
            tt γr je jr p2)) in Hseq2.
          destruct Hseq2 as [γc2 [jc2 [u4 [b2 [[_ Hsep2] _]]]]].
          apply (char_denote_nth (prefix ++ w) sep je jc2 u4 γc2) in Hsep2.
          destruct Hsep2 as [Hnth_sep2 _]. rewrite Hnth_sep2 in Hc. injection Hc as Hc'. subst c. exact Hsep_ndigit. }
    assert (Helem_parse : elem_parser (3 * List.length (skipn jm (prefix ++ w)) + 1) (skip_ws (skipn jm (prefix ++ w))) = Some (a0, skipn je (prefix ++ w))).
    { pose proof (Helem_c (skipn jm (prefix ++ w)) Hlt_elem (firstn jm (prefix ++ w)) a0 je Helem' Hnodigit_je) as Hh.
      rewrite (firstn_skipn jm (prefix ++ w)) in Hh. exact Hh. }
    (* pad the element parser's fuel up to 3*len + 1 *)
    assert (Helem_pad : elem_parser (3 * List.length w + 1) (skip_ws (skipn jm (prefix ++ w))) = Some (a0, skipn je (prefix ++ w))).
    { apply (Helem_mono (3 * List.length (skipn jm (prefix ++ w)) + 1) (3 * List.length w + 1) (skip_ws (skipn jm (prefix ++ w))) (a0, skipn je (prefix ++ w))).
      - rewrite (skipn_length jm (prefix ++ w)). rewrite length_app.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt (S (List.length prefix)) jm tt Hws_sep) as Hg.
        lia.
      - exact Helem_parse. }
    (* strict suffix for the recursion: the element consumes >= 1 char *)
    assert (Hjm_lt_je : jm < je).
    { pose proof (Helem_cons (firstn jm (prefix ++ w)) (skipn jm (prefix ++ w)) a0 je Helem') as Hh.
      rewrite firstn_length in Hh. rewrite (Nat.min_l jm (List.length (prefix ++ w)) Hjm_le) in Hh. exact Hh. }
    assert (Hlt_rec : List.length (skipn jw2 (prefix ++ w)) < List.length w).
    { rewrite (skipn_length jw2 (prefix ++ w)). rewrite length_app. rewrite length_app in Hjm_le.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt (S (List.length prefix)) jm tt Hws_sep) as Hg1.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt je jw2 tt Hws_mid) as Hg2.
      lia. }
    (* re-shape the tail for the recursive call *)
    assert (Htail' : denote json_grammar (firstn jw2 (prefix ++ w) ++ skipn jw2 (prefix ++ w))
      (Many (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a1 : A => Bind ws (fun _ : unit => Pure a1)))))))
      tt (List.length (firstn jw2 (prefix ++ w))) xs' tt j).
    { rewrite (firstn_skipn jw2 (prefix ++ w)). rewrite firstn_length. rewrite (Nat.min_l jw2 (List.length (prefix ++ w))).
      - exact Htail.
      - pose proof (denote_ge_json (prefix ++ w) (list A) (Many (Map snd (Seq (char sep) (Bind ws (fun _ : unit => Bind elem (fun a1 : A => Bind ws (fun _ : unit => Pure a1))))))) tt tt jw2 j xs' Htail) as Hg.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt j jclose tt Hws) as Hg0.
        assert (Hjc_lt : jclose < List.length (prefix ++ w)) by (apply (nth_error_Some (prefix ++ w) jclose); rewrite Hnth; discriminate).
        lia. }
    assert (Hws' : denote json_grammar (firstn jw2 (prefix ++ w) ++ skipn jw2 (prefix ++ w)) ws tt j tt tt jclose).
    { rewrite (firstn_skipn jw2 (prefix ++ w)). exact Hws. }
    assert (Hnth' : nth_error (firstn jw2 (prefix ++ w) ++ skipn jw2 (prefix ++ w)) jclose = Some closer).
    { rewrite (firstn_skipn jw2 (prefix ++ w)). exact Hnth. }
    pose proof (IH (skipn jw2 (prefix ++ w)) Hlt_rec (fun w' Hlt => Helem_c w' (Nat.lt_trans (Datatypes.length w') (Datatypes.length (skipn jw2 (prefix ++ w))) (Datatypes.length w) Hlt Hlt_rec)) (firstn jw2 (prefix ++ w)) xs' j jclose Htail' Hws' Hnth') as Hrest_parse.
    rewrite (firstn_skipn jw2 (prefix ++ w)) in Hrest_parse.
    (* pad the recursive call's fuel up to 3*len + 1 *)
    assert (Hrest_pad : sep_by A elem_parser sep closer (3 * List.length w + 1) (skip_ws (skipn jw2 (prefix ++ w))) = Some (xs', skipn jclose (prefix ++ w))).
    { apply (sep_by_mono A elem_parser sep closer Helem_mono (3 * List.length (skipn jw2 (prefix ++ w)) + 2) (3 * List.length w + 1) (skip_ws (skipn jw2 (prefix ++ w))) (xs', skipn jclose (prefix ++ w))).
      - rewrite (skipn_length jw2 (prefix ++ w)). rewrite length_app.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt (S (List.length prefix)) jm tt Hws_sep) as Hg1.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt je jw2 tt Hws_mid) as Hg2.
        lia.
      - exact Hrest_parse. }
    (* ws after the element is maximal, so skip_ws (skipn je ...) = skip_ws (skipn jw2 ...) *)
    pose proof (skip_ws_ws (prefix ++ w) je jw2 Hws_mid) as Hskip_mid.
    pose proof (skip_ws_ws (prefix ++ w) (S (List.length prefix)) jm Hws_sep) as Hskip_sep_ws.
    (* skip_ws w begins with the separator *)
    assert (Hskip_sep : skip_ws w = sep :: skipn (S (List.length prefix)) (prefix ++ w)).
    { rewrite <- (skipn_length_app ascii prefix w) at 1.
      pose proof (skip_ws_nonws (prefix ++ w) (List.length prefix) sep Hnth_sep Hsep_nw) as Hsw.
      rewrite Hsw.
      rewrite (skipn_cons_head ascii (prefix ++ w) (List.length prefix) sep Hnth_sep).
      reflexivity. }
    replace (3 * List.length w + 2) with (S (3 * List.length w + 1)) by lia.
    cbn [sep_by].
    rewrite Hskip_sep. cbn [Ascii.eqb].
    rewrite Hsep_closer. rewrite (proj2 (Ascii.eqb_eq sep sep) eq_refl).
    cbn [sep_by].
    rewrite Hskip_sep_ws. rewrite Helem_pad.
    cbn [sep_by Ascii.eqb].
    rewrite Hskip_mid. rewrite Hrest_pad.
    cbn [Ascii.eqb]. reflexivity.
Qed.


(* Bridge: a Call NT_value denotation is a value_spec denotation (the inverse of
   value_sound_call). *)
Lemma value_complete_call (prefix w : list ascii) (v : Json) (j : nat) :
  denote json_grammar (prefix ++ w) (Call NT_value) tt (List.length prefix) v tt j ->
  denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt j.
Proof.
  intros H.
  apply (fst (denote_call_iff ascii unit json_nt json_grammar (prefix ++ w) Json NT_value tt tt (List.length prefix) j v)) in H.
  cbn [json_grammar] in H. exact H.
Qed.

(* A value's input is non-ws at the head, so skip_ws is a no-op on it. *)
Lemma value_input_skip_ws (prefix w : list ascii) (v : Json) (j : nat) :
  denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt j ->
  skip_ws w = w.
Proof.
  intros Hd.
  destruct w as [| c rest]; [reflexivity |].
  unfold skip_ws.
  destruct (is_wsb c) eqn:Ews; [| reflexivity].
  exfalso. exact (value_no_ws prefix c rest v j Ews Hd).
Qed.

#[local] Definition Vst (w : list ascii) : Type :=
  forall (prefix : list ascii) (v : Json) (j : nat),
    denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt j ->
    (forall c : ascii, nth_error (prefix ++ w) j = Some c -> is_digitb c = false) ->
    sigT (fun fuel : nat => prod (fuel <= 3 * List.length w) (parse_value fuel w = Some (v, skipn j (prefix ++ w)))).
#[local] Definition Ost (w : list ascii) : Type :=
  forall (prefix : list ascii) (ms : list (list ascii * Json)) (j : nat),
    denote json_grammar (prefix ++ w) object_body_spec tt (List.length prefix) ms tt j ->
    sigT (fun fuel : nat => prod (fuel <= 3 * List.length w + 2) (parse_object fuel w = Some (ms, skipn j (prefix ++ w)))).
#[local] Definition Ast (w : list ascii) : Type :=
  forall (prefix : list ascii) (vs : list Json) (j : nat),
    denote json_grammar (prefix ++ w) array_body_spec tt (List.length prefix) vs tt j ->
    sigT (fun fuel : nat => prod (fuel <= 3 * List.length w + 2) (parse_array fuel w = Some (vs, skipn j (prefix ++ w)))).


Opaque parse_string parse_number parse_lit.
 (* Fuel monotonicity and bound for the recursive parsers. *)
Lemma parse_all_mono : forall fuel fuel',
  fuel <= fuel' ->
  (forall w r, parse_value fuel w = Some r -> parse_value fuel' w = Some r)
  * (forall w r, parse_object fuel w = Some r -> parse_object fuel' w = Some r)
  * (forall w r, parse_array fuel w = Some r -> parse_array fuel' w = Some r)
  * (forall w r, parse_members fuel w = Some r -> parse_members fuel' w = Some r)
  * (forall w r, parse_members_more fuel w = Some r -> parse_members_more fuel' w = Some r)
  * (forall w r, parse_elements fuel w = Some r -> parse_elements fuel' w = Some r)
  * (forall w r, parse_elements_more fuel w = Some r -> parse_elements_more fuel' w = Some r).
Proof.
  induction fuel as [| f IH]; intros fuel' Hle.
  { repeat split; intros w r H;
    cbn [parse_value parse_object parse_array parse_members parse_members_more parse_elements parse_elements_more] in H; discriminate. }
  destruct fuel' as [| f']; [lia |].
  assert (Hle' : f <= f') by lia.
  destruct (IH f' Hle') as [[[[[[IHv IHo] IHa] IHm] IHmm] IHe] IHem].
  repeat split; intros w r H.
  - (* parse_value *)
    cbn [parse_value] in H.
    destruct w as [| c rest]; cbn [parse_value] in H; try discriminate.
    cbn [parse_value].
    destruct (Ascii.eqb c "{"%char) eqn:E1.
    + destruct (parse_object f rest) as [[? ?] |] eqn:Eo; try discriminate.
      rewrite (IHo _ _ Eo). cbn. exact H.
    + destruct (Ascii.eqb c "["%char) eqn:E2.
      * destruct (parse_array f rest) as [[? ?] |] eqn:Ea; try discriminate.
        rewrite (IHa _ _ Ea). cbn. exact H.
      * destruct (Ascii.eqb c "034"%char) eqn:E3.
        -- destruct (parse_string (c :: rest)) as [[? ?] |] eqn:Es; try discriminate. exact H.
        -- destruct (Ascii.eqb c "t"%char) eqn:E4.
           ++ destruct (parse_lit "rue" rest) as [? |] eqn:El; try discriminate. exact H.
           ++ destruct (Ascii.eqb c "f"%char) eqn:E5.
              ** destruct (parse_lit "alse" rest) as [? |] eqn:El; try discriminate. exact H.
              ** destruct (Ascii.eqb c "n"%char) eqn:E6.
                 --+ destruct (parse_lit "ull" rest) as [? |] eqn:El; try discriminate. exact H.
                 --+ destruct (is_digitb c || Ascii.eqb c "-"%char) eqn:E7.
                     ---+ destruct (parse_number (c :: rest)) as [[? ?] |] eqn:En; try discriminate. exact H.
                     ---+ discriminate.
  - (* parse_object *)
    cbn [parse_object] in H.
    destruct (parse_members f (skip_ws w)) as [[ms rest] |] eqn:Em; cbn [parse_object] in H; try discriminate.
    cbn [parse_object].
    rewrite (IHm _ _ Em). cbn. exact H.
  - (* parse_array *)
    cbn [parse_array] in H.
    destruct (parse_elements f (skip_ws w)) as [[vs rest] |] eqn:Ee; cbn [parse_array] in H; try discriminate.
    cbn [parse_array].
    rewrite (IHe _ _ Ee). cbn. exact H.
  - (* parse_members *)
    cbn [parse_members] in H.
    destruct w as [| c rest]; cbn [parse_members] in H; try discriminate.
    cbn [parse_members].
    destruct (Ascii.eqb c "}"%char) eqn:E1.
    + exact H.
    + destruct (parse_string (c :: rest)) as [[s rest1] |] eqn:Es; try discriminate.
      destruct (skip_ws rest1) as [| c' rest2] eqn:Ew; try discriminate.
      destruct (Ascii.eqb c' ":"%char) eqn:E2.
      * destruct (parse_value f (skip_ws rest2)) as [[v rest3] |] eqn:Ev; try discriminate.
        rewrite (IHv _ _ Ev).
        destruct (parse_members_more f (skip_ws rest3)) as [[ms rest4] |] eqn:Emm; try discriminate.
        rewrite (IHmm _ _ Emm). cbn. exact H.
      * discriminate.
  - (* parse_members_more *)
    cbn [parse_members_more] in H.
    destruct w as [| c rest]; cbn [parse_members_more] in H; try discriminate.
    cbn [parse_members_more].
    destruct (Ascii.eqb c "}"%char) eqn:E1.
    + exact H.
    + destruct (Ascii.eqb c ","%char) eqn:E2.
      * destruct (parse_string (skip_ws rest)) as [[s rest1] |] eqn:Es; try discriminate.
        destruct (skip_ws rest1) as [| c' rest2] eqn:Ew; try discriminate.
        destruct (Ascii.eqb c' ":"%char) eqn:E3.
        -- destruct (parse_value f (skip_ws rest2)) as [[v rest3] |] eqn:Ev; try discriminate.
           rewrite (IHv _ _ Ev).
           destruct (parse_members_more f (skip_ws rest3)) as [[ms rest4] |] eqn:Emm; try discriminate.
           rewrite (IHmm _ _ Emm). cbn. exact H.
        -- discriminate.
      * discriminate.
  - (* parse_elements *)
    cbn [parse_elements] in H.
    destruct w as [| c rest]; cbn [parse_elements] in H; try discriminate.
    cbn [parse_elements].
    destruct (Ascii.eqb c "]"%char) eqn:E1.
    + exact H.
    + destruct (parse_value f (c :: rest)) as [[v rest1] |] eqn:Ev; try discriminate.
      rewrite (IHv _ _ Ev).
      destruct (parse_elements_more f (skip_ws rest1)) as [[vs rest2] |] eqn:Eem; try discriminate.
      rewrite (IHem _ _ Eem). cbn. exact H.
  - (* parse_elements_more *)
    cbn [parse_elements_more] in H.
    destruct w as [| c rest]; cbn [parse_elements_more] in H; try discriminate.
    cbn [parse_elements_more].
    destruct (Ascii.eqb c "]"%char) eqn:E1.
    + exact H.
    + destruct (Ascii.eqb c ","%char) eqn:E2.
      * destruct (parse_value f (skip_ws rest)) as [[v rest1] |] eqn:Ev; try discriminate.
        rewrite (IHv _ _ Ev).
        destruct (parse_elements_more f (skip_ws rest1)) as [[vs rest2] |] eqn:Eem; try discriminate.
        rewrite (IHem _ _ Eem). cbn. exact H.
      * discriminate.
Qed.

Lemma parse_value_mono (fuel fuel' : nat) (w : list ascii) (r : Json * list ascii) :
  fuel <= fuel' -> parse_value fuel w = Some r -> parse_value fuel' w = Some r.
Proof.
  intros Hle H. exact (fst (fst (fst (fst (fst (fst (parse_all_mono fuel fuel' Hle)))))) w r H).
Qed.

Lemma parse_members_more_mono (fuel fuel' : nat) (w : list ascii) (r : list (list ascii * Json) * list ascii) :
  fuel <= fuel' -> parse_members_more fuel w = Some r -> parse_members_more fuel' w = Some r.
Proof.
  intros Hle H. exact (snd (fst (fst (parse_all_mono fuel fuel' Hle))) w r H).
Qed.

Lemma parse_elements_more_mono (fuel fuel' : nat) (w : list ascii) (r : list Json * list ascii) :
  fuel <= fuel' -> parse_elements_more fuel w = Some r -> parse_elements_more fuel' w = Some r.
Proof.
  intros Hle H. exact (snd (parse_all_mono fuel fuel' Hle) w r H).
Qed.

Lemma value_len_nonempty (prefix w : list ascii) (v : Json) (j : nat) :
  denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt j ->
  List.length w >= 1.
Proof.
  intros Hd. unfold value_spec in Hd.
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json (Map (fun _ : unit => JNull) (lit "null")) _ tt tt (List.length prefix) j v)) in Hd.
  destruct Hd as [Hd | Hd].
  - apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit Json (fun _ : unit => JNull) (lit "null") tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [u [Ev Hl]]. subst v.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "n") (lit "ull")) tt tt (List.length prefix) j u)) in Hl.
    destruct Hl as [p [_ Hseq]].
    apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "n") (lit "ull") tt tt (List.length prefix) j p)) in Hseq.
    destruct Hseq as [γ1 [j1 [a [b [[_ Hc] _]]]]].
    destruct (char_head_cons "n"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w. simpl. lia.
  - apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [Hd | Hd].
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) bool Json (fun b : bool => JBool b) _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [b [Ev Hb]]. subst v.
        apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) bool _ _ tt tt (List.length prefix) j b)) in Hb.
        destruct Hb as [Ht | Hf].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => true) (lit "true") tt tt (List.length prefix) j b)) in Ht.
           destruct Ht as [u [Eb Hl]]. subst b.
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "t") (lit "rue")) tt tt (List.length prefix) j u)) in Hl.
           destruct Hl as [p [_ Hseq]].
           apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "t") (lit "rue") tt tt (List.length prefix) j p)) in Hseq.
           destruct Hseq as [γ1 [j1 [a [b [[_ Hc] _]]]]].
           destruct (char_head_cons "t"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w. simpl. lia.
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => false) (lit "false") tt tt (List.length prefix) j b)) in Hf.
           destruct Hf as [u [Eb Hl]]. subst b.
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "f") (lit "alse")) tt tt (List.length prefix) j u)) in Hl.
           destruct Hl as [p [_ Hseq]].
           apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "f") (lit "alse") tt tt (List.length prefix) j p)) in Hseq.
           destruct Hseq as [γ1 [j1 [a [b [[_ Hc] _]]]]].
           destruct (char_head_cons "f"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w. simpl. lia.
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii) Json JString string_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [ss [Ev Hs]]. subst v.
        apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii) (char "034") (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034") (fun _ : unit => Pure cs))) tt tt (List.length prefix) j ss)) in Hs.
        destruct Hs as [γ1 [j1 [a [Hc _]]]].
        destruct (char_head_cons "034"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w. simpl. lia.
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) Z Json JNumber number_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [n [Ev Hn]]. subst v.
        destruct (number_head prefix w n j Hn) as [c [rest [Ew _]]]. subst w. simpl. lia.
      * apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [Hd | Hd].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) Json JArray array_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [vs [Ev Ha]]. subst v.
           apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) (char "[") (fun _ : unit => Bind ws (fun _ : unit => Bind elements_spec (fun vs0 : list Json => Bind ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs0))))) tt tt (List.length prefix) j vs)) in Ha.
           destruct Ha as [γ1 [j1 [a [Hc _]]]].
           destruct (char_head_cons "["%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w. simpl. lia.
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) Json JObject object_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [ms [Ev Ho]]. subst v.
           apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) (char "{") (fun _ : unit => Bind ws (fun _ : unit => Bind members_spec (fun ms0 : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms0))))) tt tt (List.length prefix) j ms)) in Ho.
           destruct Ho as [γ1 [j1 [a [Hc _]]]].
           destruct (char_head_cons "{"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w. simpl. lia.
Qed.

Lemma value_first_char (prefix w : list ascii) (v : Json) (j : nat) :
  denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt j ->
  { c : ascii & { rest : list ascii & prod (w = c :: rest) (Ascii.eqb c "]"%char = false) } }.
Proof.
  intros Hd. unfold value_spec in Hd.
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json (Map (fun _ : unit => JNull) (lit "null")) _ tt tt (List.length prefix) j v)) in Hd.
  destruct Hd as [Hd | Hd].
  - apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit Json (fun _ : unit => JNull) (lit "null") tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [u [Ev Hl]]. subst v.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "n") (lit "ull")) tt tt (List.length prefix) j u)) in Hl.
    destruct Hl as [p [_ Hseq]].
    apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "n") (lit "ull") tt tt (List.length prefix) j p)) in Hseq.
    destruct Hseq as [γ1 [j1 [a [b [[_ Hc] _]]]]].
    destruct (char_head_cons "n"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w.
    exists "n"%char, rest. split; [reflexivity | reflexivity].
  - apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [Hd | Hd].
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) bool Json (fun b : bool => JBool b) _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [b [Ev Hb]]. subst v.
        apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) bool _ _ tt tt (List.length prefix) j b)) in Hb.
        destruct Hb as [Ht | Hf].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => true) (lit "true") tt tt (List.length prefix) j b)) in Ht.
           destruct Ht as [u [Eb Hl]]. subst b.
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "t") (lit "rue")) tt tt (List.length prefix) j u)) in Hl.
           destruct Hl as [p [_ Hseq]].
           apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "t") (lit "rue") tt tt (List.length prefix) j p)) in Hseq.
           destruct Hseq as [γ1 [j1 [a [b [[_ Hc] _]]]]].
           destruct (char_head_cons "t"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w.
           exists "t"%char, rest. split; [reflexivity | reflexivity].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => false) (lit "false") tt tt (List.length prefix) j b)) in Hf.
           destruct Hf as [u [Eb Hl]]. subst b.
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "f") (lit "alse")) tt tt (List.length prefix) j u)) in Hl.
           destruct Hl as [p [_ Hseq]].
           apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "f") (lit "alse") tt tt (List.length prefix) j p)) in Hseq.
           destruct Hseq as [γ1 [j1 [a [b [[_ Hc] _]]]]].
           destruct (char_head_cons "f"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w.
           exists "f"%char, rest. split; [reflexivity | reflexivity].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii) Json JString string_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [ss [Ev Hs]]. subst v.
        apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii) (char "034") (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034") (fun _ : unit => Pure cs))) tt tt (List.length prefix) j ss)) in Hs.
        destruct Hs as [γ1 [j1 [a [Hc _]]]].
        destruct (char_head_cons "034"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w.
        exists "034"%char, rest. split; [reflexivity | reflexivity].
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) Z Json JNumber number_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [n [Ev Hn]]. subst v.
        destruct (number_head prefix w n j Hn) as [c [rest [Ew Horb]]]. subst w.
        exists c, rest. split; [reflexivity |].
        destruct (is_digitb c) eqn:Ed.
        -- destruct (Ascii.eqb c "]"%char) eqn:E; [| reflexivity].
           apply (Ascii.eqb_eq c "]"%char) in E. subst c. unfold is_digitb in Ed. simpl in Ed. discriminate.
        -- simpl in Horb. apply (Ascii.eqb_eq c "-"%char) in Horb. subst c. reflexivity.
      * apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [Hd | Hd].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) Json JArray array_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [vs [Ev Ha]]. subst v.
           apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) (char "[") (fun _ : unit => Bind ws (fun _ : unit => Bind elements_spec (fun vs0 : list Json => Bind ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs0))))) tt tt (List.length prefix) j vs)) in Ha.
           destruct Ha as [γ1 [j1 [a [Hc _]]]].
           destruct (char_head_cons "["%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w.
           exists "["%char, rest. split; [reflexivity | reflexivity].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) Json JObject object_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [ms [Ev Ho]]. subst v.
           apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) (char "{") (fun _ : unit => Bind ws (fun _ : unit => Bind members_spec (fun ms0 : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms0))))) tt tt (List.length prefix) j ms)) in Ho.
           destruct Ho as [γ1 [j1 [a [Hc _]]]].
           destruct (char_head_cons "{"%char prefix w a γ1 j1 Hc) as [rest [Ew _]]. subst w.
           exists "{"%char, rest. split; [reflexivity | reflexivity].
Qed.

Lemma value_consumes (prefix w : list ascii) (v : Json) (j : nat) :
  denote json_grammar (prefix ++ w) value_spec tt (List.length prefix) v tt j ->
  List.length prefix < j.
Proof.
  intros Hd. unfold value_spec in Hd.
  apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json (Map (fun _ : unit => JNull) (lit "null")) _ tt tt (List.length prefix) j v)) in Hd.
  destruct Hd as [Hd | Hd].
  - apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit Json (fun _ : unit => JNull) (lit "null") tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [u [Ev Hl]]. subst v.
    apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "n") (lit "ull")) tt tt (List.length prefix) j u)) in Hl.
    destruct Hl as [p [_ Hseq]].
    apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "n") (lit "ull") tt tt (List.length prefix) j p)) in Hseq.
    destruct Hseq as [γ1 [j1 [a [b [[_ Hc] Hl2]]]]].
    destruct (char_head_cons "n"%char prefix w a γ1 j1 Hc) as [rest [Ew [Eg Ej]]]. subst γ1. subst w.
    pose proof (denote_ge_json (prefix ++ "n"%char :: rest) unit (lit "ull") tt tt j1 j b Hl2) as Hg. lia.
  - apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [Hd | Hd].
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) bool Json (fun b : bool => JBool b) _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [b [Ev Hb]]. subst v.
        apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) bool _ _ tt tt (List.length prefix) j b)) in Hb.
        destruct Hb as [Ht | Hf].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => true) (lit "true") tt tt (List.length prefix) j b)) in Ht.
           destruct Ht as [u [Eb Hl]]. subst b.
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "t") (lit "rue")) tt tt (List.length prefix) j u)) in Hl.
           destruct Hl as [p [_ Hseq]].
           apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "t") (lit "rue") tt tt (List.length prefix) j p)) in Hseq.
           destruct Hseq as [γ1 [j1 [a [b [[_ Hc] Hl2]]]]].
           destruct (char_head_cons "t"%char prefix w a γ1 j1 Hc) as [rest [Ew [Eg Ej]]]. subst γ1. subst w.
           pose proof (denote_ge_json (prefix ++ "t"%char :: rest) unit (lit "rue") tt tt j1 j b Hl2) as Hg. lia.
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => false) (lit "false") tt tt (List.length prefix) j b)) in Hf.
           destruct Hf as [u [Eb Hl]]. subst b.
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "f") (lit "alse")) tt tt (List.length prefix) j u)) in Hl.
           destruct Hl as [p [_ Hseq]].
           apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "f") (lit "alse") tt tt (List.length prefix) j p)) in Hseq.
           destruct Hseq as [γ1 [j1 [a [b [[_ Hc] Hl2]]]]].
           destruct (char_head_cons "f"%char prefix w a γ1 j1 Hc) as [rest [Ew [Eg Ej]]]. subst γ1. subst w.
           pose proof (denote_ge_json (prefix ++ "f"%char :: rest) unit (lit "alse") tt tt j1 j b Hl2) as Hg. lia.
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii) Json JString string_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [ss [Ev Hs]]. subst v.
        apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii) (char "034") (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034") (fun _ : unit => Pure cs))) tt tt (List.length prefix) j ss)) in Hs.
        destruct Hs as [γ1 [j1 [a [Hc Hl2]]]].
        destruct (char_head_cons "034"%char prefix w a γ1 j1 Hc) as [rest [Ew [Eg Ej]]]. subst γ1. subst w.
        pose proof (denote_ge_json (prefix ++ "034"%char :: rest) (list ascii) (Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034") (fun _ : unit => Pure cs))) tt tt j1 j ss Hl2) as Hg. lia.
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) Z Json JNumber number_spec tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [n [Ev Hn]]. subst v.
        unfold number_spec in Hn.
        apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) bool Z (Alt (Map (fun _ : unit => true) (char "-")) (Pure false)) (fun neg : bool => Map (fun n0 : nat => if neg then Z.opp (Z.of_nat n0) else Z.of_nat n0) int_spec) tt tt (List.length prefix) j n)) in Hn.
        destruct Hn as [γ1 [j1 [neg [Hneg Hn2]]]]. destruct γ1.
        apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) bool (Map (fun _ : unit => true) (char "-")) (Pure false) tt tt (List.length prefix) j1 neg)) in Hneg.
        destruct Hneg as [Hdash | Hfalse].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => true) (char "-") tt tt (List.length prefix) j1 neg)) in Hdash.
           destruct Hdash as [u [E Hc]].
           destruct (char_head_cons "-"%char prefix w u tt j1 Hc) as [rest [Ew [Eg Ej]]]. subst j1. subst w.
           pose proof (denote_ge_json (prefix ++ "-"%char :: rest) Z (Map (fun n0 : nat => if neg then Z.opp (Z.of_nat n0) else Z.of_nat n0) int_spec) tt tt (S (List.length prefix)) j n Hn2) as Hg. lia.
        -- apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) bool false tt (List.length prefix) neg tt j1)) in Hfalse.
           destruct Hfalse as [[Eneg _] Ej]. subst j1. subst neg.
           unfold int_spec in Hn2.
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) nat Z (fun n0 : nat => Z.of_nat n0) (Alt (Map (fun _ : unit => 0) (char "0")) (Map (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec)))) tt tt (List.length prefix) j n)) in Hn2.
           destruct Hn2 as [n0 [En Hn3]]. subst n.
           apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) nat (Map (fun _ : unit => 0) (char "0")) _ tt tt (List.length prefix) j n0)) in Hn3.
           destruct Hn3 as [Hz | Hd19].
           ++ apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit nat (fun _ : unit => 0) (char "0") tt tt (List.length prefix) j n0)) in Hz.
              destruct Hz as [u [E0 Hc]].
              destruct (char_head_cons "0"%char prefix w u tt j Hc) as [rest [Ew [Eg Ej]]]. subst w. lia.
           ++ apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (ascii * list ascii) nat (fun p : ascii * list ascii => digits_to_nat (fst p :: snd p)) (Seq digit1_9_spec (Many digit_spec)) tt tt (List.length prefix) j n0)) in Hd19.
              destruct Hd19 as [p [E Hseq]].
              apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) ascii (list ascii) digit1_9_spec (Many digit_spec) tt tt (List.length prefix) j p)) in Hseq.
              destruct Hseq as [γ2 [j2 [c [cs [[Eab Hd19c] Hmany]]]]].
              apply (fst (denote_tok_iff ascii unit json_nt json_grammar (prefix ++ w) (fun c0 : ascii => is_digit1_9b c0 = true) c tt γ2 (List.length prefix) j2)) in Hd19c.
              destruct Hd19c as [[[Eg2 Ej2] Hnth] HP]. subst γ2. subst j2.
              pose proof (denote_ge_json (prefix ++ w) (list ascii) (Many digit_spec) tt tt (S (List.length prefix)) j cs Hmany) as Hg.
              lia.
      * apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [Hd | Hd].
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) Json JArray array_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [vs [Ev Ha]]. subst v.
           apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) (char "[") (fun _ : unit => Bind ws (fun _ : unit => Bind elements_spec (fun vs0 : list Json => Bind ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs0))))) tt tt (List.length prefix) j vs)) in Ha.
           destruct Ha as [γ1 [j1 [a [Hc Hl2]]]].
           destruct (char_head_cons "["%char prefix w a γ1 j1 Hc) as [rest [Ew [Eg Ej]]]. subst γ1. subst w.
           pose proof (denote_ge_json (prefix ++ "["%char :: rest) (list Json) (Bind ws (fun _ : unit => Bind elements_spec (fun vs0 : list Json => Bind ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs0))))) tt tt j1 j vs Hl2) as Hg. lia.
        -- apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) Json JObject object_spec tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [ms [Ev Ho]]. subst v.
           apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) (char "{") (fun _ : unit => Bind ws (fun _ : unit => Bind members_spec (fun ms0 : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms0))))) tt tt (List.length prefix) j ms)) in Ho.
           destruct Ho as [γ1 [j1 [a [Hc Hl2]]]].
           destruct (char_head_cons "{"%char prefix w a γ1 j1 Hc) as [rest [Ew [Eg Ej]]]. subst γ1. subst w.
           pose proof (denote_ge_json (prefix ++ "{"%char :: rest) (list (list ascii * Json)) (Bind ws (fun _ : unit => Bind members_spec (fun ms0 : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms0))))) tt tt j1 j ms Hl2) as Hg. lia.
Qed.

Lemma parse_member_mono (fuel fuel' : nat) (w : list ascii) (r : (list ascii * Json) * list ascii) :
  fuel <= fuel' -> parse_member fuel w = Some r -> parse_member fuel' w = Some r.
Proof.
  intros Hle H. unfold parse_member in H.
  destruct (parse_string w) as [[s rest1] |] eqn:Es; [| discriminate].
  destruct (skip_ws rest1) as [| c' rest2] eqn:Eskip1; [discriminate |].
  destruct (Ascii.eqb c' ":"%char) eqn:Ecolon; [| discriminate].
  destruct (parse_value fuel (skip_ws rest2)) as [[v rest3] |] eqn:Ev; [| discriminate].
  simpl in H. injection H as Hr. subst r.
  unfold parse_member. rewrite Es, Eskip1, Ecolon.
  rewrite (parse_value_mono fuel fuel' (skip_ws rest2) (v, rest3) Hle Ev). reflexivity.
Qed.

Lemma parse_member_cons (prefix w : list ascii) (m : list ascii * Json) (j : nat) :
  denote json_grammar (prefix ++ w) member_spec tt (List.length prefix) m tt j ->
  List.length prefix < j.
Proof.
  intros Hd. unfold member_spec in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii) (list ascii * Json) string_spec (fun s : list ascii => Bind ws (fun _ : unit => Bind (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value))))) tt tt (List.length prefix) j m)) in Hd.
  destruct Hd as [γ1 [j1 [s [Hs Hrest]]]].
  pose proof (denote_ge_json (prefix ++ w) (list ascii) string_spec tt γ1 (List.length prefix) j1 s Hs) as Hg1.
  pose proof (denote_ge_json (prefix ++ w) (list ascii * Json) (Bind ws (fun _ : unit => Bind (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value))))) γ1 tt j1 j m Hrest) as Hg2.
  unfold string_spec in Hs.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii) (char "034"%char) (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) tt γ1 (List.length prefix) j1 s)) in Hs.
  destruct Hs as [γq [jq [uq [Hq Hs_rest]]]].
  apply (char_denote_nth (prefix ++ w) "034"%char (List.length prefix) jq uq γq) in Hq.
  destruct Hq as [Hnth [Eu [Eg Ej]]]. subst uq. subst γq. subst jq.
  pose proof (denote_ge_json (prefix ++ w) (list ascii) (Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) tt γ1 (S (List.length prefix)) j1 s Hs_rest) as Hg3.
  lia.
Qed.

(* A member's input is non-ws at the head, so skip_ws is a no-op on it. *)
Lemma member_input_skip_ws (prefix w : list ascii) (m : list ascii * Json) (j : nat) :
  denote json_grammar (prefix ++ w) member_spec tt (List.length prefix) m tt j ->
  skip_ws w = w.
Proof.
  intros Hd.
  destruct w as [| c rest]; [reflexivity |].
  unfold skip_ws.
  destruct (is_wsb c) eqn:Ews; [| reflexivity].
  exfalso.
  unfold member_spec in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ c :: rest) (list ascii) (list ascii * Json) string_spec (fun s : list ascii => Bind ws (fun _ : unit => Bind (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value))))) tt tt (List.length prefix) j m)) in Hd.
  destruct Hd as [γ1 [j1 [s [Hs Hrest]]]].
  unfold string_spec in Hs.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ c :: rest) unit (list ascii) (char "034"%char) (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) tt γ1 (List.length prefix) j1 s)) in Hs.
  destruct Hs as [γq [jq [uq [Hq _]]]].
  apply (char_denote_nth (prefix ++ c :: rest) "034"%char (List.length prefix) jq uq γq) in Hq.
  destruct Hq as [Hnth [Eu [Eg Ej]]].
  rewrite (nth_error_app_cons c prefix rest) in Hnth.
  injection Hnth as Hc. subst c. simpl in Ews. discriminate.
Qed.

(* A denotation that consumes at least one token ends within the input. *)
Lemma denote_le_length (w : list ascii) (A : Type) (s : Spec ascii unit json_nt A) (γ γ' : unit) (i j : nat) (a : A) :
  denote json_grammar w s γ i a γ' j -> i < j -> j <= List.length w.
Proof.
  intros d Hlt. induction d; simpl in *; try (exfalso; lia).
  - assert (en : nth_error w i <> None) by (rewrite e; discriminate). apply nth_error_Some in en. lia.
  - destruct (Nat.lt_ge_cases j k) as [Hjk | Hkj].
    + apply (IHd2 Hjk).
    + assert (k = j) by (pose proof (denote_ge_json w B s2 γ' γ'' j k b d2) as Hg; lia). subst k. apply IHd1. lia.
  - apply IHd. exact Hlt.
  - apply IHd. exact Hlt.
  - apply IHd. exact Hlt.
  - destruct (Nat.lt_ge_cases j k) as [Hjk | Hkj].
    + apply (IHd2 Hjk).
    + assert (k = j) by (pose proof (denote_ge_json w B (f a) γ' γ'' j k b d2) as Hg; lia). subst k. apply IHd1. lia.
  - apply IHd. exact Hlt.
  - destruct (Nat.lt_ge_cases j k) as [Hjk | Hkj].
    + apply (IHd2 Hjk).
    + assert (k = j) by (pose proof (denote_ge_json w (list A) (Many s) γ' γ'' j k as_ d2) as Hg; lia). subst k. apply IHd1. lia.
  - destruct (Nat.lt_ge_cases j k) as [Hjk | Hkj].
    + apply (IHd2 Hjk).
    + assert (k = j) by (pose proof (denote_ge_json w (list A) (@Exactly ascii unit json_nt A n s) γ' γ'' j k as_ d2) as Hg; lia). subst k. apply IHd1. lia.
  - apply IHd. exact Hlt.
  - apply IHd. exact Hlt.
Qed.

(* parse_member is complete for member_spec, given the value parser's completeness
   on strictly shorter inputs. *)
Lemma parse_member_complete (fuel : nat) :
  (forall (prefix w : list ascii) (m : list ascii * Json) (j : nat),
     (forall (prefix' w' : list ascii) (v : Json) (j' : nat),
        List.length w' < List.length w ->
        denote json_grammar (prefix' ++ w') value_spec tt (List.length prefix') v tt j' ->
        (forall c : ascii, nth_error (prefix' ++ w') j' = Some c -> is_digitb c = false) ->
        parse_value fuel (skip_ws w') = Some (v, skipn j' (prefix' ++ w'))) ->
     denote json_grammar (prefix ++ w) member_spec tt (List.length prefix) m tt j ->
     (forall c : ascii, nth_error (prefix ++ w) j = Some c -> is_digitb c = false) ->
     parse_member fuel (skip_ws w) = Some (m, skipn j (prefix ++ w))).
Proof.
  intros prefix w m j Hvc Hd Hnodigit.
  pose proof Hd as Hd_orig.
  pose proof (member_input_skip_ws prefix w m j Hd) as Hskip_w.
  unfold member_spec in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii) (list ascii * Json) string_spec (fun s : list ascii => Bind ws (fun _ : unit => Bind (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value))))) tt tt (List.length prefix) j m)) in Hd.
  destruct Hd as [γs [js [s [Hstr Hmem1]]]].
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii * Json) ws (fun _ : unit => Bind (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value)))) γs tt js j m)) in Hmem1.
  destruct Hmem1 as [γw1 [jw1 [u1 [Hws_a Hmem2]]]].
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii * Json) (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value))) γw1 tt jw1 j m)) in Hmem2.
  destruct Hmem2 as [γc [jc [uc [Hcolon Hmem3]]]].
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii * Json) ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value)) γc tt jc j m)) in Hmem3.
  destruct Hmem3 as [γw2 [jw2 [u2 [Hws_b Hmem4]]]].
  apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) Json (list ascii * Json) (fun v : Json => (s, v)) (Call NT_value) γw2 tt jw2 j m)) in Hmem4.
  destruct Hmem4 as [v [Em Hcall]].
  apply (fst (denote_call_iff ascii unit json_nt json_grammar (prefix ++ w) Json NT_value γw2 tt jw2 j v)) in Hcall.
  cbn [json_grammar] in Hcall.
  subst m. destruct γs, γw1, γc, γw2, u1, uc, u2.
  apply (char_denote_nth (prefix ++ w) ":"%char jw1 jc tt tt) in Hcolon.
  destruct Hcolon as [Hnth_colon [_ [_ Ejc]]]. subst jc.
  assert (Hj_le : j <= List.length (prefix ++ w)).
  { apply (denote_le_length (prefix ++ w) (list ascii * Json) member_spec tt tt (List.length prefix) j (s, v) Hd_orig).
    apply (parse_member_cons prefix w (s, v) j Hd_orig). }
  assert (Hjw2_le : jw2 <= List.length (prefix ++ w)).
  { pose proof (denote_ge_json (prefix ++ w) Json value_spec tt tt jw2 j v Hcall) as Hg. lia. }
  assert (Hjw2_gt : List.length prefix < jw2).
  { pose proof (denote_ge_json (prefix ++ w) (list ascii) string_spec tt tt (List.length prefix) js s Hstr) as Hg1.
    pose proof (denote_ge_json (prefix ++ w) unit ws tt tt js jw1 tt Hws_a) as Hg2.
    pose proof (denote_ge_json (prefix ++ w) unit ws tt tt (S jw1) jw2 tt Hws_b) as Hg3.
    lia. }
  assert (Hlt : List.length (skipn jw2 (prefix ++ w)) < List.length w).
  { rewrite (skipn_length jw2 (prefix ++ w)). rewrite length_app. rewrite length_app in Hjw2_le. lia. }
  assert (Hnws_colon : forall c, nth_error (prefix ++ w) jw1 = Some c -> is_wsb c = false).
  { intros c Hc. rewrite Hnth_colon in Hc. injection Hc as Hc'. subst c. simpl. reflexivity. }
  assert (Hnws_val : forall c, nth_error (prefix ++ w) jw2 = Some c -> is_wsb c = false).
  { intros c Hc. destruct (is_wsb c) eqn:E; [| reflexivity].
    exfalso. apply (value_no_ws (firstn jw2 (prefix ++ w)) c (skipn (S jw2) (prefix ++ w)) v j E).
    replace (firstn jw2 (prefix ++ w) ++ c :: skipn (S jw2) (prefix ++ w)) with (prefix ++ w).
    + replace (List.length (firstn jw2 (prefix ++ w))) with jw2 by (rewrite firstn_length; symmetry; apply Nat.min_l; exact Hjw2_le).
      exact Hcall.
    + rewrite <- (skipn_cons_head ascii (prefix ++ w) jw2 c Hc). rewrite (firstn_skipn jw2 (prefix ++ w)). reflexivity. }
  pose proof (ws_skip_gen (prefix ++ w) js jw1 Hws_a Hnws_colon) as Hskip2.
  pose proof (ws_skip_gen (prefix ++ w) (S jw1) jw2 Hws_b Hnws_val) as Hskip_b.
  pose proof (parse_string_complete prefix w s js Hstr) as Hps.
  assert (Hps' : parse_string (skip_ws w) = Some (s, skipn js (prefix ++ w))).
  { exact (eq_ind_r (fun w0 : list ascii => parse_string w0 = Some (s, skipn js (prefix ++ w))) Hps Hskip_w). }
  assert (Hcall' : denote json_grammar (firstn jw2 (prefix ++ w) ++ skipn jw2 (prefix ++ w)) value_spec tt (List.length (firstn jw2 (prefix ++ w))) v tt j).
  { rewrite (firstn_skipn jw2 (prefix ++ w)). rewrite firstn_length. rewrite (Nat.min_l jw2 (List.length (prefix ++ w)) Hjw2_le). exact Hcall. }
  assert (Hnodigit' : forall c, nth_error (firstn jw2 (prefix ++ w) ++ skipn jw2 (prefix ++ w)) j = Some c -> is_digitb c = false).
  { intros c Hc. apply Hnodigit. rewrite <- (firstn_skipn jw2 (prefix ++ w)). exact Hc. }
  pose proof (Hvc (firstn jw2 (prefix ++ w)) (skipn jw2 (prefix ++ w)) v j Hlt Hcall' Hnodigit') as Hpv.
  rewrite (firstn_skipn jw2 (prefix ++ w)) in Hpv.
  pose proof (value_input_skip_ws (firstn jw2 (prefix ++ w)) (skipn jw2 (prefix ++ w)) v j Hcall') as Hskip_v.
  unfold parse_member.
  rewrite Hps'.
  rewrite Hskip2. rewrite (skipn_cons_head ascii (prefix ++ w) jw1 ":"%char Hnth_colon).
  cbn [Ascii.eqb].
  rewrite Hskip_b. rewrite <- Hskip_v. rewrite Hpv. reflexivity.
Qed.

Lemma complete_value_object_array : forall w : list ascii, prod (Vst w) (prod (Ost w) (Ast w)).
Proof.
  apply (@well_founded_induction_type (list ascii) (fun w w' : list ascii => List.length w < List.length w') wf_lt_length (fun w => prod (Vst w) (prod (Ost w) (Ast w)))). intros w IH.
  assert (Vst_w : Vst w).
  { intros prefix v j Hd Hnd. unfold value_spec in Hd.
    assert (Hw_gt : List.length w >= 1) by (apply (value_len_nonempty prefix w v j Hd)).
    apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
    destruct Hd as [Hnull | Hd].
    + (* null *)
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit Json (fun _ : unit => JNull) (lit "null") tt tt (List.length prefix) j v)) in Hnull.
      destruct Hnull as [u [Ev Hlit]]. subst v.
      exists 1. split; [lia |]. change (denote json_grammar (prefix ++ w) (Map (fun _ : unit * unit => tt) (Seq (char "n") (lit "ull"))) tt (List.length prefix) u tt j) in Hlit.
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "n") (lit "ull")) tt tt (List.length prefix) j u)) in Hlit.
      destruct Hlit as [p [Em Hseq]].
      apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "n") (lit "ull") tt tt (List.length prefix) j p)) in Hseq.
      destruct Hseq as [γ1 [j1 [a [b [[_ Hc] Hl]]]]].
      apply (char_head_cons "n"%char prefix w a γ1 j1) in Hc.
      destruct Hc as [rest [Ew [Eg Ej]]]. subst w. subst γ1. subst j1. destruct a. destruct b.
      replace (prefix ++ "n"%char :: rest) with ((prefix ++ ["n"%char]) ++ rest) in Hl by (rewrite <- app_assoc; simpl; reflexivity).
      replace (S (List.length prefix)) with (List.length (prefix ++ ["n"%char])) in Hl by (rewrite length_app; simpl; lia).
      pose proof (parse_lit_complete "ull" (prefix ++ ["n"%char]) rest j Hl) as Hlr.
      replace ((prefix ++ ["n"%char]) ++ rest) with (prefix ++ "n"%char :: rest) in Hlr by (rewrite <- app_assoc; simpl; reflexivity).
      cbn [parse_value]. rewrite Hlr. simpl. reflexivity.
    + apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
      destruct Hd as [Hd | Hd].
      * apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [Hbool | Hstring].
        -- (* bool *)
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) bool Json (fun b : bool => JBool b) _ tt tt (List.length prefix) j v)) in Hbool.
           destruct Hbool as [b [Ev Hb]]. subst v.
           apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) bool _ _ tt tt (List.length prefix) j b)) in Hb.
           destruct Hb as [Htrue | Hfalse].
           ++ (* true *)
              apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => true) (lit "true") tt tt (List.length prefix) j b)) in Htrue.
              destruct Htrue as [u [Eb Hlit]]. subst b.
              exists 1. split; [lia |]. change (denote json_grammar (prefix ++ w) (Map (fun _ : unit * unit => tt) (Seq (char "t") (lit "rue"))) tt (List.length prefix) u tt j) in Hlit.
              apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "t") (lit "rue")) tt tt (List.length prefix) j u)) in Hlit.
              destruct Hlit as [p [Em Hseq]].
              apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "t") (lit "rue") tt tt (List.length prefix) j p)) in Hseq.
              destruct Hseq as [γ1 [j1 [a [b' [[_ Hc] Hl]]]]].
              apply (char_head_cons "t"%char prefix w a γ1 j1) in Hc.
              destruct Hc as [rest [Ew [Eg Ej]]]. subst w. subst γ1. subst j1. destruct a. destruct b'.
              replace (prefix ++ "t"%char :: rest) with ((prefix ++ ["t"%char]) ++ rest) in Hl by (rewrite <- app_assoc; simpl; reflexivity).
              replace (S (List.length prefix)) with (List.length (prefix ++ ["t"%char])) in Hl by (rewrite length_app; simpl; lia).
              pose proof (parse_lit_complete "rue" (prefix ++ ["t"%char]) rest j Hl) as Hlr.
              replace ((prefix ++ ["t"%char]) ++ rest) with (prefix ++ "t"%char :: rest) in Hlr by (rewrite <- app_assoc; simpl; reflexivity).
              cbn [parse_value]. rewrite Hlr. simpl. reflexivity.
           ++ (* false *)
              apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) unit bool (fun _ : unit => false) (lit "false") tt tt (List.length prefix) j b)) in Hfalse.
              destruct Hfalse as [u [Eb Hlit]]. subst b.
              exists 1. split; [lia |]. change (denote json_grammar (prefix ++ w) (Map (fun _ : unit * unit => tt) (Seq (char "f") (lit "alse"))) tt (List.length prefix) u tt j) in Hlit.
              apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "f") (lit "alse")) tt tt (List.length prefix) j u)) in Hlit.
              destruct Hlit as [p [Em Hseq]].
              apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit unit (char "f") (lit "alse") tt tt (List.length prefix) j p)) in Hseq.
              destruct Hseq as [γ1 [j1 [a [b' [[_ Hc] Hl]]]]].
              apply (char_head_cons "f"%char prefix w a γ1 j1) in Hc.
              destruct Hc as [rest [Ew [Eg Ej]]]. subst w. subst γ1. subst j1. destruct a. destruct b'.
              replace (prefix ++ "f"%char :: rest) with ((prefix ++ ["f"%char]) ++ rest) in Hl by (rewrite <- app_assoc; simpl; reflexivity).
              replace (S (List.length prefix)) with (List.length (prefix ++ ["f"%char])) in Hl by (rewrite length_app; simpl; lia).
              pose proof (parse_lit_complete "alse" (prefix ++ ["f"%char]) rest j Hl) as Hlr.
              replace ((prefix ++ ["f"%char]) ++ rest) with (prefix ++ "f"%char :: rest) in Hlr by (rewrite <- app_assoc; simpl; reflexivity).
              cbn [parse_value]. rewrite Hlr. simpl. reflexivity.
        -- (* string *)
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii) Json JString string_spec tt tt (List.length prefix) j v)) in Hstring.
           destruct Hstring as [s [Ev Hs]]. subst v.
           destruct w as [| c rest].
           { rewrite app_nil_r in Hs. unfold string_spec in Hs.
             apply (fst (denote_bind_iff ascii unit json_nt json_grammar prefix unit (list ascii) (char "034"%char) (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) tt tt (List.length prefix) j s)) in Hs.
             destruct Hs as [γ1 [j1 [u [Hq _]]]].
             apply (char_denote_nth prefix "034"%char (List.length prefix) j1 u γ1) in Hq.
             destruct Hq as [Hnth _]. rewrite (nth_error_self_none prefix) in Hnth. discriminate. }
           pose proof (bind_char_head "034"%char (list ascii) (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034"%char) (fun _ : unit => Pure cs))) prefix rest c s tt j Hs) as Hc34.
           subst c.

           pose proof (parse_string_complete prefix ("034"%char :: rest) s j Hs) as Hs'.
           exists 1. split; [lia |]. cbn [parse_value]. rewrite Hs'. simpl. reflexivity.
      * apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
        destruct Hd as [Hnumber | Hd].
        -- (* number *)
           apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) Z Json JNumber number_spec tt tt (List.length prefix) j v)) in Hnumber.
           destruct Hnumber as [n [Ev Hn]]. subst v.
           pose proof (parse_number_complete prefix w n j Hn Hnd) as Hnr.
           pose proof (number_head prefix w n j Hn) as Hh.
           destruct Hh as [c [rest [Ew Hdgt]]]. subst w.
           pose proof (parse_value_digit c rest n (skipn j (prefix ++ c :: rest)) Hdgt Hnr) as Hpv.
           exists 1. split; [lia |]. exact Hpv.
        -- apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) Json _ _ tt tt (List.length prefix) j v)) in Hd.
           destruct Hd as [Harray | Hobject].
           ++ (* array *)
              apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) Json JArray array_spec tt tt (List.length prefix) j v)) in Harray.
              destruct Harray as [vs [Ev Ha]]. subst v.
              unfold array_spec in Ha.
              apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) (char "[") (fun _ : unit => Bind ws (fun _ : unit => Bind elements_spec (fun vs : list Json => Bind ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs))))) tt tt (List.length prefix) j vs)) in Ha.
              destruct Ha as [γ1 [j1 [u [Hbracket Hbody]]]].
              apply (char_head_cons "["%char prefix w u γ1 j1) in Hbracket.
              destruct Hbracket as [rest [Ew [Eg Ej]]]. subst w. subst γ1. subst j1. destruct u.
              replace (prefix ++ "["%char :: rest) with ((prefix ++ ["["%char]) ++ rest) in Hbody by (rewrite <- app_assoc; simpl; reflexivity).
              replace (S (List.length prefix)) with (List.length (prefix ++ ["["%char])) in Hbody by (rewrite length_app; simpl; lia).
              destruct ((snd (snd (IH rest (Nat.lt_succ_diag_r (List.length rest))))) (prefix ++ ["["%char]) vs j Hbody) as [fuel [Hfuel_le Harr]].
              exists (S fuel). split.
              - cbn [List.length]. lia.
              - cbn [parse_value]. rewrite Harr. rewrite <- app_assoc. simpl. reflexivity.
           ++ (* object *)
              apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) Json JObject object_spec tt tt (List.length prefix) j v)) in Hobject.
              destruct Hobject as [ms [Ev Ho]]. subst v.
              unfold object_spec in Ho.
              apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) (char "{") (fun _ : unit => Bind ws (fun _ : unit => Bind members_spec (fun ms : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms))))) tt tt (List.length prefix) j ms)) in Ho.
              destruct Ho as [γ1 [j1 [u [Hbrace Hbody]]]].
              apply (char_head_cons "{"%char prefix w u γ1 j1) in Hbrace.
              destruct Hbrace as [rest [Ew [Eg Ej]]]. subst w. subst γ1. subst j1. destruct u.
              replace (prefix ++ "{"%char :: rest) with ((prefix ++ ["{"%char]) ++ rest) in Hbody by (rewrite <- app_assoc; simpl; reflexivity).
              replace (S (List.length prefix)) with (List.length (prefix ++ ["{"%char])) in Hbody by (rewrite length_app; simpl; lia).
              destruct ((fst (snd (IH rest (Nat.lt_succ_diag_r (List.length rest))))) (prefix ++ ["{"%char]) ms j Hbody) as [fuel [Hfuel_le Hobj]].
              exists (S fuel). split.
              - cbn [List.length]. lia.
              - cbn [parse_value]. rewrite Hobj. rewrite <- app_assoc. simpl. reflexivity.

  }
  split; [exact Vst_w | split].
  - (* object *)
    intros prefix ms j Hd. unfold object_body_spec in Hd.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) ws (fun _ : unit => Bind members_spec (fun ms : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms)))) tt tt (List.length prefix) j ms)) in Hd.
    destruct Hd as [γ1 [j1 [u [Hws1 Hrest]]]]. destruct u, γ1.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) (list (list ascii * Json)) members_spec (fun ms0 : list (list ascii * Json) => Bind ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms0))) tt tt j1 j ms)) in Hrest.
    destruct Hrest as [γ2 [j2 [ms0 [Hmem Hrest2]]]]. destruct γ2.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) ws (fun _ : unit => Bind (char "}") (fun _ : unit => Pure ms0)) tt tt j2 j ms)) in Hrest2.
    destruct Hrest2 as [γ3 [j3 [u3 [Hws2 Hrest3]]]]. destruct u3, γ3.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) (char "}") (fun _ : unit => Pure ms0) tt tt j3 j ms)) in Hrest3.
    destruct Hrest3 as [γ4 [j4 [u4 [Hbrace Hpure]]]].
    apply (char_denote_nth (prefix ++ w) "}"%char j3 j4 u4 γ4) in Hbrace.
    destruct Hbrace as [Hnth [Eu4 [Eg4 Ej4]]]. subst u4 γ4 j4.
    apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) ms0 tt (S j3) ms tt j)) in Hpure.
    destruct Hpure as [[Ems0 _] Ej]. subst ms0. subst j.
    unfold members_spec in Hmem.
    apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) _ _ tt tt j1 j2 ms)) in Hmem.
    destruct Hmem as [Hempty | Hcons].
    + (* empty members *)
      apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) (@nil (list ascii * Json)) tt j1 ms tt j2)) in Hempty.
      destruct Hempty as [[Ems _] Ej2]. subst ms. subst j2.
      assert (Hnw : forall c, nth_error (prefix ++ w) j3 = Some c -> is_wsb c = false).
      { intros c Hc. rewrite Hnth in Hc. injection Hc as Hc'. subst c. simpl. reflexivity. }
      pose proof (ws_ws_skip prefix w j1 j3 Hws1 Hws2 Hnw) as Hskip.
      exists (S (S O)). split; [lia |]. cbn [parse_object parse_members].
      rewrite Hskip. rewrite (skipn_cons_head ascii (prefix ++ w) j3 "}"%char Hnth). simpl. reflexivity.
    + (* non-empty members *)
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii * Json) (list (list ascii * Json)) member_spec (fun m : list ascii * Json => Bind ws (fun _ : unit => Map (fun rest : list (list ascii * Json) => m :: rest) members_rest_spec)) tt tt j1 j2 ms)) in Hcons.
      destruct Hcons as [γm [jm [m [Hmem0 Hrest]]]].
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list (list ascii * Json)) ws (fun _ : unit => Map (fun rest : list (list ascii * Json) => m :: rest) members_rest_spec) γm tt jm j2 ms)) in Hrest.
      destruct Hrest as [γw [jw [u [Hws_mid Hmap]]]].
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list (list ascii * Json)) (list (list ascii * Json)) (fun rest : list (list ascii * Json) => m :: rest) members_rest_spec γw tt jw j2 ms)) in Hmap.
      destruct Hmap as [ms' [Ems Hmany]].
      unfold member_spec in Hmem0.
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii) (list ascii * Json) string_spec (fun s : list ascii => Bind ws (fun _ : unit => Bind (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value))))) tt γm j1 jm m)) in Hmem0.
      destruct Hmem0 as [γs [js [s [Hstr Hmem1]]]].
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii * Json) ws (fun _ : unit => Bind (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value)))) γs γm js jm m)) in Hmem1.
      destruct Hmem1 as [γw1 [jw1 [u1 [Hws_a Hmem2]]]].
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii * Json) (char ":") (fun _ : unit => Bind ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value))) γw1 γm jw1 jm m)) in Hmem2.
      destruct Hmem2 as [γc [jc [uc [Hcolon Hmem3]]]].
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii * Json) ws (fun _ : unit => Map (fun v : Json => (s, v)) (Call NT_value)) γc γm jc jm m)) in Hmem3.
      destruct Hmem3 as [γw2 [jw2 [u2 [Hws_b Hmem4]]]].
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) Json (list ascii * Json) (fun v : Json => (s, v)) (Call NT_value) γw2 γm jw2 jm m)) in Hmem4.
      destruct Hmem4 as [v [Em Hcall]].
      apply (fst (denote_call_iff ascii unit json_nt json_grammar (prefix ++ w) Json NT_value γw2 γm jw2 jm v)) in Hcall.
      cbn [json_grammar] in Hcall.
      subst ms. subst m.
      destruct γs, γw1, γc, γw2, γm, γw, uc, u1, u2, u.
      assert (Hnws_head : forall c, nth_error (prefix ++ w) j1 = Some c -> is_wsb c = false).
      { unfold string_spec in Hstr.
        apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii) (char "034") (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034") (fun _ : unit => Pure cs))) tt tt j1 js s)) in Hstr.
        destruct Hstr as [γq [jq [uq [Hquote _]]]].
        apply (char_denote_nth (prefix ++ w) "034"%char j1 jq uq γq) in Hquote.
        destruct Hquote as [Hnth_q _].
        intros c Hc. rewrite Hnth_q in Hc. injection Hc as Hc'. subst c. simpl. reflexivity. }
      pose proof (ws_skip prefix w j1 Hws1 Hnws_head) as Hskip1.
      pose proof (ws_skip_j prefix w j1 Hws1 Hnws_head) as Hj1.
      assert (Hstr' : denote json_grammar ((prefix ++ ws_part w) ++ skip_ws w) string_spec tt (List.length (prefix ++ ws_part w)) s tt js).
      { rewrite <- app_assoc. rewrite (ws_part_skip w). rewrite length_app. rewrite <- Hj1. exact Hstr. }
      pose proof (parse_string_complete (prefix ++ ws_part w) (skip_ws w) s js Hstr') as Hps.
      rewrite <- app_assoc in Hps. rewrite (ws_part_skip w) in Hps.
      apply (char_denote_nth (prefix ++ w) ":"%char jw1 jc tt tt) in Hcolon.
      destruct Hcolon as [Hnth_colon [_ [_ Ejc]]]. subst jc.
      assert (Hnws_colon : forall c, nth_error (prefix ++ w) jw1 = Some c -> is_wsb c = false).
      { intros c Hc. rewrite Hnth_colon in Hc. injection Hc as Hc'. subst c. simpl. reflexivity. }
      pose proof (ws_skip_gen (prefix ++ w) js jw1 Hws_a Hnws_colon) as Hskip2.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt (List.length prefix) j1 tt Hws1) as Hge0.
      pose proof (denote_ge_json (prefix ++ w) (list ascii) string_spec tt tt j1 js s Hstr) as Hge_s.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt js jw1 tt Hws_a) as Hge_a.
      pose proof (denote_ge_json (prefix ++ w) unit ws tt tt (S jw1) jw2 tt Hws_b) as Hge_b.
      assert (Hjw2_le : jw2 <= List.length (prefix ++ w)).
      { pose proof (denote_ge_json (prefix ++ w) Json value_spec tt tt jw2 jm v Hcall) as Hge_v.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jm jw tt Hws_mid) as Hge_mid.
        pose proof (denote_ge_json (prefix ++ w) (list (list ascii * Json)) members_rest_spec tt tt jw j2 ms' Hmany) as Hge_many.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt j2 j3 tt Hws2) as Hge_ws2.
        assert (Hj3lt : j3 < List.length (prefix ++ w)) by (apply (nth_error_Some (prefix ++ w) j3); rewrite Hnth; discriminate).
        lia. }
      assert (Hjw2_gt : List.length prefix < jw2) by lia.
      assert (Hlt : List.length (skipn jw2 (prefix ++ w)) < List.length w).
      { rewrite (skipn_length jw2 (prefix ++ w)). rewrite length_app. rewrite length_app in Hjw2_le. lia. }
      assert (Hcall' : denote json_grammar (firstn jw2 (prefix ++ w) ++ skipn jw2 (prefix ++ w)) value_spec tt (List.length (firstn jw2 (prefix ++ w))) v tt jm).
      { rewrite <- (firstn_skipn jw2 (prefix ++ w)) in Hcall. rewrite firstn_length. rewrite (Nat.min_l jw2 (List.length (prefix ++ w)) Hjw2_le). exact Hcall. }
      assert (Hnodigit : forall c, nth_error (firstn jw2 (prefix ++ w) ++ skipn jw2 (prefix ++ w)) jm = Some c -> is_digitb c = false).
      { intros c Hc. rewrite (firstn_skipn jw2 (prefix ++ w)) in Hc.
        destruct (Nat.lt_ge_cases jm jw) as [Hltjmw | Hgejmw].
        - pose proof (ws_head_char (prefix ++ w) jm jw c Hws_mid Hltjmw Hc) as Hwc. apply (ws_not_digit c Hwc).
        - assert (Hjmw : jm = jw) by (pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jm jw tt Hws_mid) as Hge5; lia). subst jw.
          unfold members_rest_spec in Hmany.
          apply (fst (denote_many_iff ascii unit json_nt json_grammar (prefix ++ w) (list ascii * Json) (Map snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind member_spec (fun m0 : list ascii * Json => Bind ws (fun _ : unit => Pure m0)))))) tt tt jm j2 ms')) in Hmany.
          destruct Hmany as [Hnil | Hcons].
          + destruct Hnil as [[_ _] Ej2]. subst j2.
            destruct (Nat.lt_ge_cases jm j3) as [Hlt2 | Hge2].
            * pose proof (ws_head_char (prefix ++ w) jm j3 c Hws2 Hlt2 Hc) as Hwc. apply (ws_not_digit c Hwc).
            * assert (Hjm3 : jm = j3) by (pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jm j3 tt Hws2) as Hge6; lia). subst j3. rewrite Hnth in Hc. injection Hc as Hc'. subst c. simpl. reflexivity.
          + destruct Hcons as [m' [ms'' [γr [jr [[Ems' Hs_rest] _]]]]]. subst ms'.
            apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * (list ascii * Json)) (list ascii * Json) snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind member_spec (fun m0 : list ascii * Json => Bind ws (fun _ : unit => Pure m0))))) tt γr jm jr m')) in Hs_rest.
            destruct Hs_rest as [p [_ Hseq]].
            apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii * Json) (char ","%char) (Bind ws (fun _ : unit => Bind member_spec (fun m0 : list ascii * Json => Bind ws (fun _ : unit => Pure m0)))) tt γr jm jr p)) in Hseq.
            destruct Hseq as [γc [jc [a [b [[_ Hcomma] _]]]]].
            apply (char_denote_nth (prefix ++ w) ","%char jm jc a γc) in Hcomma.
            destruct Hcomma as [Hnth_comma _].
            rewrite Hnth_comma in Hc. injection Hc as Hc'. subst c. simpl. reflexivity. }
      destruct (fst (IH (skipn jw2 (prefix ++ w)) Hlt) (firstn jw2 (prefix ++ w)) v jm Hcall' Hnodigit) as [fuelv [Hfv_le Hv]].
      rewrite (firstn_skipn jw2 (prefix ++ w)) in Hv.
      assert (Helem_c : forall (w' : list ascii), List.length w' <= List.length w -> forall (w'' : list ascii), List.length w'' < List.length w' -> forall (pre : list ascii) (m : list ascii * Json) (jj : nat),
        denote json_grammar (pre ++ w'') member_spec tt (List.length pre) m tt jj ->
        (forall c : ascii, nth_error (pre ++ w'') jj = Some c -> is_digitb c = false) ->
        parse_member (3 * List.length w'' + 1) (skip_ws w'') = Some (m, skipn jj (pre ++ w''))).
      { intros w' Hle_w' w'' Hlt_w'' pre m jj hden hndigit.
        apply (parse_member_complete (3 * List.length w'' + 1)).
        - intros prefix0 w0 val0 j0 Hlt0 hden_v hndigit_v.
          pose proof (value_input_skip_ws prefix0 w0 val0 j0 hden_v) as hskip.
          destruct (fst (IH w0 (Nat.lt_le_trans (Datatypes.length w0) (Datatypes.length w') (Datatypes.length w) (Nat.lt_trans (Datatypes.length w0) (Datatypes.length w'') (Datatypes.length w') Hlt0 Hlt_w'') Hle_w')) prefix0 val0 j0 hden_v hndigit_v) as [hf [hhf_le hp]].
          assert (hp' : parse_value hf (skip_ws w0) = Some (val0, skipn j0 (prefix0 ++ w0))).
          { exact (eq_ind_r (fun w00 : list ascii => parse_value hf w00 = Some (val0, skipn j0 (prefix0 ++ w0))) hp hskip). }
          apply (parse_value_mono hf (3 * List.length w'' + 1) (skip_ws w0) (val0, skipn j0 (prefix0 ++ w0))).
          + lia.
          + exact hp'.
        - exact hden.
        - exact hndigit. }
      assert (Hfold : forall (w' : list ascii), List.length w' <= List.length w ->
        forall (prefix' : list ascii) (ms'0 : list (list ascii * Json)) (j20 jclose : nat),
          denote json_grammar (prefix' ++ w') members_rest_spec tt (List.length prefix') ms'0 tt j20 ->
          denote json_grammar (prefix' ++ w') ws tt j20 tt tt jclose ->
          nth_error (prefix' ++ w') jclose = Some "}"%char ->
          parse_members_more (3 * List.length w' + 2) (skip_ws w') = Some (ms'0, skipn jclose (prefix' ++ w'))).
      { intros w' Hle_w' prefix' ms'0 j20 jclose Hmany0 Hws0 hnth0.
        rewrite (parse_members_more_equiv_sep_by (3 * List.length w' + 2) (skip_ws w')).
        assert (Hcomma_nw : is_wsb ","%char = false) by (vm_compute; reflexivity).
        assert (Hbrace_nw : is_wsb "}"%char = false) by (vm_compute; reflexivity).
        assert (Hcomma_brace : Ascii.eqb ","%char "}"%char = false) by (vm_compute; reflexivity).
        assert (Hcomma_ndigit : is_digitb ","%char = false) by (vm_compute; reflexivity).
        assert (Hbrace_ndigit : is_digitb "}"%char = false) by (vm_compute; reflexivity).
        exact (sep_by_complete (list ascii * Json) member_spec parse_member ","%char "}"%char
          parse_member_mono parse_member_cons
          Hcomma_nw Hbrace_nw Hcomma_brace Hcomma_ndigit Hbrace_ndigit
          w' (Helem_c w' Hle_w') prefix' ms'0 j20 jclose Hmany0 Hws0 hnth0). }
      assert (Hjw_le : jw <= List.length (prefix ++ w)).
      { pose proof (denote_ge_json (prefix ++ w) (list (list ascii * Json)) members_rest_spec tt tt jw j2 ms' Hmany) as Hg.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt j2 j3 tt Hws2) as Hg0.
        assert (Hj3lt : j3 < List.length (prefix ++ w)) by (apply (nth_error_Some (prefix ++ w) j3); rewrite Hnth; discriminate).
        lia. }
      assert (Hle_w : List.length (skipn jw (prefix ++ w)) <= List.length w).
      { rewrite (skipn_length jw (prefix ++ w)). rewrite length_app. rewrite length_app in Hjw_le.
        pose proof (denote_ge_json (prefix ++ w) Json value_spec tt tt jw2 jm v Hcall) as Hgv.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jm jw tt Hws_mid) as Hgm.
        lia. }
      assert (Hmany' : denote json_grammar (firstn jw (prefix ++ w) ++ skipn jw (prefix ++ w)) members_rest_spec tt (List.length (firstn jw (prefix ++ w))) ms' tt j2).
      { rewrite (firstn_skipn jw (prefix ++ w)). rewrite firstn_length. rewrite (Nat.min_l jw (List.length (prefix ++ w)) Hjw_le). exact Hmany. }
      assert (Hws2' : denote json_grammar (firstn jw (prefix ++ w) ++ skipn jw (prefix ++ w)) ws tt j2 tt tt j3).
      { rewrite (firstn_skipn jw (prefix ++ w)). exact Hws2. }
      assert (Hnth' : nth_error (firstn jw (prefix ++ w) ++ skipn jw (prefix ++ w)) j3 = Some "}"%char).
      { rewrite (firstn_skipn jw (prefix ++ w)). exact Hnth. }
      pose proof (Hfold (skipn jw (prefix ++ w)) Hle_w (firstn jw (prefix ++ w)) ms' j2 j3 Hmany' Hws2' Hnth') as Hrest_parse.
      rewrite (firstn_skipn jw (prefix ++ w)) in Hrest_parse.
      assert (Hv_pad : parse_value (3 * List.length w) (skipn jw2 (prefix ++ w)) = Some (v, skipn jm (prefix ++ w))).
      { apply (parse_value_mono fuelv (3 * List.length w) (skipn jw2 (prefix ++ w)) (v, skipn jm (prefix ++ w))).
        - lia.
        - exact Hv. }
      assert (Hrest_pad : parse_members_more (3 * List.length w) (skip_ws (skipn jw (prefix ++ w))) = Some (ms', skipn j3 (prefix ++ w))).
      { apply (parse_members_more_mono (3 * List.length (skipn jw (prefix ++ w)) + 2) (3 * List.length w) (skip_ws (skipn jw (prefix ++ w))) (ms', skipn j3 (prefix ++ w))).
        - rewrite (skipn_length jw (prefix ++ w)). rewrite length_app.
          pose proof (denote_ge_json (prefix ++ w) Json value_spec tt tt jw2 jm v Hcall) as Hgv.
          pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jm jw tt Hws_mid) as Hgm.
          lia.
        - exact Hrest_parse. }
      assert (Hnws_value : forall c, nth_error (prefix ++ w) jw2 = Some c -> is_wsb c = false).
      { intros c Hc. destruct (is_wsb c) eqn:E; [| reflexivity].
        exfalso. apply (value_no_ws (firstn jw2 (prefix ++ w)) c (skipn (S jw2) (prefix ++ w)) v jm).
        - exact E.
        - replace (firstn jw2 (prefix ++ w) ++ c :: skipn (S jw2) (prefix ++ w)) with (prefix ++ w).
          + replace (List.length (firstn jw2 (prefix ++ w))) with jw2 by (rewrite firstn_length; symmetry; apply Nat.min_l; exact Hjw2_le).
            exact Hcall.
          + rewrite <- (skipn_cons_head ascii (prefix ++ w) jw2 c Hc). rewrite (firstn_skipn jw2 (prefix ++ w)). reflexivity. }
      pose proof (ws_skip_gen (prefix ++ w) (S jw1) jw2 Hws_b Hnws_value) as Hskip_b_ws.
      pose proof (skip_ws_ws (prefix ++ w) jm jw Hws_mid) as Hskip_mid.
      assert (Hbrace_nw : is_wsb "}"%char = false) by (vm_compute; reflexivity).
      pose proof (skip_ws_nonws (prefix ++ w) j3 "}"%char Hnth Hbrace_nw) as Hskip_trail.
      assert (Hnth_quote : nth_error (prefix ++ w) j1 = Some "034"%char).
      { unfold string_spec in Hstr.
        apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list ascii) (char "034") (fun _ : unit => Bind (Many string_char_spec) (fun cs : list ascii => Bind (char "034") (fun _ : unit => Pure cs))) tt tt j1 js s)) in Hstr.
        destruct Hstr as [γq [jq [uq [Hquote _]]]].
        apply (char_denote_nth (prefix ++ w) "034"%char j1 jq uq γq) in Hquote.
        destruct Hquote as [Hnth_q _]. exact Hnth_q. }
      exists (3 * List.length w + 2). split; [lia |].
      replace (3 * List.length w + 2) with (S (3 * List.length w + 1)) by lia.
      replace (3 * List.length w + 1) with (S (3 * List.length w)) by lia.
      assert (Hmembers : parse_members (S (3 * List.length w)) (skip_ws w) = Some ((s, v) :: ms', skipn j3 (prefix ++ w))).
      { cbn [parse_members].
        rewrite Hps. rewrite Hskip1. rewrite (skipn_cons_head ascii (prefix ++ w) j1 "034"%char Hnth_quote).
        cbn [Ascii.eqb].
        rewrite Hskip2. rewrite (skipn_cons_head ascii (prefix ++ w) jw1 ":"%char Hnth_colon).
        cbn [Ascii.eqb].
        rewrite Hskip_b_ws. rewrite Hv_pad.
        cbn [Ascii.eqb].
        rewrite Hskip_mid. rewrite Hrest_pad.
        cbn [Ascii.eqb]. reflexivity. }
      cbn [parse_object]. rewrite Hmembers.
      cbn [Ascii.eqb]. rewrite Hskip_trail. rewrite (skipn_cons_head ascii (prefix ++ w) j3 "}"%char Hnth).
      cbn [Ascii.eqb]. reflexivity.
    intros prefix vs j Hd. unfold array_body_spec in Hd.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) ws (fun _ : unit => Bind elements_spec (fun vs : list Json => Bind ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs)))) tt tt (List.length prefix) j vs)) in Hd.
    destruct Hd as [γ1 [j1 [u [Hws1 Hrest]]]]. destruct u, γ1.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) (list Json) elements_spec (fun vs0 : list Json => Bind ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs0))) tt tt j1 j vs)) in Hrest.
    destruct Hrest as [γ2 [j2 [vs0 [Hel Hrest2]]]]. destruct γ2.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) ws (fun _ : unit => Bind (char "]") (fun _ : unit => Pure vs0)) tt tt j2 j vs)) in Hrest2.
    destruct Hrest2 as [γ3 [j3 [u3 [Hws2 Hrest3]]]]. destruct u3, γ3.
    apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) (char "]") (fun _ : unit => Pure vs0) tt tt j3 j vs)) in Hrest3.
    destruct Hrest3 as [γ4 [j4 [u4 [Hbr Hpure]]]].
    apply (char_denote_nth (prefix ++ w) "]"%char j3 j4 u4 γ4) in Hbr.
    destruct Hbr as [Hnth [Eu4 [Eg4 Ej4]]]. subst u4 γ4 j4.
    apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) vs0 tt (S j3) vs tt j)) in Hpure.
    destruct Hpure as [[Evs0 _] Ej]. subst vs0. subst j.
    unfold elements_spec in Hel.
    apply (fst (denote_alt_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) _ _ tt tt j1 j2 vs)) in Hel.
    destruct Hel as [Hempty | Hcons].
    + (* empty elements *)
      apply (fst (denote_pure_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) (@nil Json) tt j1 vs tt j2)) in Hempty.
      destruct Hempty as [[Evs _] Ej2]. subst vs. subst j2.
      assert (Hnw : forall c, nth_error (prefix ++ w) j3 = Some c -> is_wsb c = false).
      { intros c Hc. rewrite Hnth in Hc. injection Hc as Hc'. subst c. simpl. reflexivity. }
      pose proof (ws_ws_skip prefix w j1 j3 Hws1 Hws2 Hnw) as Hskip.
      exists (S (S O)). split; [lia |]. cbn [parse_array parse_elements].
      rewrite Hskip. rewrite (skipn_cons_head ascii (prefix ++ w) j3 "]"%char Hnth). simpl. reflexivity.
    + (* non-empty elements *)
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) Json (list Json) (Call NT_value) (fun v : Json => Bind ws (fun _ : unit => Map (fun rest : list Json => v :: rest) elements_rest_spec)) tt tt j1 j2 vs)) in Hcons.
      destruct Hcons as [γv [jv [v [Hcall Hel_rest]]]].
      apply (fst (denote_call_iff ascii unit json_nt json_grammar (prefix ++ w) Json NT_value tt γv j1 jv v)) in Hcall.
      cbn [json_grammar] in Hcall.
      apply (fst (denote_bind_iff ascii unit json_nt json_grammar (prefix ++ w) unit (list Json) ws (fun _ : unit => Map (fun rest : list Json => v :: rest) elements_rest_spec) γv tt jv j2 vs)) in Hel_rest.
      destruct Hel_rest as [γw [jw [u [Hws_mid Hel_map]]]].
      apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (list Json) (list Json) (fun rest : list Json => v :: rest) elements_rest_spec γw tt jw j2 vs)) in Hel_map.
      destruct Hel_map as [vs' [Evs Hel_rest2]]. subst vs. destruct γv, γw, u.
      assert (Hj1_le : j1 <= List.length (prefix ++ w)).
      { pose proof (denote_ge_json (prefix ++ w) Json value_spec tt tt j1 jv v Hcall) as Hg1.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jv jw tt Hws_mid) as Hg2.
        pose proof (denote_ge_json (prefix ++ w) (list Json) elements_rest_spec tt tt jw j2 vs' Hel_rest2) as Hg3.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt j2 j3 tt Hws2) as Hg4.
        assert (Hj3lt : j3 < List.length (prefix ++ w)) by (apply (nth_error_Some (prefix ++ w) j3); rewrite Hnth; discriminate).
        lia. }
      assert (Hnws_head : forall c, nth_error (prefix ++ w) j1 = Some c -> is_wsb c = false).
      { intros c Hc. destruct (is_wsb c) eqn:E; [| reflexivity].
        exfalso. apply (value_no_ws (firstn j1 (prefix ++ w)) c (skipn (S j1) (prefix ++ w)) v jv).
        - exact E.
        - replace (firstn j1 (prefix ++ w) ++ c :: skipn (S j1) (prefix ++ w)) with (prefix ++ w).
          + replace (List.length (firstn j1 (prefix ++ w))) with j1 by (rewrite firstn_length; symmetry; apply Nat.min_l; lia).
            exact Hcall.
          + rewrite <- (skipn_cons_head ascii (prefix ++ w) j1 c Hc). rewrite (firstn_skipn j1 (prefix ++ w)). reflexivity. }
      pose proof (ws_skip prefix w j1 Hws1 Hnws_head) as Hskip1.
      pose proof (ws_skip_j prefix w j1 Hws1 Hnws_head) as Hj1.
      assert (Hcall'' : denote json_grammar ((prefix ++ ws_part w) ++ skip_ws w) value_spec tt (List.length (prefix ++ ws_part w)) v tt jv).
      { rewrite <- app_assoc. rewrite (ws_part_skip w). rewrite length_app. rewrite <- Hj1. exact Hcall. }
      assert (Hnodigit : forall c, nth_error (firstn j1 (prefix ++ w) ++ skipn j1 (prefix ++ w)) jv = Some c -> is_digitb c = false).
      { intros c Hc. rewrite (firstn_skipn j1 (prefix ++ w)) in Hc.
        destruct (Nat.lt_ge_cases jv jw) as [Hltjv | Hgejv].
        - pose proof (ws_head_char (prefix ++ w) jv jw c Hws_mid Hltjv Hc) as Hwc. apply (ws_not_digit c Hwc).
        - assert (Hjvj : jv = jw) by (pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jv jw tt Hws_mid) as Hg; lia). subst jw.
          unfold elements_rest_spec in Hel_rest2.
          apply (fst (denote_many_iff ascii unit json_nt json_grammar (prefix ++ w) Json (Map snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind (Call NT_value) (fun v0 : Json => Bind ws (fun _ : unit => Pure v0)))))) tt tt jv j2 vs')) in Hel_rest2.
          destruct Hel_rest2 as [Hnil | Hcons].
          + destruct Hnil as [[_ _] Ej2]. subst j2.
            destruct (Nat.lt_ge_cases jv j3) as [Hlt2 | Hge2].
            * pose proof (ws_head_char (prefix ++ w) jv j3 c Hws2 Hlt2 Hc) as Hwc. apply (ws_not_digit c Hwc).
            * assert (Hjv3 : jv = j3) by (pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jv j3 tt Hws2) as Hg; lia). subst j3. rewrite Hnth in Hc. injection Hc as Hc'. subst c. simpl. reflexivity.
          + destruct Hcons as [vv [vs'' [γr [jr [[Evs' Hs_rest] _]]]]]. subst vs'.
            apply (fst (denote_map_iff ascii unit json_nt json_grammar (prefix ++ w) (unit * Json) Json snd (Seq (char ","%char) (Bind ws (fun _ : unit => Bind (Call NT_value) (fun v0 : Json => Bind ws (fun _ : unit => Pure v0))))) tt γr jv jr vv)) in Hs_rest.
            destruct Hs_rest as [p [_ Hseq]].
            apply (fst (denote_seq_iff ascii unit json_nt json_grammar (prefix ++ w) unit Json (char ","%char) (Bind ws (fun _ : unit => Bind (Call NT_value) (fun v0 : Json => Bind ws (fun _ : unit => Pure v0)))) tt γr jv jr p)) in Hseq.
            destruct Hseq as [γc [jc [a [b [[_ Hcomma] _]]]]].
            apply (char_denote_nth (prefix ++ w) ","%char jv jc a γc) in Hcomma.
            destruct Hcomma as [Hnth_comma _].
            rewrite Hnth_comma in Hc. injection Hc as Hc'. subst c. simpl. reflexivity. }
      assert (Hnodigit'' : forall c, nth_error ((prefix ++ ws_part w) ++ skip_ws w) jv = Some c -> is_digitb c = false).
      { intros c Hc. rewrite <- app_assoc in Hc. rewrite (ws_part_skip w) in Hc. apply Hnodigit. rewrite (firstn_skipn j1 (prefix ++ w)). exact Hc. }
      assert (Hvalue : {fuel : nat & prod (fuel <= 3 * List.length w) (parse_value fuel (skip_ws w) = Some (v, skipn jv (prefix ++ w)))}).
      { destruct (ws_part w) as [| c0 wsw] eqn:Ewp.
        - assert (Hskip_eq : skip_ws w = w) by (rewrite <- (ws_part_skip w) at 2; rewrite Ewp; reflexivity).
          rewrite Hskip_eq in Hcall''. rewrite app_nil_r in Hcall''.
          rewrite Hskip_eq in Hnodigit''. rewrite app_nil_r in Hnodigit''.
          destruct (Vst_w prefix v jv Hcall'' Hnodigit'') as [fuelv [Hfv_le Hv]].
          rewrite <- Hskip_eq in Hv at 1. exists fuelv. split; [exact Hfv_le | exact Hv].
        - rewrite <- Ewp in Hcall''. rewrite <- Ewp in Hnodigit''.
          assert (Hlt : List.length (skip_ws w) < List.length w).
          { rewrite <- (ws_part_skip w) at 2. rewrite Ewp. simpl. rewrite length_app. simpl. lia. }
          destruct (fst (IH (skip_ws w) Hlt) (prefix ++ ws_part w) v jv Hcall'' Hnodigit'') as [fuelv [Hfv_le Hv]].
          rewrite <- app_assoc in Hv. rewrite (ws_part_skip w) in Hv.
          exists fuelv. split; [| exact Hv].
          assert (Hskip_le : List.length (skip_ws w) <= List.length w) by (rewrite <- (ws_part_skip w) at 2; rewrite length_app; lia).
          lia. }
      destruct Hvalue as [fuelv [Hfv_le Hv]].
      assert (Helem_c : forall (w' : list ascii), List.length w' <= List.length w -> forall (w'' : list ascii), List.length w'' < List.length w' -> forall (pre : list ascii) (val : Json) (jj : nat),
        denote json_grammar (pre ++ w'') (Call NT_value) tt (List.length pre) val tt jj ->
        (forall c : ascii, nth_error (pre ++ w'') jj = Some c -> is_digitb c = false) ->
        parse_value (3 * List.length w'' + 1) (skip_ws w'') = Some (val, skipn jj (pre ++ w''))).
      { intros w' Hle_w' w'' Hlt_w'' pre val jj hden hndigit.
        pose proof (value_complete_call pre w'' val jj hden) as hval.
        pose proof (value_input_skip_ws pre w'' val jj hval) as hskip.
        destruct (fst (IH w'' (Nat.lt_le_trans (Datatypes.length w'') (Datatypes.length w') (Datatypes.length w) Hlt_w'' Hle_w')) pre val jj hval hndigit) as [hf [hhf_le hp]].
        assert (hp' : parse_value hf (skip_ws w'') = Some (val, skipn jj (pre ++ w''))).
        { exact (eq_ind_r (fun w0 : list ascii => parse_value hf w0 = Some (val, skipn jj (pre ++ w''))) hp hskip). }
        apply (parse_value_mono hf (3 * List.length w'' + 1) (skip_ws w'') (val, skipn jj (pre ++ w''))).
        - lia.
        - exact hp'. }
      assert (Hfold : forall (w' : list ascii), List.length w' <= List.length w ->
        forall (prefix' : list ascii) (vs'0 : list Json) (j20 jclose : nat),
          denote json_grammar (prefix' ++ w') elements_rest_spec tt (List.length prefix') vs'0 tt j20 ->
          denote json_grammar (prefix' ++ w') ws tt j20 tt tt jclose ->
          nth_error (prefix' ++ w') jclose = Some "]"%char ->
          parse_elements_more (3 * List.length w' + 2) (skip_ws w') = Some (vs'0, skipn jclose (prefix' ++ w'))).
      { intros w' Hle_w' prefix' vs'0 j20 jclose Hmany Hws hnth0.
        rewrite (parse_elements_more_equiv_sep_by (3 * List.length w' + 2) (skip_ws w')).
        assert (Hcomma_nw : is_wsb ","%char = false) by (vm_compute; reflexivity).
        assert (Hbracket_nw : is_wsb "]"%char = false) by (vm_compute; reflexivity).
        assert (Hcomma_bracket : Ascii.eqb ","%char "]"%char = false) by (vm_compute; reflexivity).
        assert (Hcomma_ndigit : is_digitb ","%char = false) by (vm_compute; reflexivity).
        assert (Hbracket_ndigit : is_digitb "]"%char = false) by (vm_compute; reflexivity).
        exact (sep_by_complete Json (Call NT_value) parse_value ","%char "]"%char
          parse_value_mono
          (fun pre w0 val jj hden => value_consumes pre w0 val jj (value_complete_call pre w0 val jj hden))
          Hcomma_nw Hbracket_nw Hcomma_bracket Hcomma_ndigit Hbracket_ndigit
          w' (Helem_c w' Hle_w') prefix' vs'0 j20 jclose Hmany Hws hnth0). }
      assert (Hjw_le : jw <= List.length (prefix ++ w)).
      { pose proof (denote_ge_json (prefix ++ w) (list Json) elements_rest_spec tt tt jw j2 vs' Hel_rest2) as Hg.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt j2 j3 tt Hws2) as Hg0.
        assert (Hj3lt : j3 < List.length (prefix ++ w)) by (apply (nth_error_Some (prefix ++ w) j3); rewrite Hnth; discriminate).
        lia. }
      assert (Hle_w : List.length (skipn jw (prefix ++ w)) <= List.length w).
      { rewrite (skipn_length jw (prefix ++ w)). rewrite length_app. rewrite length_app in Hjw_le.
        pose proof (denote_ge_json (prefix ++ w) Json value_spec tt tt j1 jv v Hcall) as Hgv.
        pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jv jw tt Hws_mid) as Hgm.
        lia. }
      assert (Hel_rest2' : denote json_grammar (firstn jw (prefix ++ w) ++ skipn jw (prefix ++ w)) elements_rest_spec tt (List.length (firstn jw (prefix ++ w))) vs' tt j2).
      { rewrite (firstn_skipn jw (prefix ++ w)). rewrite firstn_length. rewrite (Nat.min_l jw (List.length (prefix ++ w)) Hjw_le). exact Hel_rest2. }
      assert (Hws2' : denote json_grammar (firstn jw (prefix ++ w) ++ skipn jw (prefix ++ w)) ws tt j2 tt tt j3).
      { rewrite (firstn_skipn jw (prefix ++ w)). exact Hws2. }
      assert (Hnth' : nth_error (firstn jw (prefix ++ w) ++ skipn jw (prefix ++ w)) j3 = Some "]"%char).
      { rewrite (firstn_skipn jw (prefix ++ w)). exact Hnth. }
      pose proof (Hfold (skipn jw (prefix ++ w)) Hle_w (firstn jw (prefix ++ w)) vs' j2 j3 Hel_rest2' Hws2' Hnth') as Hrest_parse.
      rewrite (firstn_skipn jw (prefix ++ w)) in Hrest_parse.
      assert (Hv_pad : parse_value (3 * List.length w) (skip_ws w) = Some (v, skipn jv (prefix ++ w))).
      { apply (parse_value_mono fuelv (3 * List.length w) (skip_ws w) (v, skipn jv (prefix ++ w))).
        - lia.
        - exact Hv. }
      assert (Hrest_pad : parse_elements_more (3 * List.length w) (skip_ws (skipn jw (prefix ++ w))) = Some (vs', skipn j3 (prefix ++ w))).
      { apply (parse_elements_more_mono (3 * List.length (skipn jw (prefix ++ w)) + 2) (3 * List.length w) (skip_ws (skipn jw (prefix ++ w))) (vs', skipn j3 (prefix ++ w))).
        - rewrite (skipn_length jw (prefix ++ w)). rewrite length_app.
          pose proof (denote_ge_json (prefix ++ w) Json value_spec tt tt j1 jv v Hcall) as Hgv.
          pose proof (denote_ge_json (prefix ++ w) unit ws tt tt jv jw tt Hws_mid) as Hgm.
          assert (Hcall_vc : denote json_grammar (firstn j1 (prefix ++ w) ++ skipn j1 (prefix ++ w)) value_spec tt (List.length (firstn j1 (prefix ++ w))) v tt jv).
          { rewrite (firstn_skipn j1 (prefix ++ w)). rewrite firstn_length. rewrite (Nat.min_l j1 (List.length (prefix ++ w)) Hj1_le). exact Hcall. }
          pose proof (value_consumes (firstn j1 (prefix ++ w)) (skipn j1 (prefix ++ w)) v jv Hcall_vc) as Hj1ltjv.
          rewrite firstn_length in Hj1ltjv. rewrite (Nat.min_l j1 (List.length (prefix ++ w)) Hj1_le) in Hj1ltjv.
          assert (Hpfx_lt_jw : List.length prefix < jw) by (rewrite Hj1 in Hj1ltjv; lia).
          rewrite length_app in Hjw_le. lia.
        - exact Hrest_parse. }
      pose proof (skip_ws_ws (prefix ++ w) jv jw Hws_mid) as Hskip_mid.
      assert (Hbracket_nw : is_wsb "]"%char = false) by (vm_compute; reflexivity).
      pose proof (skip_ws_nonws (prefix ++ w) j3 "]"%char Hnth Hbracket_nw) as Hskip_trail.
      assert (Hcall_vc : denote json_grammar (firstn j1 (prefix ++ w) ++ skipn j1 (prefix ++ w)) value_spec tt (List.length (firstn j1 (prefix ++ w))) v tt jv).
      { rewrite (firstn_skipn j1 (prefix ++ w)). rewrite firstn_length. rewrite (Nat.min_l j1 (List.length (prefix ++ w)) Hj1_le). exact Hcall. }
      destruct (value_first_char (firstn j1 (prefix ++ w)) (skipn j1 (prefix ++ w)) v jv Hcall_vc) as [c [rest [Ew Hnotclose]]].
      rewrite Hskip1 in Hv_pad. rewrite Ew in Hv_pad.
      exists (3 * List.length w + 2). split; [lia |].
      replace (3 * List.length w + 2) with (S (S (3 * List.length w))) by lia.
      cbn [parse_array parse_elements].
      rewrite Hskip1. rewrite Ew. cbn [parse_elements].
      rewrite Hnotclose. cbn [parse_elements].
      rewrite Hv_pad.
      cbn [parse_elements Ascii.eqb].
      rewrite Hskip_mid. rewrite Hrest_pad.
      cbn [parse_elements Ascii.eqb].
      rewrite Hskip_trail. rewrite (skipn_cons_head ascii (prefix ++ w) j3 "]"%char Hnth).
      cbn [Ascii.eqb]. reflexivity.
Qed.


Lemma ws_denote_char (w : list ascii) (j : nat) (c : ascii) :
  denote json_grammar w ws tt j tt tt (List.length w) ->
  nth_error w j = Some c -> is_wsb c = true.
Proof.
  intros Hd Hnth. unfold ws in Hd.
  apply (fst (denote_map_iff ascii unit json_nt json_grammar w (list ascii) unit (fun _ : list ascii => tt) (Many (Tok (fun c : ascii => is_wsb c = true))) tt tt j (List.length w) tt)) in Hd.
  destruct Hd as [wsl [_ Hmany]].
  destruct wsl as [| c0 wsl].
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt j (List.length w) (@nil ascii))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[_ _] Ej]. subst. rewrite (nth_error_self_none w) in Hnth. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E _] _]]]]]. discriminate.
  - apply (fst (denote_many_iff ascii unit json_nt json_grammar w ascii (Tok (fun c : ascii => is_wsb c = true)) tt tt j (List.length w) (c0 :: wsl))) in Hmany.
    destruct Hmany as [Hnil | Hcons].
    + destruct Hnil as [[E _] _]. discriminate.
    + destruct Hcons as [a [as' [γ'' [k [[E Hone] _]]]]].
      injection E as Ea Eas. subst a as'.
      apply (fst (denote_tok_iff ascii unit json_nt json_grammar w (fun c : ascii => is_wsb c = true) c0 tt γ'' j k)) in Hone.
      destruct Hone as [[[_ _] Hnth'] HP].
      rewrite Hnth' in Hnth. injection Hnth as Hc. subst c0. exact HP.
Qed.


(* Whole-document completeness. *)
Lemma parse_json_complete (w : list ascii) (v : Json) :
  denote json_grammar w json_text tt 0 v tt (List.length w) ->
  parse_json w = Some v.
Proof.
  intros Hd. unfold json_text in Hd.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar w unit Json ws (fun _ : unit => Bind (Call NT_value) (fun v : Json => Bind ws (fun _ : unit => Pure v))) tt tt 0 (List.length w) v)) in Hd.
  destruct Hd as [γ1 [j1 [u [Hws1 Hrest]]]]. destruct u, γ1.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar w Json Json (Call NT_value) (fun v0 : Json => Bind ws (fun _ : unit => Pure v0)) tt tt j1 (List.length w) v)) in Hrest.
  destruct Hrest as [γ2 [j2 [v0 [Hcall Hrest2]]]]. destruct γ2.
  apply (fst (denote_call_iff ascii unit json_nt json_grammar w Json NT_value tt tt j1 j2 v0)) in Hcall.
  cbn [json_grammar] in Hcall.
  apply (fst (denote_bind_iff ascii unit json_nt json_grammar w unit Json ws (fun _ : unit => Pure v0) tt tt j2 (List.length w) v)) in Hrest2.
  destruct Hrest2 as [γ3 [j3 [u3 [Hws2 Hpure]]]]. destruct u3, γ3.
  apply (fst (denote_pure_iff ascii unit json_nt json_grammar w Json v0 tt j3 v tt (List.length w))) in Hpure.
  destruct Hpure as [[Ev _] Ej]. subst v0. subst j3.
  (* leading ws maximal: j1 = length (ws_part w) *)
  assert (Hj1 : j1 = List.length (ws_part w)).
  { pose proof (ws_denote_j w 0 j1 Hws1) as Hle1. simpl in Hle1.
    assert (Hge1 : List.length (ws_part w) <= j1).
    { destruct (Nat.lt_ge_cases j1 (List.length (ws_part w))) as [Hlt | Hge]; [| exact Hge].
      exfalso.
      assert (Hltw : j1 < List.length w).
      { assert (Hwslen : List.length (ws_part w) <= List.length w) by (clear; induction w; simpl; [lia |]; destruct (is_wsb a) eqn:E; simpl; lia).
        lia. }
      destruct (nth_error w j1) as [c |] eqn:E.
      - pose proof (ws_part_char_ws w j1 c Hlt E) as Hwc.
        apply (value_no_ws (firstn j1 w) c (skipn (S j1) w) v j2 Hwc).
        replace (firstn j1 w ++ c :: skipn (S j1) w) with w by (rewrite <- (skipn_cons_head ascii w j1 c E); rewrite (firstn_skipn j1 w); reflexivity).
        replace (List.length (firstn j1 w)) with j1 by (rewrite firstn_length; symmetry; apply Nat.min_l; lia).
        exact Hcall.
      - apply nth_error_None in E. lia. }
    lia. }
  rewrite Hj1 in Hcall.
  assert (Hcall' : denote json_grammar (ws_part w ++ skip_ws w) value_spec tt (List.length (ws_part w)) v tt j2).
  { rewrite (ws_part_skip w). exact Hcall. }
  assert (Hnodigit : forall c, nth_error (ws_part w ++ skip_ws w) j2 = Some c -> is_digitb c = false).
  { intros c Hc. apply ws_not_digit. eapply (ws_denote_char w j2 c).
    - exact Hws2.
    - rewrite (ws_part_skip w) in Hc. exact Hc. }
  destruct (fst (complete_value_object_array (skip_ws w)) (ws_part w) v j2 Hcall' Hnodigit) as [fuel [Hfuel_le Hparse]].
  rewrite (ws_part_skip w) in Hparse.
  unfold parse_json.
  assert (Hskip_le : List.length (skip_ws w) <= List.length w).
  { pose proof (length_ws_part_skip w). lia. }
  assert (Hpv : parse_value (3 * List.length w + 2) (skip_ws w) = Some (v, skipn j2 w)).
  { apply (parse_value_mono fuel (3 * List.length w + 2) (skip_ws w) (v, skipn j2 w)).
    - lia.
    - exact Hparse. }
  rewrite Hpv. simpl.
  assert (Hnonws : forall c, nth_error w (List.length w) = Some c -> is_wsb c = false).
  { intros c Hc. rewrite (nth_error_self_none w) in Hc. discriminate. }
  pose proof (ws_skip_gen w j2 (List.length w) Hws2 Hnonws) as Hskip.
  rewrite Hskip.
  assert (Hskip_all : skipn (List.length w) w = []).
  { apply length_zero_iff_nil. rewrite skipn_length. lia. }
  rewrite Hskip_all. simpl. reflexivity.
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
