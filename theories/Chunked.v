(* S6 — HTTP/1.1 chunked transfer coding (RFC 9112 §7.1).

   The essential dependent grammar:

       Chunk := Bind HexNatural (fun n =>
                  if n = 0 then LastChunk
                  else Seq (Exactly n Octet) CRLF)

   A non-final chunk is `size CRLF data CRLF` (data is *exactly* the `size`
   bytes); a zero-size chunk (`0 CRLF`) terminates the body.  The slice uses
   `Token = ascii` (bytes as chars), no escapes, no chunk extensions, and an
   unbounded hexadecimal size (no machine-size falsehood — RP §6.3). *)

From Stdlib Require Import List Ascii String ZArith Bool Lia.
Import ListNotations.
From Parsebot Require Import Spec.

(* ------------------------------------------------------------------------- *)
(* 1. Nonterminals                                                            *)
(* ------------------------------------------------------------------------- *)

(* Chunked transfer coding has no recursion: a chunk is a flat value-dependent
   parse.  The nonterminal family is therefore empty. *)
Inductive chunked_nt : Type -> Type := .

Definition empty_grammar : Grammar ascii unit chunked_nt :=
  fun (A : Type) (n : chunked_nt A) => match n with end.

(* ------------------------------------------------------------------------- *)
(* 2. Hexadecimal sizes                                                       *)
(* ------------------------------------------------------------------------- *)

Definition is_hex_digitb (c : ascii) : bool :=
  Ascii.eqb c "0"%char || Ascii.eqb c "1"%char || Ascii.eqb c "2"%char
  || Ascii.eqb c "3"%char || Ascii.eqb c "4"%char || Ascii.eqb c "5"%char
  || Ascii.eqb c "6"%char || Ascii.eqb c "7"%char || Ascii.eqb c "8"%char
  || Ascii.eqb c "9"%char
  || Ascii.eqb c "a"%char || Ascii.eqb c "b"%char || Ascii.eqb c "c"%char
  || Ascii.eqb c "d"%char || Ascii.eqb c "e"%char || Ascii.eqb c "f"%char
  || Ascii.eqb c "A"%char || Ascii.eqb c "B"%char || Ascii.eqb c "C"%char
  || Ascii.eqb c "D"%char || Ascii.eqb c "E"%char || Ascii.eqb c "F"%char.

Definition hex_val (c : ascii) : nat :=
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
  else if Ascii.eqb c "a"%char then 10
  else if Ascii.eqb c "b"%char then 11
  else if Ascii.eqb c "c"%char then 12
  else if Ascii.eqb c "d"%char then 13
  else if Ascii.eqb c "e"%char then 14
  else if Ascii.eqb c "f"%char then 15
  else if Ascii.eqb c "A"%char then 10
  else if Ascii.eqb c "B"%char then 11
  else if Ascii.eqb c "C"%char then 12
  else if Ascii.eqb c "D"%char then 13
  else if Ascii.eqb c "E"%char then 14
  else if Ascii.eqb c "F"%char then 15
  else 0.

Definition hex_digits_to_nat (cs : list ascii) : nat :=
  List.fold_left (fun acc c => 16 * acc + hex_val c) cs 0.

(* ------------------------------------------------------------------------- *)
(* 3. Specs                                                                   *)
(* ------------------------------------------------------------------------- *)

Definition char (c : ascii) : Spec ascii unit chunked_nt unit :=
  Map (fun _ : ascii => tt) (Tok (fun c' => c' = c)).

(* CRLF := "\r" "\n" *)
Definition crlf : Spec ascii unit chunked_nt unit :=
  Map (fun _ : unit * unit => tt) (Seq (char "013"%char) (char "010"%char)).

Definition hex_digit_spec : Spec ascii unit chunked_nt ascii :=
  Tok (fun c => is_hex_digitb c = true).

(* chunk-size := 1*HEXDIG  (at least one digit, unbounded value) *)
Definition hex_natural_spec : Spec ascii unit chunked_nt nat :=
  Map (fun p : ascii * list ascii => hex_digits_to_nat (fst p :: snd p))
      (Seq hex_digit_spec (Many hex_digit_spec)).

(* Octet := any byte *)
Definition octet_spec : Spec ascii unit chunked_nt ascii :=
  Tok (fun _ => True).

(* A chunk produces its payload (the exactly-`n` data octets); a zero chunk
   produces nil. *)
Definition chunk_spec : Spec ascii unit chunked_nt (list ascii) :=
  Bind hex_natural_spec (fun n : nat =>
    if n =? 0 then
      Map (fun _ : unit => nil) crlf
    else
      Map (fun p : unit * (list ascii * unit) => fst (snd p))
          (Seq crlf (Seq (Exactly n octet_spec) crlf))).

(* chunked-body := *chunk ; the decoded content is the concatenated payloads. *)
Definition chunked_body_spec : Spec ascii unit chunked_nt (list ascii) :=
  Map (@List.concat ascii) (Many chunk_spec).

(* ------------------------------------------------------------------------- *)
(* 4. Parser                                                                  *)
(* ------------------------------------------------------------------------- *)

Fixpoint parse_hex_rest (w : list ascii) : option (list ascii * list ascii) :=
  match w with
  | [] => Some ([], [])
  | c :: rest =>
      if is_hex_digitb c then
        match parse_hex_rest rest with
        | Some (ds, rest') => Some (c :: ds, rest')
        | None => None
        end
      else Some ([], w)
  end.

Definition parse_hex_size (w : list ascii) : option (nat * list ascii) :=
  match w with
  | [] => None
  | c :: rest =>
      if is_hex_digitb c then
        match parse_hex_rest rest with
        | Some (ds, rest') => Some (hex_digits_to_nat (c :: ds), rest')
        | None => None
        end
      else None
  end.

(* Exactly n: consume exactly n octets, or fail. *)
Definition parse_exactly (n : nat) (w : list ascii) : option (list ascii * list ascii) :=
  if n <=? List.length w then Some (List.firstn n w, List.skipn n w) else None.

Definition parse_chunk (w : list ascii) : option (list ascii * list ascii) :=
  match parse_hex_size w with
  | None => None
  | Some (n, rest0) =>
      match rest0 with
      | [] => None
      | c1 :: rest1 =>
          if Ascii.eqb c1 "013"%char then
            match rest1 with
            | [] => None
            | c2 :: rest2 =>
                if Ascii.eqb c2 "010"%char then
                  if n =? 0 then Some ([], rest2)
                  else
                    match parse_exactly n rest2 with
                    | None => None
                    | Some (data, rest3) =>
                        match rest3 with
                        | [] => None
                        | c3 :: rest4 =>
                            if Ascii.eqb c3 "013"%char then
                              match rest4 with
                              | [] => None
                              | c4 :: rest5 =>
                                  if Ascii.eqb c4 "010"%char then Some (data, rest5) else None
                              end
                            else None
                        end
                    end
                else None
            end
          else None
      end
  end.

Fixpoint parse_body (fuel : nat) (w : list ascii) : option (list ascii * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match parse_chunk w with
      | None => None
      | Some ([], rest) => Some ([], rest)          (* zero chunk terminates *)
      | Some (data, rest) =>
          match parse_body fuel' rest with
          | None => None
          | Some (rest_data, rest') => Some (data ++ rest_data, rest')
          end
      end
  end.

(* The whole body: chunks, then the terminating CRLF, then end of input. *)
Definition parse_chunked_body (w : list ascii) : option (list ascii) :=
  match parse_body (3 * List.length w + 2) w with
  | Some (data, rest) =>
      match rest with
      | c1 :: c2 :: [] =>
          if Ascii.eqb c1 "013"%char && Ascii.eqb c2 "010"%char then Some data else None
      | _ => None
      end
  | None => None
  end.

(* ------------------------------------------------------------------------- *)
(* 5. Example: decode "5 CRLF hello CRLF 0 CRLF CRLF" -> "hello"              *)
(* ------------------------------------------------------------------------- *)

Definition ex_input : list ascii :=
  ["5"%char; "013"%char; "010"%char;
   "h"%char; "e"%char; "l"%char; "l"%char; "o"%char;
   "013"%char; "010"%char;
   "0"%char; "013"%char; "010"%char;
   "013"%char; "010"%char].

Eval compute in parse_chunked_body ex_input.
Eval compute in parse_chunk ["5"%char; "013"%char; "010"%char; "h"%char; "e"%char; "l"%char; "l"%char; "o"%char; "013"%char; "010"%char].

(* ------------------------------------------------------------------------- *)
(* 6. Soundness: the parser only produces real denotations                   *)
(* ------------------------------------------------------------------------- *)

Lemma nth_error_app_cons (x : ascii) (prefix rest : list ascii) :
  nth_error (prefix ++ x :: rest) (List.length prefix) = Some x.
Proof.
  induction prefix as [| p ps IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma octet_sound (c : ascii) (prefix rest : list ascii) :
  denote empty_grammar (prefix ++ c :: rest) octet_spec tt (List.length prefix) c tt (S (List.length prefix)).
Proof.
  unfold octet_spec. apply d_tok; [ exact (nth_error_app_cons c prefix rest) | exact I ].
Qed.

Lemma char_sound (c : ascii) (prefix rest : list ascii) :
  denote empty_grammar (prefix ++ c :: rest) (char c) tt (List.length prefix) tt tt (S (List.length prefix)).
Proof.
  unfold char. apply d_map with (a := c). apply d_tok.
  - exact (nth_error_app_cons c prefix rest).
  - reflexivity.
Qed.

Lemma nth_error_app_cons2 (x : ascii) (prefix rest : list ascii) :
  nth_error (prefix ++ x :: rest) (S (List.length prefix)) = nth_error rest 0.
Proof.
  induction prefix as [| p ps IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma app_cons_snoc (A : Type) (prefix rest : list A) (c : A) :
  prefix ++ c :: rest = (prefix ++ c :: []) ++ rest.
Proof.
  intros. rewrite <- app_assoc. reflexivity.
Qed.

Lemma crlf_sound (prefix rest : list ascii) :
  denote empty_grammar (prefix ++ "013"%char :: "010"%char :: rest) crlf tt (List.length prefix) tt tt (S (S (List.length prefix))).
Proof.
  unfold crlf. apply d_map with (a := (tt, tt)).
  apply (d_seq ascii unit chunked_nt empty_grammar (prefix ++ "013"%char :: "010"%char :: rest) unit unit (char "013"%char) (char "010"%char) tt tt tt (List.length prefix) (S (List.length prefix)) (S (S (List.length prefix))) tt tt).
  - apply char_sound.
  - unfold char. apply d_map with (a := "010"%char). apply d_tok.
    + rewrite nth_error_app_cons2. reflexivity.
    + reflexivity.
Qed.

(* Many hex digits: parse_hex_rest collects digits until a non-hex char. *)
Lemma parse_hex_rest_sound (prefix w : list ascii) (ds rest : list ascii) :
  parse_hex_rest w = Some (ds, rest) ->
  denote empty_grammar (prefix ++ w) (Many hex_digit_spec) tt (List.length prefix) ds tt (List.length prefix + List.length w - List.length rest).
Proof.
  revert prefix ds rest. induction w as [| c w' IH]; intros prefix ds rest H.
  - cbn in H. injection H as Hds Hrest. subst ds rest.
    simpl. replace (List.length prefix + 0 - 0) with (List.length prefix) by lia. apply d_many_nil.
  - cbn in H. destruct (is_hex_digitb c) eqn:Ehex.
    + remember (parse_hex_rest w') as pw eqn:Erec.
      destruct pw as [[ds' rest'] |]; [| discriminate].
      injection H as Hds Hrest. subst ds rest.
      eapply d_many_cons.
      * unfold hex_digit_spec. apply d_tok; [ exact (nth_error_app_cons c prefix w') | exact Ehex ].
      * replace (prefix ++ c :: w') with ((prefix ++ c :: []) ++ w')
          by (rewrite <- app_assoc; reflexivity).
        replace (S (List.length prefix)) with (List.length (prefix ++ c :: []))
          by (rewrite app_length; simpl; lia).
        replace (List.length prefix + List.length (c :: w') - List.length rest')
          with (List.length (prefix ++ c :: []) + List.length w' - List.length rest')
          by (simpl; rewrite app_length; simpl; lia).
        apply (IH (prefix ++ c :: []) ds' rest' eq_refl).
    + injection H as Hds Hrest. subst ds rest.
      simpl. replace (List.length prefix + S (List.length w') - S (List.length w')) with (List.length prefix) by lia. apply d_many_nil.
Qed.

Lemma parse_hex_size_sound (prefix w : list ascii) (n : nat) (rest : list ascii) :
  parse_hex_size w = Some (n, rest) ->
  denote empty_grammar (prefix ++ w) hex_natural_spec tt (List.length prefix) n tt (List.length prefix + List.length w - List.length rest).
Proof.
  unfold parse_hex_size. destruct w as [| c w']; [discriminate |].
  intros H. destruct (is_hex_digitb c) eqn:Ehex; [| discriminate].
  destruct (parse_hex_rest w') as [[ds rest'] |] eqn:Erec; [| discriminate].
  injection H as Hn Hrest. subst n rest.
  unfold hex_natural_spec. apply d_map with (a := (c, ds)). eapply d_seq.
  - unfold hex_digit_spec. apply d_tok; [ exact (nth_error_app_cons c prefix w') | exact Ehex ].
  - replace (prefix ++ c :: w') with ((prefix ++ c :: []) ++ w')
      by (rewrite <- app_assoc; reflexivity).
    replace (S (List.length prefix)) with (List.length (prefix ++ c :: []))
      by (rewrite app_length; simpl; lia).
    replace (List.length prefix + List.length (c :: w') - List.length rest')
      with (List.length (prefix ++ c :: []) + List.length w' - List.length rest')
      by (simpl; rewrite app_length; simpl; lia).
    apply (parse_hex_rest_sound (prefix ++ c :: []) w' ds rest' Erec).
Qed.

(* Exactly n octets. *)
Lemma parse_exactly_sound (n : nat) (prefix w : list ascii) (data rest : list ascii) :
  parse_exactly n w = Some (data, rest) ->
  denote empty_grammar (prefix ++ w) (Exactly n octet_spec) tt (List.length prefix) data tt (List.length prefix + List.length w - List.length rest).
Proof.
  revert prefix w data rest. induction n as [| n' IH]; intros prefix w data rest H.
  - cbn in H. injection H as Hd Hr. subst data rest.
    cbn. replace (List.length prefix + List.length w - List.length w) with (List.length prefix) by lia. apply d_exactly_nil.
  - unfold parse_exactly in H. destruct (S n' <=? List.length w) eqn:Hle; [| cbn in H; discriminate].
    rewrite Nat.leb_le in Hle.
    destruct w as [| h tl]; [exfalso; cbn in Hle; lia |].
    injection H as Hd Hr. subst data rest.
    eapply d_exactly_cons.
    + apply octet_sound.
    + cbn [List.length].
      replace (prefix ++ h :: tl) with ((prefix ++ h :: []) ++ tl)
        by (rewrite <- app_assoc; reflexivity).
      replace (S (List.length prefix)) with (List.length (prefix ++ h :: []))
        by (rewrite app_length; simpl; lia).
      replace (List.length prefix + S (List.length tl) - List.length (skipn n' tl))
        with (List.length (prefix ++ h :: []) + List.length tl - List.length (skipn n' tl))
        by (rewrite app_length; simpl; lia).
      apply (IH (prefix ++ h :: []) tl (List.firstn n' tl) (List.skipn n' tl)).
      assert (Hleb : (n' <=? List.length tl) = true).
      { apply (proj2 (Nat.leb_le n' (List.length tl))). cbn in Hle. lia. }
      unfold parse_exactly. rewrite Hleb. reflexivity.
Qed.

(* Consumed-prefix facts: the parser's result is a suffix of the input. *)
Lemma parse_hex_rest_prefix (w : list ascii) (ds rest : list ascii) :
  parse_hex_rest w = Some (ds, rest) -> ds ++ rest = w.
Proof.
  revert ds rest. induction w as [| c w' IH]; intros ds rest H.
  - cbn in H. injection H as Hds Hrest. subst ds rest. reflexivity.
  - cbn in H. destruct (is_hex_digitb c) eqn:Ehex.
    + remember (parse_hex_rest w') as pw eqn:Erec.
      destruct pw as [[ds' rest'] |]; [| discriminate].
      injection H as Hds Hrest. subst ds rest.
      specialize (IH ds' rest' eq_refl). simpl. rewrite IH. reflexivity.
    + injection H as Hds Hrest. subst ds rest. reflexivity.
Qed.

Lemma parse_hex_size_prefix (w : list ascii) (n : nat) (rest : list ascii) :
  parse_hex_size w = Some (n, rest) -> { ds : list ascii & ds ++ rest = w }.
Proof.
  unfold parse_hex_size. destruct w as [| c w']; [discriminate |].
  intros H. destruct (is_hex_digitb c) eqn:Ehex; [| discriminate].
  remember (parse_hex_rest w') as pw eqn:Erec.
  destruct pw as [[ds rest'] |]; [| discriminate].
  injection H as Hn Hrest. subst n rest.
  exists (c :: ds). simpl. symmetry in Erec. rewrite (parse_hex_rest_prefix w' ds rest' Erec). reflexivity.
Qed.

Lemma parse_exactly_prefix (n : nat) (w : list ascii) (data rest : list ascii) :
  parse_exactly n w = Some (data, rest) -> data ++ rest = w.
Proof.
  unfold parse_exactly. intros H.
  destruct (n <=? List.length w) eqn:Hle; [| discriminate].
  injection H as Hd Hr. subst data rest.
  apply List.firstn_skipn.
Qed.
