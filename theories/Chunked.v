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
   produces nil.  `chunk_spec` is the *unified* chunk (zero or non-zero), used
   by the parser.  The body grammar below needs the two cases separated: the
   body is `*data-chunk last-chunk` (RFC 9112 §7.1). *)
Definition chunk_spec : Spec ascii unit chunked_nt (list ascii) :=
  Bind hex_natural_spec (fun n : nat =>
    if n =? 0 then
      Map (fun _ : unit => nil) crlf
    else
      Map (fun p : unit * (list ascii * unit) => fst (snd p))
          (Seq crlf (Seq (Exactly n octet_spec) crlf))).

(* A non-final chunk: size CRLF data CRLF, producing the data. *)
Definition data_chunk_spec : Spec ascii unit chunked_nt (list ascii) :=
  Bind hex_natural_spec (fun n : nat =>
    if n =? 0 then Fail
    else Map (fun p : unit * (list ascii * unit) => fst (snd p))
             (Seq crlf (Seq (Exactly n octet_spec) crlf))).

(* The final chunk: 0 CRLF, producing nil. *)
Definition last_chunk_spec : Spec ascii unit chunked_nt (list ascii) :=
  Bind hex_natural_spec (fun n : nat =>
    if n =? 0 then Map (fun _ : unit => nil) crlf
    else Fail).

(* chunked-body := *chunk last-chunk CRLF ; the decoded content is the
   concatenated data-chunk payloads (the last chunk contributes nothing). *)
Definition chunked_body_spec : Spec ascii unit chunked_nt (list ascii) :=
  Map (fun p : list ascii * unit => fst p)
      (Seq (Map (fun p : list (list ascii) * list ascii => List.concat (fst p))
                (Seq (Many data_chunk_spec) last_chunk_spec)) crlf).

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

(* The framing theorem: a chunk's payload is exactly its hex-declared size. *)
Lemma parse_chunk_sound (prefix w : list ascii) (data rest : list ascii) :
  parse_chunk w = Some (data, rest) ->
  denote empty_grammar (prefix ++ w) chunk_spec tt (List.length prefix) data tt (List.length prefix + List.length w - List.length rest).
Proof.
  intros H. unfold parse_chunk in H.
  destruct (parse_hex_size w) as [[n rest0] |] eqn:Ehex; [| discriminate].
  destruct rest0 as [| c1 rest1]; [discriminate |].
  destruct (Ascii.eqb c1 "013"%char) eqn:Ecr; [| discriminate].
  apply Ascii.eqb_eq in Ecr. subst c1.
  destruct rest1 as [| c2 rest2]; [discriminate |].
  destruct (Ascii.eqb c2 "010"%char) eqn:Enl; [| discriminate].
  apply Ascii.eqb_eq in Enl. subst c2.
  destruct (n =? 0) eqn:En0.
  - (* zero chunk *)
    injection H as Hd Hr. subst data rest.
    apply (Nat.eqb_eq n 0) in En0. subst n.
    destruct (parse_hex_size_prefix w 0 ("013"%char :: "010"%char :: rest2) Ehex) as [ds Eprefix].
    unfold chunk_spec. eapply d_bind.
    + apply (parse_hex_size_sound prefix w 0 ("013"%char :: "010"%char :: rest2) Ehex).
    + simpl. apply d_map with (a := tt).
      replace (prefix ++ w) with ((prefix ++ ds) ++ "013"%char :: "010"%char :: rest2) by (rewrite <- Eprefix; rewrite !app_assoc; reflexivity).
      replace (List.length prefix + List.length w - S (S (List.length rest2)))
        with (List.length (prefix ++ ds)) by (rewrite <- Eprefix; rewrite !app_length; simpl; lia).
      replace (List.length prefix + List.length w - List.length rest2)
        with (S (S (List.length (prefix ++ ds)))) by (rewrite <- Eprefix; rewrite !app_length; simpl; lia).
      apply crlf_sound.
  - (* data chunk *)
    destruct (parse_exactly n rest2) as [[payload rest3] |] eqn:Eex; [| discriminate].
    destruct rest3 as [| c3 rest4]; [discriminate |].
    destruct (Ascii.eqb c3 "013"%char) eqn:Ecr3; [| discriminate].
    apply Ascii.eqb_eq in Ecr3. subst c3.
    destruct rest4 as [| c4 rest5]; [discriminate |].
    destruct (Ascii.eqb c4 "010"%char) eqn:Enl4; [| discriminate].
    apply Ascii.eqb_eq in Enl4. subst c4.
    injection H as Hd Hr. subst data rest.
    destruct (parse_hex_size_prefix w n ("013"%char :: "010"%char :: rest2) Ehex) as [ds Eprefix].
    pose proof (parse_exactly_prefix n rest2 payload ("013"%char :: "010"%char :: rest5) Eex) as Eex_prefix.
    unfold chunk_spec. eapply d_bind.
    + apply (parse_hex_size_sound prefix w n ("013"%char :: "010"%char :: rest2) Ehex).
    + rewrite En0. simpl. apply d_map with (a := (tt, (payload, tt))). eapply d_seq.
      * replace (prefix ++ w) with ((prefix ++ ds) ++ "013"%char :: "010"%char :: rest2) by (rewrite <- Eprefix; rewrite !app_assoc; reflexivity).
        replace (List.length prefix + List.length w - S (S (List.length rest2)))
          with (List.length (prefix ++ ds)) by (rewrite <- Eprefix; rewrite !app_length; simpl; lia).
        apply crlf_sound.
      * eapply d_seq.
        -- replace (prefix ++ w) with ((prefix ++ ds ++ "013"%char :: "010"%char :: []) ++ rest2)
             by (rewrite <- Eprefix; rewrite !app_assoc; rewrite <- (app_assoc (prefix ++ ds) ("013"%char :: "010"%char :: []) rest2); simpl; reflexivity).
           replace (S (S (List.length (prefix ++ ds)))) with (List.length (prefix ++ ds ++ "013"%char :: "010"%char :: []))
             by (rewrite !app_length; simpl; lia).
           apply (parse_exactly_sound n (prefix ++ ds ++ "013"%char :: "010"%char :: []) rest2 payload ("013"%char :: "010"%char :: rest5) Eex).
        -- replace (prefix ++ w) with ((prefix ++ ds ++ "013"%char :: "010"%char :: [] ++ payload) ++ "013"%char :: "010"%char :: rest5)
             by (rewrite <- Eprefix; rewrite <- Eex_prefix; rewrite !app_assoc; simpl; rewrite <- (app_assoc (prefix ++ ds) ("013"%char :: "010"%char :: payload) ("013"%char :: "010"%char :: rest5)); simpl; reflexivity).
           replace (List.length (prefix ++ ds ++ "013"%char :: "010"%char :: []) + List.length rest2 - List.length ("013"%char :: "010"%char :: rest5))
             with (List.length (prefix ++ ds ++ "013"%char :: "010"%char :: [] ++ payload)) by (rewrite <- Eex_prefix; rewrite !app_length; simpl; lia).
           replace (List.length prefix + List.length w - List.length rest5)
             with (S (S (List.length (prefix ++ ds ++ "013"%char :: "010"%char :: [] ++ payload)))) by (rewrite <- Eprefix; rewrite <- Eex_prefix; rewrite !app_length; simpl; rewrite !app_length; simpl; lia).
           apply crlf_sound.
Qed.

(* A unified chunk denotation refines to a data-chunk (non-empty payload) or a
   last-chunk (empty payload), depending on its payload. *)
Lemma denote_chunk_to_data (prefix w : list ascii) (d : list ascii) (j : nat) :
  denote empty_grammar (prefix ++ w) chunk_spec tt (List.length prefix) d tt j ->
  d <> [] ->
  denote empty_grammar (prefix ++ w) data_chunk_spec tt (List.length prefix) d tt j.
Proof.
  intros Hd Hnz. unfold chunk_spec, data_chunk_spec in *.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar (prefix ++ w) nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Map (fun _ : unit => nil) crlf
        else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt (List.length prefix) j d) Hd) as Hb.
  destruct Hb as [γ' [k [n [Hn Hbody]]]]. destruct γ'.
  destruct (n =? 0) eqn:En0.
  - pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar (prefix ++ w) unit (list ascii)
        (fun _ : unit => nil) crlf tt tt k j d) Hbody) as Hm.
    destruct Hm as [a [Ed Hcrlf]]. simpl in Ed. subst d. exfalso. apply Hnz. reflexivity.
  - eapply d_bind. exact Hn. simpl. rewrite En0. exact Hbody.
Qed.

Lemma denote_chunk_to_last (prefix w : list ascii) (j : nat) :
  denote empty_grammar (prefix ++ w) chunk_spec tt (List.length prefix) [] tt j ->
  denote empty_grammar (prefix ++ w) last_chunk_spec tt (List.length prefix) [] tt j.
Proof.
  intros Hd. unfold chunk_spec, last_chunk_spec in *.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar (prefix ++ w) nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Map (fun _ : unit => nil) crlf
        else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt (List.length prefix) j []) Hd) as Hb.
  destruct Hb as [γ' [k [n [Hn Hbody]]]]. destruct γ'.
  destruct (n =? 0) eqn:En0.
  - eapply d_bind. exact Hn. simpl. rewrite En0. exact Hbody.
  - exfalso.
    pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar (prefix ++ w)
        (unit * (list ascii * unit)) (list ascii) (fun p : unit * (list ascii * unit) => fst (snd p))
        (Seq crlf (Seq (Exactly n octet_spec) crlf)) tt tt k j []) Hbody) as Hm.
    destruct Hm as [a [Ed Hseq]]. simpl in Ed.
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ w) unit (list ascii * unit)
        crlf (Seq (Exactly n octet_spec) crlf) tt tt k j a) Hseq) as Hs.
    destruct Hs as [γ1 [j1 [u [ab [[Ea Hcrlf1] Hseq2]]]]]. destruct γ1. subst a.
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ w) (list ascii) unit
        (Exactly n octet_spec) crlf tt tt j1 j ab) Hseq2) as Hs2.
    destruct Hs2 as [γ2 [j2 [payload [u2 [[Eab Hex] Hcrlf2]]]]]. destruct γ2. subst ab.
    pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar (prefix ++ w) ascii n octet_spec
        tt tt j1 j2 payload) Hex) as He.
    destruct He as [[[[En2 Ed2] Eg2] Ej2] | [n' [a' [as' [γ'' [k2 [[[En3 Ed3] Hoct] Hrest]]]]]]].
    + apply (proj1 (Nat.eqb_neq n 0) En0). exact En2.
    + subst payload. simpl in Ed. inversion Ed.
Qed.

(* A chunk consumes a prefix. *)
Lemma parse_chunk_prefix (w : list ascii) (data rest : list ascii) :
  parse_chunk w = Some (data, rest) -> { consumed : list ascii & consumed ++ rest = w }.
Proof.
  intros H. unfold parse_chunk in H.
  destruct (parse_hex_size w) as [[n rest0] |] eqn:Ehex; [| discriminate].
  destruct rest0 as [| c1 rest1]; [discriminate |].
  destruct (Ascii.eqb c1 "013"%char) eqn:Ecr; [| discriminate].
  apply Ascii.eqb_eq in Ecr. subst c1.
  destruct rest1 as [| c2 rest2]; [discriminate |].
  destruct (Ascii.eqb c2 "010"%char) eqn:Enl; [| discriminate].
  apply Ascii.eqb_eq in Enl. subst c2.
  destruct (n =? 0) eqn:En0.
  - injection H as Hd Hr. subst data rest.
    destruct (parse_hex_size_prefix w n ("013"%char :: "010"%char :: rest2) Ehex) as [ds Eprefix].
    exists (ds ++ "013"%char :: "010"%char :: []). rewrite <- Eprefix.
    rewrite <- (app_assoc ds ("013"%char :: "010"%char :: []) rest2). simpl. reflexivity.
  - destruct (parse_exactly n rest2) as [[payload rest3] |] eqn:Eex; [| discriminate].
    destruct rest3 as [| c3 rest4]; [discriminate |].
    destruct (Ascii.eqb c3 "013"%char) eqn:Ecr3; [| discriminate].
    apply Ascii.eqb_eq in Ecr3. subst c3.
    destruct rest4 as [| c4 rest5]; [discriminate |].
    destruct (Ascii.eqb c4 "010"%char) eqn:Enl4; [| discriminate].
    apply Ascii.eqb_eq in Enl4. subst c4.
    injection H as Hd Hr. subst data rest.
    destruct (parse_hex_size_prefix w n ("013"%char :: "010"%char :: rest2) Ehex) as [ds Eprefix].
    pose proof (parse_exactly_prefix n rest2 payload ("013"%char :: "010"%char :: rest5) Eex) as Eex_prefix.
    exists (ds ++ "013"%char :: "010"%char :: payload ++ "013"%char :: "010"%char :: []).
    rewrite <- Eprefix. rewrite <- Eex_prefix.
    rewrite <- (app_assoc ds ("013"%char :: "010"%char :: payload ++ "013"%char :: "010"%char :: []) rest5).
    simpl.
    rewrite <- (app_assoc payload ("013"%char :: "010"%char :: []) rest5).
    simpl. reflexivity.
Qed.

(* The chunked-body loop is `*data-chunk last-chunk`: non-final chunks then the
   terminating zero chunk. *)
Lemma parse_body_sound (fuel : nat) (prefix w : list ascii) (data rest : list ascii) :
  parse_body fuel w = Some (data, rest) ->
  { init : list (list ascii) &
    prod (data = List.concat init)
         (denote empty_grammar (prefix ++ w) (Seq (Many data_chunk_spec) last_chunk_spec)
             tt (List.length prefix) (init, []) tt (List.length prefix + List.length w - List.length rest)) }.
Proof.
  revert prefix w data rest. induction fuel as [| fuel' IH]; intros prefix w data rest H.
  - cbn in H. discriminate.
  - cbn in H. destruct (parse_chunk w) as [[payload rest0] |] eqn:Echunk; [| discriminate].
    destruct payload as [| p payload'].
    + injection H as Hd Hr. subst data rest.
      exists []. split.
      * reflexivity.
      * eapply d_seq. apply d_many_nil.
        exact (denote_chunk_to_last prefix w (List.length prefix + List.length w - List.length rest0)
                 (parse_chunk_sound prefix w [] rest0 Echunk)).
    + destruct (parse_body fuel' rest0) as [[rest_data rest''] |] eqn:Ebody; [| discriminate].
      injection H as Hd Hr. subst data rest.
      destruct (parse_chunk_prefix w (p :: payload') rest0 Echunk) as [consumed Econsumed].
      destruct (IH (prefix ++ consumed) rest0 rest_data rest'' Ebody) as [init' [Econcat Hbody']].
      exists ((p :: payload') :: init'). split.
      * simpl. rewrite Econcat. reflexivity.
      * replace ((prefix ++ consumed) ++ rest0) with (prefix ++ w) in Hbody'
          by (rewrite <- Econsumed; rewrite !app_assoc; reflexivity).
        pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ w)
            (list (list ascii)) (list ascii) (Many data_chunk_spec) last_chunk_spec
            tt tt (List.length (prefix ++ consumed))
            (List.length (prefix ++ consumed) + List.length rest0 - List.length rest'')
            (init', [])) Hbody') as Hs.
        destruct Hs as [γb [kb [init'' [last [[Ep Hmany] Hlast]]]]].
        injection Ep as Einit Elast. symmetry in Einit. symmetry in Elast. subst init'' last.
        assert (Hnz : (p :: payload') <> []) by (intro Hc; inversion Hc).
        pose proof (parse_chunk_sound prefix w (p :: payload') rest0 Echunk) as Hchunk.
        replace (List.length prefix + List.length w - List.length rest0) with (List.length (prefix ++ consumed)) in Hchunk
          by (rewrite <- Econsumed; rewrite !app_length; simpl; lia).
        pose proof (denote_chunk_to_data prefix w (p :: payload') (List.length (prefix ++ consumed)) Hchunk Hnz) as Hdata.
        replace (List.length (prefix ++ consumed) + List.length rest0 - List.length rest'')
          with (List.length prefix + List.length w - List.length rest'') in Hlast
          by (rewrite <- Econsumed; rewrite !app_length; simpl; lia).
        eapply d_seq. eapply d_many_cons. exact Hdata. exact Hmany. exact Hlast.
Qed.

(* The body consumes a prefix. *)
Lemma parse_body_prefix (fuel : nat) (w : list ascii) (data rest : list ascii) :
  parse_body fuel w = Some (data, rest) -> { consumed : list ascii & consumed ++ rest = w }.
Proof.
  revert w data rest. induction fuel as [| fuel' IH]; intros w data rest H.
  - cbn in H. discriminate.
  - cbn in H. destruct (parse_chunk w) as [[payload rest0] |] eqn:Echunk; [| discriminate].
    destruct payload as [| p payload'].
    + injection H as Hd Hr. subst data rest.
      destruct (parse_chunk_prefix w [] rest0 Echunk) as [consumed Econsumed].
      exists consumed. exact Econsumed.
    + destruct (parse_body fuel' rest0) as [[rest_data rest''] |] eqn:Ebody; [| discriminate].
      injection H as Hd Hr. subst data rest.
      destruct (parse_chunk_prefix w (p :: payload') rest0 Echunk) as [consumed Econsumed].
      destruct (IH rest0 rest_data rest'' Ebody) as [consumed' Econsumed'].
      exists (consumed ++ consumed'). rewrite <- Econsumed. rewrite <- Econsumed'. rewrite !app_assoc. reflexivity.
Qed.

(* Top-level: parse_chunked_body is a chunked_body_spec denotation. *)
Lemma parse_chunked_body_sound (w : list ascii) (data : list ascii) :
  parse_chunked_body w = Some data ->
  denote empty_grammar w (chunked_body_spec) tt 0 data tt (List.length w).
Proof.
  intros H. unfold parse_chunked_body in H.
  destruct (parse_body (3 * List.length w + 2) w) as [[data0 rest] |] eqn:Ebody; [| discriminate].
  destruct rest as [| c1 rest1]; [discriminate |].
  destruct rest1 as [| c2 rest2]; [discriminate |].
  destruct rest2 as [| c3 rest3]; [| discriminate].
  destruct (Ascii.eqb c1 "013"%char) eqn:Ecr; [| discriminate].
  destruct (Ascii.eqb c2 "010"%char) eqn:Enl; [| discriminate].
  apply Ascii.eqb_eq in Ecr. subst c1.
  apply Ascii.eqb_eq in Enl. subst c2.
  injection H as Hd. subst data.
  destruct (parse_body_sound (3 * List.length w + 2) [] w data0 ("013"%char :: "010"%char :: []) Ebody) as [init [Econcat Hbody]].
  destruct (parse_body_prefix (3 * List.length w + 2) w data0 ("013"%char :: "010"%char :: []) Ebody) as [consumed Econsumed].
  unfold chunked_body_spec. apply d_map with (a := (data0, tt)). rewrite Econcat. eapply d_seq.
  - apply d_map with (a := (init, [])). exact Hbody.
  - replace w with (consumed ++ "013"%char :: "010"%char :: []) by (rewrite <- Econsumed; reflexivity).
    replace (List.length [] + List.length (consumed ++ "013"%char :: "010"%char :: []) - List.length ("013"%char :: "010"%char :: []))
      with (List.length consumed) by (rewrite !app_length; simpl; lia).
    replace (List.length (consumed ++ "013"%char :: "010"%char :: []))
      with (S (S (List.length consumed))) by (rewrite !app_length; simpl; lia).
    apply (crlf_sound consumed []).
Qed.


(* ------------------------------------------------------------------------- *)
(* 7. Completeness: every denotation is accepted by the parser               *)
(* ------------------------------------------------------------------------- *)

(* A denotation never moves the cursor backwards. *)
Lemma denote_ge (w : list ascii) (A : Type) (s : Spec ascii unit chunked_nt A)
  (γ γ' : unit) (i j : nat) (a : A) :
  denote empty_grammar w s γ i a γ' j -> i <= j.
Proof.
  intros d. induction d; simpl; lia.
Qed.

(* hex digits: the `Many` loop maps to `parse_hex_rest` on the fully-consumed
   input (no trailing `rest` — `Many` is non-deterministic, the parser greedy). *)
Lemma parse_hex_rest_complete (prefix consumed : list ascii) (ds : list ascii) :
  denote empty_grammar (prefix ++ consumed) (Many hex_digit_spec)
    tt (List.length prefix) ds tt (List.length (prefix ++ consumed)) ->
  parse_hex_rest consumed = Some (ds, []).
Proof.
  revert prefix consumed. induction ds as [| d ds' IH]; intros prefix consumed Hd.
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar
        (prefix ++ consumed) ascii hex_digit_spec tt tt
        (List.length prefix) (List.length (prefix ++ consumed)) []) Hd) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as' [γ'' [k [[Eas2 Ed2] Hrest2]]]]]]; [| inversion Eas2].
    rewrite (app_length prefix consumed) in Ej.
    assert (Hc : List.length consumed = 0) by lia.
    apply (proj1 (length_zero_iff_nil consumed)) in Hc. subst consumed. reflexivity.
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar
        (prefix ++ consumed) ascii hex_digit_spec tt tt
        (List.length prefix) (List.length (prefix ++ consumed)) (d :: ds')) Hd) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as' [γ'' [k [[Eas2 Ed] Hrest]]]]]]; [inversion Eas |].
    injection Eas2 as Eh Et. subst a as'.
    unfold hex_digit_spec in Ed.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar
        (prefix ++ consumed) (fun c0 : ascii => is_hex_digitb c0 = true)
        d tt γ'' (List.length prefix) k) Ed) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] Hhex]. subst γ''. subst k.
    destruct consumed as [| c consumed'].
    + rewrite (app_nil_r prefix) in Hrest.
      exfalso. pose proof (denote_ge prefix (list ascii)
          (Many hex_digit_spec) tt tt (S (List.length prefix)) (List.length prefix) ds' Hrest) as Hge.
      lia.
    + simpl in Hnth.
      pose proof (nth_error_app_cons c prefix consumed') as Hnth'.
      erewrite Hnth' in Hnth. injection Hnth as Hc. subst c.
      replace (S (List.length prefix)) with (List.length (prefix ++ [d])) in Hrest
        by (rewrite app_length; simpl; lia).
      replace (prefix ++ d :: consumed') with ((prefix ++ [d]) ++ consumed') in Hrest
        by (rewrite <- app_assoc; reflexivity).
      replace (List.length (prefix ++ d :: consumed')) with (List.length ((prefix ++ [d]) ++ consumed')) in Hrest
        by (rewrite !app_length; simpl; lia).
      specialize (IH (prefix ++ [d]) consumed' Hrest).
      simpl. rewrite Hhex. rewrite IH. reflexivity.
Qed.

(* Greedy extension: if `consumed` is all hex digits and `rest` starts with a
   non-hex digit (or is empty), the parser on `consumed ++ rest` stops exactly
   at `rest`. *)
Lemma parse_hex_rest_app_nonhex (consumed rest : list ascii) (ds : list ascii) :
  parse_hex_rest consumed = Some (ds, []) ->
  (forall c r', rest = c :: r' -> is_hex_digitb c = false) ->
  parse_hex_rest (consumed ++ rest) = Some (ds, rest).
Proof.
  revert rest ds. induction consumed as [| c consumed' IH]; intros rest ds H Hnonhex.
  - cbn in H. inversion H.
    destruct rest as [| c r']; [reflexivity |].
    assert (Hc : is_hex_digitb c = false) by (apply (Hnonhex c r'); reflexivity).
    simpl. rewrite Hc. reflexivity.
  - cbn in H. destruct (is_hex_digitb c) eqn:Ec.
    + destruct (parse_hex_rest consumed') as [[ds' r''] |] eqn:Erec; [| discriminate].
      inversion H. subst r''. symmetry in H1. subst ds.
      specialize (IH rest ds' eq_refl Hnonhex).
      simpl. rewrite Ec. rewrite IH. reflexivity.
    + inversion H.
Qed.

(* chunk-size: one hex digit then more hex digits. *)
Lemma parse_hex_size_complete (prefix consumed : list ascii) (n : nat) :
  denote empty_grammar (prefix ++ consumed) hex_natural_spec
    tt (List.length prefix) n tt (List.length (prefix ++ consumed)) ->
  parse_hex_size consumed = Some (n, []).
Proof.
  intros Hd. unfold hex_natural_spec in Hd.
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar
      (prefix ++ consumed) (ascii * list ascii) nat
      (fun p : ascii * list ascii => hex_digits_to_nat (fst p :: snd p))
      (Seq hex_digit_spec (Many hex_digit_spec)) tt tt
      (List.length prefix) (List.length (prefix ++ consumed)) n) Hd) as Hm.
  destruct Hm as [p [En Hseq]].
  pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar
      (prefix ++ consumed) ascii (list ascii) hex_digit_spec (Many hex_digit_spec)
      tt tt (List.length prefix) (List.length (prefix ++ consumed)) p) Hseq) as Hs.
  destruct Hs as [γ' [j [a1 [a2 [[Ep Ehex] Hmany]]]]].
  destruct γ'. subst p.
  simpl in En.
  unfold hex_digit_spec in Ehex.
  pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar
      (prefix ++ consumed) (fun c0 : ascii => is_hex_digitb c0 = true)
      a1 tt tt (List.length prefix) j) Ehex) as Htok.
  destruct Htok as [[[Eg2 Ej2] Hnth] Hhex]. subst j.
  destruct consumed as [| c consumed'].
  - simpl in Hnth. rewrite (app_nil_r prefix) in Hmany. exfalso.
    pose proof (denote_ge prefix (list ascii)
        (Many hex_digit_spec) tt tt (S (List.length prefix)) (List.length prefix) a2 Hmany) as Hge.
    lia.
  - simpl in Hnth.
    pose proof (nth_error_app_cons c prefix consumed') as Hnth'.
    erewrite Hnth' in Hnth. injection Hnth as Hc. subst c.
    replace (S (List.length prefix)) with (List.length (prefix ++ [a1])) in Hmany
      by (rewrite app_length; simpl; lia).
    replace (prefix ++ a1 :: consumed') with ((prefix ++ [a1]) ++ consumed') in Hmany
      by (rewrite <- app_assoc; reflexivity).
    replace (List.length (prefix ++ a1 :: consumed')) with (List.length ((prefix ++ [a1]) ++ consumed')) in Hmany
      by (rewrite !app_length; simpl; lia).
    pose proof (parse_hex_rest_complete (prefix ++ [a1]) consumed' a2 Hmany) as Erest.
    unfold parse_hex_size. simpl. rewrite Hhex. rewrite Erest.
    subst n. reflexivity.
Qed.

Lemma parse_hex_size_app_nonhex (consumed rest : list ascii) (n : nat) :
  parse_hex_size consumed = Some (n, []) ->
  (forall c r', rest = c :: r' -> is_hex_digitb c = false) ->
  parse_hex_size (consumed ++ rest) = Some (n, rest).
Proof.
  unfold parse_hex_size. intros H Hnonhex.
  destruct consumed as [| c consumed']; [cbn in H; inversion H |].
  cbn in H. destruct (is_hex_digitb c) eqn:Ec; [| inversion H].
  destruct (parse_hex_rest consumed') as [[ds r''] |] eqn:Erec; [| inversion H].
  injection H as Hn Hr. subst n r''.
  cbn. rewrite Ec.
  pose proof (parse_hex_rest_app_nonhex consumed' rest ds Erec Hnonhex) as Erest.
  rewrite Erest. reflexivity.
Qed.

(* Exactly n octets: the parser returns exactly the consumed input. *)
Lemma parse_exactly_complete (n : nat) (prefix consumed rest : list ascii) (data : list ascii) :
  denote empty_grammar (prefix ++ consumed ++ rest) (Exactly n octet_spec)
    tt (List.length prefix) data tt (List.length (prefix ++ consumed)) ->
  parse_exactly n (consumed ++ rest) = Some (data, rest).
Proof.
  revert prefix consumed rest data. induction n as [| n' IH]; intros prefix consumed rest data Hd.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar
        (prefix ++ consumed ++ rest) ascii 0 octet_spec tt tt
        (List.length prefix) (List.length (prefix ++ consumed)) data) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as' [γ'' [k [[[En2 Ed2] Hoct] Hrest]]]]]]]; [| exfalso; lia].
    subst data. rewrite (app_length prefix consumed) in Ej.
    assert (Hc : List.length consumed = 0) by lia.
    apply (proj1 (length_zero_iff_nil consumed)) in Hc. subst consumed.
    reflexivity.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar
        (prefix ++ consumed ++ rest) ascii (S n') octet_spec tt tt
        (List.length prefix) (List.length (prefix ++ consumed)) data) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as' [γ'' [k [[[En Ed] Hoct] Hrest]]]]]]]; [exfalso; lia |].
    subst data. injection En as En'. subst n''.
    unfold octet_spec in Hoct.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar
        (prefix ++ consumed ++ rest) (fun _ : ascii => True)
        a tt γ'' (List.length prefix) k) Hoct) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] _]. subst γ''. subst k.
    destruct consumed as [| c consumed'].
    + rewrite (app_nil_r prefix) in Hrest.
      exfalso. pose proof (denote_ge (prefix ++ rest) (list ascii)
          (Exactly n' octet_spec) tt tt (S (List.length prefix)) (List.length prefix) as' Hrest) as Hge.
      lia.
    + simpl in Hnth.
      pose proof (nth_error_app_cons c prefix (consumed' ++ rest)) as Hnth'.
      erewrite Hnth' in Hnth. injection Hnth as Hc. subst c.
      replace (S (List.length prefix)) with (List.length (prefix ++ [a])) in Hrest
        by (rewrite app_length; simpl; lia).
      replace (prefix ++ (a :: consumed') ++ rest) with ((prefix ++ [a]) ++ consumed' ++ rest) in Hrest
        by (rewrite <- app_assoc; reflexivity).
      replace (List.length (prefix ++ a :: consumed')) with (List.length ((prefix ++ [a]) ++ consumed')) in Hrest
        by (rewrite !app_length; simpl; lia).
      specialize (IH (prefix ++ [a]) consumed' rest as' Hrest).
      unfold parse_exactly in *. simpl.
      destruct (n' <=? List.length (consumed' ++ rest)) eqn:He'.
      * injection IH as Efirstn Eskipn.
        simpl. rewrite Efirstn. rewrite Eskipn. reflexivity.
      * inversion IH.

Qed.

(* The refined chunk specs are sub-derivations of the unified `chunk_spec`. *)
Lemma denote_data_to_chunk (prefix w : list ascii) (d : list ascii) (j : nat) :
  denote empty_grammar (prefix ++ w) data_chunk_spec tt (List.length prefix) d tt j ->
  denote empty_grammar (prefix ++ w) chunk_spec tt (List.length prefix) d tt j.
Proof.
  intros Hd. unfold data_chunk_spec, chunk_spec in *.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar (prefix ++ w) nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Fail
        else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt (List.length prefix) j d) Hd) as Hb.
  destruct Hb as [γ' [k [n [Hn Hbody]]]]. destruct γ'.
  destruct (n =? 0) eqn:En0.
  - exfalso. exact (denote_fail_elim ascii unit chunked_nt empty_grammar (prefix ++ w) (list ascii) tt k d tt j Hbody).
  - eapply d_bind. exact Hn. simpl. rewrite En0. exact Hbody.
Qed.

Lemma denote_last_to_chunk (prefix w : list ascii) (j : nat) :
  denote empty_grammar (prefix ++ w) last_chunk_spec tt (List.length prefix) [] tt j ->
  denote empty_grammar (prefix ++ w) chunk_spec tt (List.length prefix) [] tt j.
Proof.
  intros Hd. unfold last_chunk_spec, chunk_spec in *.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar (prefix ++ w) nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Map (fun _ : unit => nil) crlf else Fail)
      tt tt (List.length prefix) j []) Hd) as Hb.
  destruct Hb as [γ' [k [n [Hn Hbody]]]]. destruct γ'.
  destruct (n =? 0) eqn:En0.
  - eapply d_bind. exact Hn. simpl. rewrite En0. exact Hbody.
  - exfalso. exact (denote_fail_elim ascii unit chunked_nt empty_grammar (prefix ++ w) (list ascii) tt k [] tt j Hbody).
Qed.

(* Extract the consumed hex digits and the remaining suffix from a `Many` hex
   derivation.  The bound `j <= length (prefix ++ consumed)` ensures the `Many`
   does not run past `consumed` into `rest`. *)
Lemma many_hex_prefix (prefix consumed rest : list ascii) (ds : list ascii) (j : nat) :
  denote empty_grammar (prefix ++ consumed ++ rest) (Many hex_digit_spec) tt (List.length prefix) ds tt j ->
  j <= List.length (prefix ++ consumed) ->
  { rest' : list ascii & prod (consumed = ds ++ rest') (parse_hex_rest ds = Some (ds, [])) }.
Proof.
  revert prefix consumed rest j. induction ds as [| d ds' IH]; intros prefix consumed rest j Hd Hj.
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        ascii hex_digit_spec tt tt (List.length prefix) j []) Hd) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as' [γ'' [k [[Eas2 Ed2] Hrest2]]]]]]; [| inversion Eas2].
    exists consumed. split; reflexivity.
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        ascii hex_digit_spec tt tt (List.length prefix) j (d :: ds')) Hd) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as' [γ'' [k [[Eas2 Ed] Hrest]]]]]]; [inversion Eas |].
    injection Eas2 as Eh Et. subst a as'.
    unfold hex_digit_spec in Ed.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        (fun c0 : ascii => is_hex_digitb c0 = true) d tt γ'' (List.length prefix) k) Ed) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] Hhex]. subst γ''. subst k.
    destruct consumed as [| c consumed'].
    + rewrite (app_nil_r prefix) in Hj. exfalso.
      pose proof (denote_ge (prefix ++ rest) (list ascii) (Many hex_digit_spec) tt tt (S (List.length prefix)) j ds' Hrest) as Hge.
      lia.
    + simpl in Hnth. pose proof (nth_error_app_cons c prefix (consumed' ++ rest)) as Hnth'.
      erewrite Hnth' in Hnth. injection Hnth as Hc. subst c.
      replace (S (List.length prefix)) with (List.length (prefix ++ [d])) in Hrest by (rewrite app_length; simpl; lia).
      replace (prefix ++ (d :: consumed') ++ rest) with ((prefix ++ [d]) ++ consumed' ++ rest) in Hrest by (rewrite <- app_assoc; reflexivity).
      replace (List.length (prefix ++ d :: consumed')) with (List.length ((prefix ++ [d]) ++ consumed')) in Hj by (rewrite !app_length; simpl; lia).
      destruct (IH (prefix ++ [d]) consumed' rest j Hrest Hj) as [rest' [Econsumed Erest]].
      exists rest'. split.
      * simpl. rewrite Econsumed. reflexivity.
      * simpl. rewrite Hhex. rewrite Erest. reflexivity.
Qed.

(* A CRLF derivation consumes exactly "\r\n". *)
Lemma crlf_prefix (prefix consumed rest : list ascii) (j : nat) :
  denote empty_grammar (prefix ++ consumed ++ rest) crlf tt (List.length prefix) tt tt j ->
  j <= List.length (prefix ++ consumed) ->
  { rest' : list ascii & prod (consumed = "013"%char :: "010"%char :: rest') (j = List.length prefix + 2) }.
Proof.
  intros Hd Hj. unfold crlf in Hd.
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
      (unit * unit) unit (fun _ : unit * unit => tt) (Seq (char "013"%char) (char "010"%char))
      tt tt (List.length prefix) j tt) Hd) as Hm.
  destruct Hm as [a [Ett Hseq]].
  pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
      unit unit (char "013"%char) (char "010"%char) tt tt (List.length prefix) j a) Hseq) as Hs.
  destruct Hs as [γ' [j' [u1 [u2 [[Ea Hc1] Hc2]]]]]. destruct γ'. subst a.
  unfold char in Hc1, Hc2.
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
      ascii unit (fun _ : ascii => tt) (Tok (fun c' : ascii => c' = "013"%char))
      tt tt (List.length prefix) j' u1) Hc1) as Hm1.
  destruct Hm1 as [t1 [Eu1 Ht1]]. subst u1.
  pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
      (fun c' : ascii => c' = "013"%char) t1 tt tt (List.length prefix) j') Ht1) as Htok1.
  destruct Htok1 as [[[Eg1 Ej1] Hnth1] Pt1]. subst j'. subst t1.
  destruct consumed as [| c1 consumed1]; [simpl in Hnth1; rewrite (app_nil_r prefix) in Hj; exfalso;
      pose proof (denote_ge (prefix ++ rest) unit (char "010"%char) tt tt (S (List.length prefix)) j u2 Hc2) as Hge; lia |].
  simpl in Hnth1. pose proof (nth_error_app_cons c1 prefix (consumed1 ++ rest)) as Hnth1'.
  erewrite Hnth1' in Hnth1. injection Hnth1 as Hc1'. subst c1.
  replace (S (List.length prefix)) with (List.length (prefix ++ ["013"%char])) in Hc2 by (rewrite app_length; simpl; lia).
  replace (prefix ++ ("013"%char :: consumed1) ++ rest) with ((prefix ++ ["013"%char]) ++ consumed1 ++ rest) in Hc2 by (rewrite <- app_assoc; reflexivity).
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar ((prefix ++ ["013"%char]) ++ consumed1 ++ rest)
      ascii unit (fun _ : ascii => tt) (Tok (fun c' : ascii => c' = "010"%char))
      tt tt (List.length (prefix ++ ["013"%char])) j u2) Hc2) as Hm2.
  destruct Hm2 as [t2 [Eu2 Ht2]]. subst u2.
  pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar ((prefix ++ ["013"%char]) ++ consumed1 ++ rest)
      (fun c' : ascii => c' = "010"%char) t2 tt tt (List.length (prefix ++ ["013"%char])) j) Ht2) as Htok2.
  destruct Htok2 as [[[Eg2 Ej2] Hnth2] Pt2]. subst t2.
  destruct consumed1 as [| c2 consumed2]; [simpl in Hnth2; exfalso;
      rewrite Ej2 in Hj; rewrite !app_length in Hj; simpl in Hj; lia |].
  simpl in Hnth2. pose proof (nth_error_app_cons c2 (prefix ++ ["013"%char]) (consumed2 ++ rest)) as Hnth2'.
  erewrite Hnth2' in Hnth2. injection Hnth2 as Hc2'. subst c2.
  exists consumed2. split; [reflexivity | rewrite Ej2; rewrite app_length; simpl; lia].
Qed.

(* The hex `Many` advances exactly one per digit. *)
Lemma denote_many_length (w : list ascii) (γ γ' : unit) (i j : nat) (as_ : list ascii) :
  denote empty_grammar w (Many hex_digit_spec) γ i as_ γ' j -> j = i + List.length as_.
Proof.
  revert γ γ' i j. induction as_ as [| a as' IH]; intros γ γ' i j d.
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar w ascii hex_digit_spec γ γ' i j []) d) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a0 [as0 [γ0 [k [[Eas2 Ed] Hrest]]]]]]; [subst; simpl; lia | inversion Eas2].
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar w ascii hex_digit_spec γ γ' i j (a :: as')) d) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a0 [as0 [γ0 [k [[Eas2 Ed] Hrest]]]]]]; [inversion Eas |].
    injection Eas2 as Eh Et. subst a0 as0.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar w (fun c0 : ascii => is_hex_digitb c0 = true) a γ γ0 i k) Ed) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] Hhex]. subst γ0. subst k.
    simpl. rewrite (IH γ γ' (S i) j Hrest). lia.
Qed.

(* parse_hex_size on a full input whose hex digits are a1 :: a2 and whose
   suffix starts with a non-hex digit. *)
Lemma parse_hex_size_with_suffix (a1 : ascii) (a2 suffix : list ascii) :
  is_hex_digitb a1 = true -> parse_hex_rest a2 = Some (a2, []) ->
  (forall c r', suffix = c :: r' -> is_hex_digitb c = false) ->
  parse_hex_size (a1 :: a2 ++ suffix) = Some (hex_digits_to_nat (a1 :: a2), suffix).
Proof.
  intros Hhex1 Erest Hnonhex.
  pose proof (parse_hex_rest_app_nonhex a2 suffix a2 Erest Hnonhex) as Erest'.
  unfold parse_hex_size. simpl. rewrite Hhex1. rewrite Erest'. reflexivity.
Qed.


(* The Exactly-n octets are the first n chars of the consumed input. *)
Lemma exactly_firstn (prefix consumed rest : list ascii) (n : nat) (data : list ascii) :
  denote empty_grammar (prefix ++ consumed ++ rest) (Exactly n octet_spec)
    tt (List.length prefix) data tt (List.length (prefix ++ consumed)) ->
  data = List.firstn n consumed.
Proof.
  revert prefix consumed rest data. induction n as [| n' IH]; intros prefix consumed rest data Hd.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        ascii 0 octet_spec tt tt (List.length prefix) (List.length (prefix ++ consumed)) data) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as' [γ'' [k [[[En2 Ed2] Hoct] Hrest]]]]]]]; [| exfalso; lia].
    subst data. simpl. reflexivity.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        ascii (S n') octet_spec tt tt (List.length prefix) (List.length (prefix ++ consumed)) data) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as' [γ'' [k [[[En Ed] Hoct] Hrest]]]]]]]; [exfalso; lia |].
    subst data. injection En as En'. subst n''.
    unfold octet_spec in Hoct.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        (fun _ : ascii => True) a tt γ'' (List.length prefix) k) Hoct) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] _]. subst γ''. subst k.
    destruct consumed as [| c consumed']; [simpl in Hnth; rewrite (app_nil_r prefix) in Hrest; exfalso;
        pose proof (denote_ge (prefix ++ rest) (list ascii) (Exactly n' octet_spec) tt tt (S (List.length prefix)) (List.length prefix) as' Hrest) as Hge; lia |].
    simpl in Hnth. pose proof (nth_error_app_cons c prefix (consumed' ++ rest)) as Hnth'.
    erewrite Hnth' in Hnth. injection Hnth as Hc. subst c.
    replace (S (List.length prefix)) with (List.length (prefix ++ [a])) in Hrest by (rewrite app_length; simpl; lia).
    replace (prefix ++ (a :: consumed') ++ rest) with ((prefix ++ [a]) ++ consumed' ++ rest) in Hrest by (rewrite <- app_assoc; reflexivity).
    replace (List.length (prefix ++ (a :: consumed'))) with (List.length ((prefix ++ [a]) ++ consumed')) in Hrest
      by (rewrite !app_length; simpl; lia).
    specialize (IH (prefix ++ [a]) consumed' rest as' Hrest).
    simpl. rewrite IH. reflexivity.
Qed.
(* The Exactly-n octets are the first n chars of the consumed suffix, even when
   the denotation's end is only the payload (not the whole suffix). *)
Lemma exactly_firstn_rest (prefix rest1 rest : list ascii) (n : nat) (data : list ascii) :
  denote empty_grammar (prefix ++ rest1 ++ rest) (Exactly n octet_spec)
    tt (List.length prefix) data tt (List.length (prefix ++ data)) ->
  List.length data <= List.length rest1 ->
  data = List.firstn n rest1.
Proof.
  revert prefix rest1 rest data. induction n as [| n' IH]; intros prefix rest1 rest data Hd Hj.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar (prefix ++ rest1 ++ rest)
        ascii 0 octet_spec tt tt (List.length prefix) (List.length (prefix ++ data)) data) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as' [γ'' [k [[[En2 Ed2] Hoct] Hrest]]]]]]]; [| exfalso; lia].
    subst data. simpl. reflexivity.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar (prefix ++ rest1 ++ rest)
        ascii (S n') octet_spec tt tt (List.length prefix) (List.length (prefix ++ data)) data) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as' [γ'' [k [[[En Ed] Hoct] Hrest]]]]]]]; [exfalso; lia |].
    subst data. injection En as En'. subst n''.
    unfold octet_spec in Hoct.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar (prefix ++ rest1 ++ rest)
        (fun _ : ascii => True) a tt γ'' (List.length prefix) k) Hoct) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] _]. subst γ''. subst k.
    destruct rest1 as [| c rest1']; [simpl in Hnth; simpl in Hj; exfalso; lia |].
    simpl in Hnth. pose proof (nth_error_app_cons c prefix (rest1' ++ rest)) as Hnth'.
    erewrite Hnth' in Hnth. injection Hnth as Hc. subst c.
    replace (S (List.length prefix)) with (List.length (prefix ++ [a])) in Hrest by (rewrite app_length; simpl; lia).
    replace (prefix ++ (a :: rest1') ++ rest) with ((prefix ++ [a]) ++ rest1' ++ rest) in Hrest by (rewrite <- app_assoc; reflexivity).
    replace (List.length (prefix ++ (a :: as'))) with (List.length ((prefix ++ [a]) ++ as')) in Hrest
      by (rewrite !app_length; simpl; lia).
    assert (Hj' : List.length as' <= List.length rest1') by (simpl in Hj; apply le_S_n in Hj; exact Hj).
    specialize (IH (prefix ++ [a]) rest1' rest as' Hrest Hj').
    cbn [List.firstn]. rewrite IH. reflexivity.
Qed.

(* The Exactly-n parser advances exactly n positions. *)
Lemma denote_exactly_length (w : list ascii) (γ γ' : unit) (i j n : nat) (as_ : list ascii) :
  denote empty_grammar w (Exactly n octet_spec) γ i as_ γ' j -> j = i + n.
Proof.
  revert γ γ' i j as_. induction n as [| n' IH]; intros γ γ' i j as_ Hd.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar w ascii 0 octet_spec γ γ' i j as_) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as'' [γ'' [k [[[En2 Ed2] Hoct] Hrest]]]]]]]; [subst; rewrite Nat.add_0_r; reflexivity | exfalso; lia].
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar w ascii (S n') octet_spec γ γ' i j as_) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as'' [γ'' [k [[[En Ed2] Hoct] Hrest]]]]]]]; [exfalso; lia |].
    injection En as En'. subst n''.
    unfold octet_spec in Hoct.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar w (fun _ : ascii => True) a γ γ'' i k) Hoct) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] _]. subst γ''. subst k.
    specialize (IH γ γ' (S i) j as'' Hrest). rewrite IH. simpl. rewrite Nat.add_succ_r. reflexivity.
Qed.


(* The Exactly-n parser produces exactly n octets. *)
Lemma denote_exactly_len (w : list ascii) (γ γ' : unit) (i j n : nat) (as_ : list ascii) :
  denote empty_grammar w (Exactly n octet_spec) γ i as_ γ' j -> List.length as_ = n.
Proof.
  revert γ γ' i j as_. induction n as [| n' IH]; intros γ γ' i j as_ Hd.
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar w ascii 0 octet_spec γ γ' i j as_) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as'' [γ'' [k [[[En2 Ed2] Hoct] Hrest]]]]]]]; [subst; reflexivity | exfalso; lia].
  - pose proof (fst (denote_exactly_iff ascii unit chunked_nt empty_grammar w ascii (S n') octet_spec γ γ' i j as_) Hd) as He.
    destruct He as [[[[En Ed] Eg] Ej] | [n'' [a [as'' [γ'' [k [[[En Ed2] Hoct] Hrest]]]]]]]; [exfalso; lia |].
    injection En as En'. subst n''.
    unfold octet_spec in Hoct.
    pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar w (fun _ : ascii => True) a γ γ'' i k) Hoct) as Htok.
    destruct Htok as [[[Eg2 Ek] Hnth] _]. subst γ''. subst k.
    specialize (IH γ γ' (S i) j as'' Hrest). subst as_. simpl. rewrite IH. reflexivity.
Qed.


(* A chunk denotation is accepted by parse_chunk. *)
Lemma parse_chunk_complete (prefix consumed rest : list ascii) (data : list ascii) :
  denote empty_grammar (prefix ++ consumed ++ rest) chunk_spec
    tt (List.length prefix) data tt (List.length (prefix ++ consumed)) ->
  parse_chunk (consumed ++ rest) = Some (data, rest).
Proof.
  intros Hd. unfold chunk_spec in Hd.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest) nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Map (fun _ : unit => nil) crlf
        else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt (List.length prefix) (List.length (prefix ++ consumed)) data) Hd) as Hb.
  destruct Hb as [γ1 [j1 [n [Hn Hbody]]]]. destruct γ1.
  unfold hex_natural_spec in Hn.
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
      (ascii * list ascii) nat (fun p : ascii * list ascii => hex_digits_to_nat (fst p :: snd p))
      (Seq hex_digit_spec (Many hex_digit_spec)) tt tt (List.length prefix) j1 n) Hn) as Hm.
  destruct Hm as [p [En Hseq]].
  pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
      ascii (list ascii) hex_digit_spec (Many hex_digit_spec) tt tt (List.length prefix) j1 p) Hseq) as Hs.
  destruct Hs as [γ2 [j2 [a1 [a2 [[Ep Ehex] Hmany]]]]]. destruct γ2. subst p. simpl in En.
  unfold hex_digit_spec in Ehex.
  pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
      (fun c0 : ascii => is_hex_digitb c0 = true) a1 tt tt (List.length prefix) j2) Ehex) as Htok.
  destruct Htok as [[[Eg3 Ej3] Hnth] Hhex1]. subst j2.
  pose proof (denote_ge (prefix ++ consumed ++ rest) (list ascii)
      (if n =? 0 then Map (fun _ : unit => nil) crlf
       else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt j1 (List.length (prefix ++ consumed)) data Hbody) as Hj1.
  destruct consumed as [| c consumed']; [simpl in Hnth; rewrite (app_nil_r prefix) in Hj1; exfalso;
      pose proof (denote_ge (prefix ++ rest) (list ascii) (Many hex_digit_spec) tt tt (S (List.length prefix)) j1 a2 Hmany) as Hge; lia |].
  simpl in Hnth. pose proof (nth_error_app_cons c prefix (consumed' ++ rest)) as Hnth'.
  erewrite Hnth' in Hnth. injection Hnth as Hc. subst c.
  replace (S (List.length prefix)) with (List.length (prefix ++ [a1])) in Hmany by (rewrite app_length; simpl; lia).
  replace (prefix ++ (a1 :: consumed') ++ rest) with ((prefix ++ [a1]) ++ consumed' ++ rest) in Hmany by (rewrite <- app_assoc; reflexivity).
  replace (List.length (prefix ++ a1 :: consumed')) with (List.length ((prefix ++ [a1]) ++ consumed')) in Hj1
    by (rewrite !app_length; simpl; lia).
  destruct (many_hex_prefix (prefix ++ [a1]) consumed' rest a2 j1 Hmany Hj1) as [chunk_rest [Econsumed Erest]].
  pose proof (denote_many_length ((prefix ++ [a1]) ++ consumed' ++ rest) tt tt (List.length (prefix ++ [a1])) j1 a2 Hmany) as Ej1.
  subst n.
  assert (Econsumed_full : (a1 :: consumed') = (a1 :: a2) ++ chunk_rest) by (simpl; rewrite Econsumed; reflexivity).
  destruct (hex_digits_to_nat (a1 :: a2) =? 0) eqn:En0.
  - (* zero chunk *)
    pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar (prefix ++ (a1 :: consumed') ++ rest)
        unit (list ascii) (fun _ : unit => nil) crlf tt tt j1 (List.length (prefix ++ (a1 :: consumed'))) data) Hbody) as Hmz.
    destruct Hmz as [uz [Ed Hcrlf]]. destruct uz. simpl in Ed. subst data.
    replace (prefix ++ (a1 :: consumed') ++ rest) with ((prefix ++ (a1 :: a2)) ++ chunk_rest ++ rest) in Hcrlf by (rewrite Econsumed_full; rewrite !app_assoc; reflexivity).
    replace j1 with (List.length (prefix ++ (a1 :: a2))) in Hcrlf by (rewrite Ej1; rewrite !app_length; simpl; lia).
    destruct (crlf_prefix (prefix ++ (a1 :: a2)) chunk_rest rest (List.length (prefix ++ (a1 :: consumed'))) Hcrlf) as [rest'' [Ecrlf Ejc]].
    { rewrite Econsumed. rewrite !app_length. simpl. rewrite !app_length. lia. }
    subst chunk_rest.
    assert (Hnonhex : forall c r', ("013"%char :: "010"%char :: rest'') ++ rest = c :: r' -> is_hex_digitb c = false).
    { intros c0 r' Hr. injection Hr as Hc0 Hr'. subst c0 r'. reflexivity. }
    pose proof (parse_hex_rest_app_nonhex a2 (("013"%char :: "010"%char :: rest'') ++ rest) a2 Erest Hnonhex) as Erest'.
    unfold parse_chunk. rewrite Econsumed_full. unfold parse_hex_size. simpl. rewrite Hhex1. simpl. rewrite <- app_assoc. rewrite Erest'. simpl. rewrite En0.
    assert (Hlen : List.length rest'' = 0).
    { rewrite Econsumed_full in Ejc. rewrite !app_length in Ejc. simpl in Ejc. lia. }
    apply (proj1 (length_zero_iff_nil rest'')) in Hlen. subst rest''. reflexivity.
  - (* data chunk *)
    pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar (prefix ++ (a1 :: consumed') ++ rest)
        (unit * (list ascii * unit)) (list ascii) (fun p : unit * (list ascii * unit) => fst (snd p))
        (Seq crlf (Seq (Exactly (hex_digits_to_nat (a1 :: a2)) octet_spec) crlf))
        tt tt j1 (List.length (prefix ++ (a1 :: consumed'))) data) Hbody) as Hmd.
    destruct Hmd as [pz [Ed Hseqz]].
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ (a1 :: consumed') ++ rest)
        unit (list ascii * unit) crlf (Seq (Exactly (hex_digits_to_nat (a1 :: a2)) octet_spec) crlf)
        tt tt j1 (List.length (prefix ++ (a1 :: consumed'))) pz) Hseqz) as Hsz.
    destruct Hsz as [γ3 [j3 [uz [abz [[Epz Hcrlf1] Hseq2]]]]]. destruct γ3. destruct uz. subst pz.
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ (a1 :: consumed') ++ rest)
        (list ascii) unit (Exactly (hex_digits_to_nat (a1 :: a2)) octet_spec) crlf
        tt tt j3 (List.length (prefix ++ (a1 :: consumed'))) abz) Hseq2) as Hsz2.
    destruct Hsz2 as [γ4 [j4 [payload [uz2 [[Epz2 Hex] Hcrlf2]]]]]. destruct γ4. destruct uz2. subst abz.
    simpl in Ed. subst data.
    replace (prefix ++ (a1 :: consumed') ++ rest) with ((prefix ++ (a1 :: a2)) ++ chunk_rest ++ rest) in Hcrlf1 by (rewrite Econsumed_full; rewrite !app_assoc; reflexivity).
    replace j1 with (List.length (prefix ++ (a1 :: a2))) in Hcrlf1 by (rewrite Ej1; rewrite !app_length; simpl; lia).
    destruct (crlf_prefix (prefix ++ (a1 :: a2)) chunk_rest rest j3 Hcrlf1) as [rest1 [Ecrlf1 Ejc1]].
    { pose proof (denote_ge (prefix ++ (a1 :: consumed') ++ rest) (list ascii * unit)
          (Seq (Exactly (hex_digits_to_nat (a1 :: a2)) octet_spec) crlf) tt tt j3
          (List.length (prefix ++ (a1 :: consumed'))) (payload, tt) Hseq2) as Hge.
      rewrite Econsumed_full in Hge. rewrite !app_length in *. simpl in *. lia. }
    subst chunk_rest.
    replace (prefix ++ (a1 :: consumed') ++ rest) with (((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) ++ rest1 ++ rest) in Hex
      by (rewrite Econsumed_full; rewrite <- !app_assoc; simpl; reflexivity).
    pose proof (denote_exactly_length (((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) ++ rest1 ++ rest) tt tt j3 j4 (hex_digits_to_nat (a1 :: a2)) payload Hex) as E4.
    pose proof (denote_exactly_len (((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) ++ rest1 ++ rest) tt tt j3 j4 (hex_digits_to_nat (a1 :: a2)) payload Hex) as E4'.
    replace j3 with (List.length ((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: [])) in Hex
      by (rewrite Ejc1; rewrite !app_length; simpl; lia).
    replace j4 with (List.length (((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) ++ payload)) in Hex
      by (rewrite E4; rewrite <- E4'; rewrite Ejc1; rewrite !app_length; simpl; lia).
    pose proof (denote_ge (prefix ++ (a1 :: consumed') ++ rest) unit crlf tt tt j4 (List.length (prefix ++ (a1 :: consumed'))) tt Hcrlf2) as Hge4.
    pose proof (exactly_firstn_rest ((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) rest1 rest
        (hex_digits_to_nat (a1 :: a2)) payload Hex) as Efirstn.
    assert (Hlen_payload : List.length payload <= List.length rest1)
      by (rewrite E4 in Hge4; rewrite <- E4' in Hge4; rewrite Econsumed_full in Hge4; rewrite !app_length in Hge4;
          simpl in Hge4; rewrite Ejc1 in Hge4; rewrite !app_length in Hge4; simpl in Hge4; lia).
    specialize (Efirstn Hlen_payload).
    assert (Hrest1 : rest1 = payload ++ skipn (hex_digits_to_nat (a1 :: a2)) rest1)
      by (symmetry in Efirstn; apply (f_equal (fun x : list ascii => x ++ skipn (hex_digits_to_nat (a1 :: a2)) rest1)) in Efirstn;
          rewrite (firstn_skipn (hex_digits_to_nat (a1 :: a2)) rest1) in Efirstn; exact Efirstn).
    rewrite Hrest1 in Econsumed_full.
    replace (prefix ++ (a1 :: consumed') ++ rest)
      with (((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: [] ++ payload)
             ++ skipn (hex_digits_to_nat (a1 :: a2)) rest1 ++ rest) in Hcrlf2
      by (rewrite Econsumed_full; rewrite <- !app_assoc; simpl; rewrite <- !app_assoc; reflexivity).
    replace j4 with (List.length ((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: [] ++ payload)) in Hcrlf2
      by (rewrite E4; rewrite <- E4'; rewrite Ejc1; rewrite !app_length; simpl; lia).
    destruct (crlf_prefix ((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: [] ++ payload)
        (skipn (hex_digits_to_nat (a1 :: a2)) rest1) rest (List.length (prefix ++ (a1 :: consumed'))) Hcrlf2) as [rest3 [Ecrlf2 Ejc2]].
    { assert (Hw : ((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: [] ++ payload) ++ skipn (hex_digits_to_nat (a1 :: a2)) rest1 = prefix ++ (a1 :: consumed'))
        by (rewrite Econsumed_full; rewrite app_assoc; simpl; rewrite <- app_assoc; reflexivity).
      rewrite Hw. apply Nat.le_refl. }
    assert (Hlen : List.length rest3 = 0).
    { rewrite Econsumed_full in Ejc2; rewrite Ecrlf2 in Ejc2.
      rewrite !app_length in Ejc2; simpl in Ejc2; rewrite !app_length in Ejc2; simpl in Ejc2; lia. }
    apply (proj1 (length_zero_iff_nil rest3)) in Hlen. subst rest3.
    (* rest1 = payload ++ "\r\n" ; parse_exactly n (payload ++ "\r\n" ++ rest) = Some (payload, "\r\n" ++ rest) *)
    replace (((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) ++ rest1 ++ rest)
      with (((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) ++ payload ++ "013"%char :: "010"%char :: rest) in Hex
      by (rewrite Hrest1; rewrite Ecrlf2; rewrite <- !app_assoc; simpl; reflexivity).
    pose proof (parse_exactly_complete (hex_digits_to_nat (a1 :: a2))
        ((prefix ++ (a1 :: a2)) ++ "013"%char :: "010"%char :: []) payload ("013"%char :: "010"%char :: rest) payload Hex) as Eex.
    assert (Hnonhex : forall c r', ("013"%char :: "010"%char :: payload ++ "013"%char :: "010"%char :: rest) = c :: r' -> is_hex_digitb c = false).
    { intros c0 r' Hr. injection Hr as Hc0 Hr'. subst c0 r'. reflexivity. }
    pose proof (parse_hex_rest_app_nonhex a2 ("013"%char :: "010"%char :: payload ++ "013"%char :: "010"%char :: rest) a2 Erest Hnonhex) as Erest'.
    unfold parse_chunk. rewrite Econsumed_full. unfold parse_hex_size. simpl. rewrite Hhex1. simpl. rewrite <- app_assoc. rewrite Ecrlf2. simpl. rewrite <- app_assoc. simpl. rewrite Erest'. simpl. rewrite En0. rewrite Eex. simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 8. Completeness of the body and the top-level parser                      *)
(* ------------------------------------------------------------------------- *)

(* The last chunk always produces nil. *)
Lemma last_chunk_payload_nil (w : list ascii) (i j : nat) (d : list ascii) :
  denote empty_grammar w last_chunk_spec tt i d tt j -> d = [].
Proof.
  intros Hd. unfold last_chunk_spec in Hd.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar w nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Map (fun _ : unit => nil) crlf else Fail)
      tt tt i j d) Hd) as Hb.
  destruct Hb as [γ' [k [n [Hn Hbody]]]]. destruct γ'.
  destruct (n =? 0) eqn:En0.
  - pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar w unit (list ascii)
        (fun _ : unit => nil) crlf tt tt k j d) Hbody) as Hm.
    destruct Hm as [u [Ed Hcrlf]]. simpl in Ed. exact Ed.
  - exfalso. exact (denote_fail_elim ascii unit chunked_nt empty_grammar w (list ascii) tt k d tt j Hbody).
Qed.

(* A data chunk produces a non-empty payload. *)
Lemma data_chunk_nonnil (w : list ascii) (d : list ascii) (i j : nat) :
  denote empty_grammar w data_chunk_spec tt i d tt j -> d <> [].
Proof.
  intros Hd. unfold data_chunk_spec in Hd.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar w nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Fail
        else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt i j d) Hd) as Hb.
  destruct Hb as [γ' [k [n [Hn Hbody]]]]. destruct γ'.
  destruct (n =? 0) eqn:En0.
  - exfalso. exact (denote_fail_elim ascii unit chunked_nt empty_grammar w (list ascii) tt k d tt j Hbody).
  - pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar w
        (unit * (list ascii * unit)) (list ascii) (fun p : unit * (list ascii * unit) => fst (snd p))
        (Seq crlf (Seq (Exactly n octet_spec) crlf)) tt tt k j d) Hbody) as Hm.
    destruct Hm as [p [Ed Hseq]].
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar w unit (list ascii * unit)
        crlf (Seq (Exactly n octet_spec) crlf) tt tt k j p) Hseq) as Hs.
    destruct Hs as [γ1 [j1 [u [ab [[Ep Hcrlf1] Hseq2]]]]]. destruct γ1. subst p.
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar w (list ascii) unit
        (Exactly n octet_spec) crlf tt tt j1 j ab) Hseq2) as Hs2.
    destruct Hs2 as [γ2 [j2 [payload [u2 [[Eab Hex] Hcrlf2]]]]]. destruct γ2. subst ab.
    simpl in Ed. subst d.
    pose proof (denote_exactly_len w tt tt j1 j2 n payload Hex) as Hlen.
    intro Hnil. rewrite Hnil in Hlen. simpl in Hlen.
    symmetry in Hlen. rewrite Hlen in En0. simpl in En0. discriminate En0.
Qed.

Lemma parse_body_complete (fuel : nat) (prefix consumed rest : list ascii) (init : list (list ascii)) :
  denote empty_grammar (prefix ++ consumed ++ rest) (Seq (Many data_chunk_spec) last_chunk_spec)
    tt (List.length prefix) (init, []) tt (List.length (prefix ++ consumed)) ->
  List.length init < fuel ->
  parse_body fuel (consumed ++ rest) = Some (List.concat init, rest).
Proof.
  revert prefix consumed rest fuel. induction init as [| d init' IH]; intros prefix consumed rest fuel Hd Hfuel.
  - (* last chunk only *)
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        (list (list ascii)) (list ascii) (Many data_chunk_spec) last_chunk_spec
        tt tt (List.length prefix) (List.length (prefix ++ consumed)) ([], [])) Hd) as Hs.
    destruct Hs as [γ' [j [a [b [[Ep Hmany] Hlast]]]]].
    injection Ep as Ea Eb. symmetry in Ea. subst a. symmetry in Eb. subst b.
    pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        (list ascii) data_chunk_spec tt γ' (List.length prefix) j []) Hmany) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as' [γ'' [k [[Eas2 Ed] Hrest]]]]]].
    + subst γ'. subst j.
      pose proof (denote_last_to_chunk prefix (consumed ++ rest) (List.length (prefix ++ consumed)) Hlast) as Hchunk.
      pose proof (parse_chunk_complete prefix consumed rest [] Hchunk) as Echunk.
      destruct fuel as [| fuel'].
      * exfalso. lia.
      * cbn [parse_body]. rewrite Echunk. reflexivity.
    + discriminate Eas2.
  - (* data chunk then the rest *)
    pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        (list (list ascii)) (list ascii) (Many data_chunk_spec) last_chunk_spec
        tt tt (List.length prefix) (List.length (prefix ++ consumed)) (d :: init', [])) Hd) as Hs.
    destruct Hs as [γ' [j [a [b [[Ep Hmany] Hlast]]]]].
    injection Ep as Ea Eb. symmetry in Ea. subst a. symmetry in Eb. subst b.
    pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar (prefix ++ consumed ++ rest)
        (list ascii) data_chunk_spec tt γ' (List.length prefix) j (d :: init')) Hmany) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as' [γ'' [k [[Eas2 Ed] Hrest]]]]]].
    + discriminate Eas.
    + injection Eas2 as Ed0 Eas'. subst a as'.
      destruct γ''.
      pose proof (denote_ge (prefix ++ consumed ++ rest) (list ascii) data_chunk_spec
          tt tt (List.length prefix) k d Ed) as Hge_ed.
      pose proof (denote_ge (prefix ++ consumed ++ rest) (list (list ascii)) (Many data_chunk_spec)
          tt γ' k j init' Hrest) as Hge_rest.
      pose proof (denote_ge (prefix ++ consumed ++ rest) (list ascii) last_chunk_spec
          γ' tt j (List.length (prefix ++ consumed)) [] Hlast) as Hge_last.
      assert (Hk : k <= List.length (prefix ++ consumed)) by lia.
      assert (Hn1le : k - List.length prefix <= List.length consumed)
        by (rewrite app_length in Hk; lia).
      set (c1 := firstn (k - List.length prefix) consumed).
      set (c2 := skipn (k - List.length prefix) consumed).
      assert (Efs : c1 ++ c2 = consumed) by (subst c1 c2; apply firstn_skipn).
      assert (Hlen1 : List.length c1 = k - List.length prefix)
        by (subst c1; apply firstn_length_le; exact Hn1le).
      assert (Ek : k = List.length (prefix ++ c1))
        by (rewrite app_length; rewrite Hlen1; lia).
      pose proof (denote_data_to_chunk prefix (consumed ++ rest) d k Ed) as Hchunk1.
      replace k with (List.length (prefix ++ c1)) in Hchunk1 by (symmetry; exact Ek).
      replace (prefix ++ consumed ++ rest) with (prefix ++ c1 ++ (c2 ++ rest)) in Hchunk1
        by (rewrite <- Efs; rewrite !app_assoc; reflexivity).
      pose proof (parse_chunk_complete prefix c1 (c2 ++ rest) d Hchunk1) as Echunk1.
      assert (Hseq' : denote empty_grammar (prefix ++ consumed ++ rest)
          (Seq (Many data_chunk_spec) last_chunk_spec) tt k (init', []) tt (List.length (prefix ++ consumed))).
      { eapply d_seq. exact Hrest. exact Hlast. }
      replace (prefix ++ consumed ++ rest) with ((prefix ++ c1) ++ c2 ++ rest) in Hseq'
        by (rewrite <- Efs; rewrite !app_assoc; reflexivity).
      replace k with (List.length (prefix ++ c1)) in Hseq' by (symmetry; exact Ek).
      replace (List.length (prefix ++ consumed)) with (List.length ((prefix ++ c1) ++ c2)) in Hseq'
        by (rewrite <- Efs; rewrite app_assoc; reflexivity).
      destruct fuel as [| fuel'].
      * exfalso. lia.
      * assert (Hfuel' : List.length init' < fuel') by (simpl in Hfuel; lia).
        pose proof (IH (prefix ++ c1) c2 rest fuel' Hseq' Hfuel') as Ebody.
        pose proof (data_chunk_nonnil (prefix ++ consumed ++ rest) d (List.length prefix) k Ed) as Hd_nn.
        cbn [parse_body]. rewrite <- Efs. rewrite <- app_assoc. rewrite Echunk1. simpl.
        rewrite Ebody. simpl. destruct d as [| x d'].
        { exfalso. apply Hd_nn. reflexivity. }
        reflexivity.
Qed.

(* A hex natural consumes at least one byte. *)
Lemma hex_natural_consumes_lt (w : list ascii) (i k : nat) (n : nat) :
  denote empty_grammar w hex_natural_spec tt i n tt k -> i < k.
Proof.
  intros Hd. unfold hex_natural_spec in Hd.
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar w
      (ascii * list ascii) nat (fun p : ascii * list ascii => hex_digits_to_nat (fst p :: snd p))
      (Seq hex_digit_spec (Many hex_digit_spec)) tt tt i k n) Hd) as Hm.
  destruct Hm as [p [En Hseq]].
  pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar w
      ascii (list ascii) hex_digit_spec (Many hex_digit_spec) tt tt i k p) Hseq) as Hs.
  destruct Hs as [γ2 [j2 [a1 [a2 [[Ep2 Hhex] Hmany]]]]]. destruct γ2. subst p.
  unfold hex_digit_spec in Hhex.
  pose proof (fst (denote_tok_iff ascii unit chunked_nt empty_grammar w
      (fun c0 : ascii => is_hex_digitb c0 = true) a1 tt tt i j2) Hhex) as Htok.
  destruct Htok as [[[Eg2 Ej2] Hnth] Hhexb]. subst j2.
  pose proof (denote_ge w (list ascii) (Many hex_digit_spec) tt tt (S i) k a2 Hmany) as Hge.
  lia.
Qed.

(* A data chunk consumes at least one byte. *)
Lemma data_chunk_consumes_lt (w : list ascii) (d : list ascii) (i j : nat) :
  denote empty_grammar w data_chunk_spec tt i d tt j -> i < j.
Proof.
  intros Hd. unfold data_chunk_spec in Hd.
  pose proof (fst (denote_bind_iff ascii unit chunked_nt empty_grammar w nat (list ascii)
      hex_natural_spec (fun n : nat => if n =? 0 then Fail
        else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt i j d) Hd) as Hb.
  destruct Hb as [γ' [k [n [Hn Hbody]]]]. destruct γ'.
  pose proof (hex_natural_consumes_lt w i k n Hn) as Hik.
  pose proof (denote_ge w (list ascii)
      (if n =? 0 then Fail
        else Map (fun p : unit * (list ascii * unit) => fst (snd p)) (Seq crlf (Seq (Exactly n octet_spec) crlf)))
      tt tt k j d Hbody) as Hkj.
  lia.
Qed.

(* The number of data chunks is at most the number of bytes they consume. *)
Lemma denote_many_data_le (w : list ascii) (i j : nat) (as_ : list (list ascii)) :
  denote empty_grammar w (Many data_chunk_spec) tt i as_ tt j -> i + List.length as_ <= j.
Proof.
  revert i j. induction as_ as [| d as' IH]; intros i j Hd.
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar w
        (list ascii) data_chunk_spec tt tt i j []) Hd) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as0 [γ0 [k [[Eas2 Ed] Hrest]]]]]]; [subst; simpl; lia | inversion Eas2].
  - pose proof (fst (denote_many_iff ascii unit chunked_nt empty_grammar w
        (list ascii) data_chunk_spec tt tt i j (d :: as')) Hd) as Hm.
    destruct Hm as [[[Eas Eg] Ej] | [a [as0 [γ0 [k [[Eas2 Ed] Hrest]]]]]]; [inversion Eas |].
    injection Eas2 as Eh Et. subst a as0.
    destruct γ0.
    pose proof (denote_ge w (list (list ascii)) (Many data_chunk_spec) tt tt k j as' Hrest) as Hkj.
    pose proof (data_chunk_consumes_lt w d i k Ed) as Hik.
    pose proof (IH k j Hrest) as Hlen.
    simpl. lia.
Qed.

Lemma parse_chunked_body_complete (w : list ascii) (data : list ascii) :
  denote empty_grammar w chunked_body_spec tt 0 data tt (List.length w) ->
  parse_chunked_body w = Some data.
Proof.
  intros Hd. unfold chunked_body_spec in Hd.
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar w
      (list ascii * unit) (list ascii) (fun p : list ascii * unit => fst p)
      (Seq (Map (fun p : list (list ascii) * list ascii => List.concat (fst p))
                (Seq (Many data_chunk_spec) last_chunk_spec)) crlf)
      tt tt 0 (List.length w) data) Hd) as Hm.
  destruct Hm as [p [Ed Hseq]].
  pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar w
      (list ascii) unit
      (Map (fun p : list (list ascii) * list ascii => List.concat (fst p))
           (Seq (Many data_chunk_spec) last_chunk_spec)) crlf
      tt tt 0 (List.length w) p) Hseq) as Hs.
  destruct Hs as [γ' [j [a [u [[Ep Hmap] Hcrlf]]]]]. destruct γ'. destruct u. subst p.
  pose proof (fst (denote_map_iff ascii unit chunked_nt empty_grammar w
      (list (list ascii) * list ascii) (list ascii)
      (fun p : list (list ascii) * list ascii => List.concat (fst p))
      (Seq (Many data_chunk_spec) last_chunk_spec) tt tt 0 j a) Hmap) as Hm2.
  destruct Hm2 as [ab [Econcat Hbody]].
  destruct ab as [init lastv]. simpl in Econcat.
  pose proof (fst (denote_seq_iff ascii unit chunked_nt empty_grammar w
      (list (list ascii)) (list ascii) (Many data_chunk_spec) last_chunk_spec
      tt tt 0 j (init, lastv)) Hbody) as Hs2.
  destruct Hs2 as [γ2 [j2 [a2 [b2 [[Ep2 Hmany] Hlast2]]]]].
  injection Ep2 as Einit Elastv. symmetry in Einit. subst a2. symmetry in Elastv. subst b2.
  destruct γ2.
  assert (Elastv0 : lastv = []) by (exact (last_chunk_payload_nil w j2 j lastv Hlast2)).
  subst lastv.
  simpl in Ed. subst data. subst a.
  (* final CRLF at the tail of w *)
  pose proof (denote_ge w unit crlf tt tt j (List.length w) tt Hcrlf) as Hge_crlf.
  assert (Hlen_firstn : List.length (firstn j w) = j) by (apply firstn_length_le; exact Hge_crlf).
  assert (Hinit_le : List.length init <= List.length w).
  { pose proof (denote_many_data_le w 0 j2 init Hmany) as H1.
    pose proof (denote_ge w (list ascii) last_chunk_spec tt tt j2 j [] Hlast2) as H2.
    lia. }
  assert (Hfuel : List.length init < 3 * List.length w + 2) by lia.
  destruct (crlf_prefix (firstn j w) (skipn j w) [] (List.length w)) as [rest' [Ecrlf_tail Ej_tail]].
  { rewrite app_assoc. rewrite firstn_skipn. rewrite app_nil_r. rewrite Hlen_firstn. exact Hcrlf. }
  { rewrite firstn_skipn. apply Nat.le_refl. }
  assert (Hrest'_nil : rest' = []).
  { assert (Hsk : List.length (skipn j w) = 2)
      by (rewrite length_skipn; rewrite Ej_tail; rewrite Hlen_firstn; lia).
    apply (f_equal (@List.length ascii)) in Ecrlf_tail.
    rewrite Ecrlf_tail in Hsk. simpl in Hsk.
    assert (Hl : List.length rest' = 0) by lia.
    apply (proj1 (length_zero_iff_nil rest')) in Hl. exact Hl. }
  subst rest'.
  set (c1 := firstn j w).
  set (c2 := skipn j w).
  assert (Efirstn : c1 ++ c2 = w) by (subst c1 c2; apply firstn_skipn).
  assert (Hlen_c1 : List.length c1 = j) by (subst c1; apply firstn_length_le; exact Hge_crlf).
  replace j with (List.length c1) in Hbody by (exact Hlen_c1).
  replace w with (c1 ++ c2) in Hbody by (exact Efirstn).
  pose proof (parse_body_complete (3 * List.length w + 2) [] c1 c2 init Hbody Hfuel) as Ebody.
  rewrite Efirstn in Ebody. subst c2. rewrite Ecrlf_tail in Ebody.
  unfold parse_chunked_body. rewrite Ebody. simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 9. Extraction: the decoder compiles to OCaml                              *)
(* ------------------------------------------------------------------------- *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlNatBigInt ExtrOcamlZBigInt ExtrOcamlChar.
(* nat and Z both extract to Big_int_Z.big_int (= Zarith Z.t); of_nat is the
   identity. ascii extracts to char. *)
Extract Constant Z.of_nat => "(fun n -> n)".
Extraction Language OCaml.
Extraction "chunked.ml" parse_chunked_body.

