(* Zero-copy JSON parser: a fast tokenizer over a buffer (extracted to OCaml
   string), producing span-carrying Json_fast values.  A separate `decode`
   materializes the spans into the certified Json, so the fast parser can be
   shown to refine the certified `parse_json` without re-doing the grammar
   soundness/completeness machinery.  Nothing in Json.v / Spec.v is changed. *)

From Stdlib Require Import List Ascii String ZArith Bool Lia.
Import ListNotations.
From Parsebot Require Import Json Spec.

(* ------------------------------------------------------------------------- *)
(* Buffer: in Coq a list wrapper (for proofs); in OCaml a `string` via        *)
(* extraction.  The hot path uses only buffer_length/buffer_get/nth.          *)
(* ------------------------------------------------------------------------- *)

Inductive buffer : Type :=
| Buf : list ascii -> buffer.

Definition buffer_length (b : buffer) : nat :=
  match b with Buf l => List.length l end.

Definition buffer_get (b : buffer) (i : nat) : option ascii :=
  match b with Buf l => List.nth_error l i end.

Definition buffer_nth (b : buffer) (i : nat) : ascii :=
  match b with Buf l => List.nth i l "000"%char end.

Definition buffer_to_list (b : buffer) : list ascii :=
  match b with Buf l => l end.

(* Equality of the char at index i with c, as a bool. *)
Definition buf_eq_char (buf : buffer) (i : nat) (c : ascii) : bool :=
  match buffer_get buf i with Some c' => Ascii.eqb c c' | None => false end.


(* ------------------------------------------------------------------------- *)
(* Json_fast: like Json but strings (and numbers) are spans into the buffer.  *)
(* ------------------------------------------------------------------------- *)

Inductive Json_fast : Type :=
| JNull_f : Json_fast
| JBool_f : bool -> Json_fast
| JNum_f  : nat -> nat -> Json_fast          (* (start, len) span *)
| JStr_f  : nat -> nat -> Json_fast          (* (start, len) span *)
| JArr_f  : list Json_fast -> Json_fast
| JObj_f  : list (nat * nat * Json_fast) -> Json_fast.  (* (key_start, key_len, value) *)


(* ------------------------------------------------------------------------- *)
(* Tokenizer: parse_json_fast records (start,len) spans for strings/numbers.  *)
(* A single fuel (buffer_length buf) is threaded and decremented at every      *)
(* forward step, giving structural recursion.                                 *)
(* ------------------------------------------------------------------------- *)

Fixpoint skip_ws_loop (buf : buffer) (fuel : nat) (i : nat) : nat :=
  match fuel with
  | O => i
  | S fuel' =>
      match buffer_get buf i with
      | Some c => if is_wsb c then skip_ws_loop buf fuel' (S i) else i
      | None => i
      end
  end.

Definition skip_ws_fast (buf : buffer) (i : nat) : nat :=
  skip_ws_loop buf (buffer_length buf) i.

Fixpoint skip_digits_loop (buf : buffer) (fuel : nat) (i : nat) : nat :=
  match fuel with
  | O => i
  | S fuel' =>
      match buffer_get buf i with
      | Some c => if is_digitb c then skip_digits_loop buf fuel' (S i) else i
      | None => i
      end
  end.

Definition skip_digits_fast (buf : buffer) (i : nat) : nat :=
  skip_digits_loop buf (buffer_length buf) i.

(* The non-`\u` escape chars the certified parser accepts. *)
Definition is_escape_char (c : ascii) : bool :=
  Ascii.eqb c "034"%char || Ascii.eqb c "092"%char || Ascii.eqb c "047"%char
  || Ascii.eqb c "b"%char || Ascii.eqb c "f"%char || Ascii.eqb c "n"%char
  || Ascii.eqb c "r"%char || Ascii.eqb c "t"%char.

(* Whether a `\uXXXX` escape (backslash at i) is followed by 4 hex digits. *)
Definition parse_u_escape_fast (buf : buffer) (i : nat) : bool :=
  match buffer_get buf (S (S i)) with
  | Some ha => match buffer_get buf (S (S (S i))) with
    | Some hb => match buffer_get buf (S (S (S (S i)))) with
      | Some hc => match buffer_get buf (S (S (S (S (S i))))) with
        | Some hd => is_hexb ha && is_hexb hb && is_hexb hc && is_hexb hd
        | None => false
        end
      | None => false
      end
    | None => false
    end
  | None => false
  end.

(* Scan a string body from i (just past the opening quote) to the closing quote. *)
Fixpoint find_string_end_loop (buf : buffer) (fuel : nat) (i : nat) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      match buffer_get buf i with
      | None => None
      | Some c =>
          if Ascii.eqb c "034"%char then Some i
          else if Ascii.eqb c "092"%char then
            match buffer_get buf (S i) with
            | None => None
            | Some e =>
                if Ascii.eqb e "u"%char then
                  if parse_u_escape_fast buf i then find_string_end_loop buf fuel' (i + 6) else None
                else if is_escape_char e then find_string_end_loop buf fuel' (i + 2) else None
            end
          else find_string_end_loop buf fuel' (S i)
      end
  end.

Definition find_string_end (buf : buffer) (i : nat) : option nat :=
  find_string_end_loop buf (buffer_length buf) i.

(* Parse a string (opening quote at i) as a span. *)
Definition parse_string_fast (buf : buffer) (i : nat) : option (Json_fast * nat) :=
  match find_string_end buf (S i) with
  | Some endq => Some (JStr_f (S i) (endq - (S i)), S endq)
  | None => None
  end.

(* The exponent scanner (i is at the 'e'): [ exp ] := e [ +/- ] 1*DIGIT.
   Consumed only when it has a digit, else the 'e' is left in place, mirroring
   the certified parse_exp.  Always returns Some. *)
Definition parse_exp_fast (buf : buffer) (i : nat) : option nat :=
  match buffer_get buf i with
  | Some c =>
      if is_expb c then
        let i2 := if (buf_eq_char buf (S i) "+"%char) || (buf_eq_char buf (S i) "-"%char)
                  then S (S i) else S i in
        match buffer_get buf i2 with
        | Some c' => if is_digitb c' then Some (skip_digits_fast buf i2) else Some i
        | None => Some i end
      else Some i
  | None => Some i
  end.

(* After the int part (i is just past it): parse [ frac ] [ exp ].  A frac/exp
   is consumed only when it has a digit; otherwise the '.'/'e' is left in place,
   mirroring the certified parse_frac/parse_exp.  Always returns Some. *)
Definition parse_frac_exp_fast (buf : buffer) (i : nat) : option nat :=
  let i1 : nat := if buf_eq_char buf i "."%char then
              match buffer_get buf (S i) with
              | Some c => if is_digitb c then skip_digits_fast buf (S i) else i
              | None => i end
            else i in
  parse_exp_fast buf i1.

Definition parse_number_fast (buf : buffer) (i : nat) : option (Json_fast * nat) :=
  let i1 := if buf_eq_char buf i "-"%char then S i else i in
  match buffer_get buf i1 with
  | None => None
  | Some d =>
      if Ascii.eqb d "0"%char then
        match parse_frac_exp_fast buf (S i1) with
        | Some i2 => Some (JNum_f i (i2 - i), i2)
        | None => None end
      else if is_digit1_9b d then
        match parse_frac_exp_fast buf (skip_digits_fast buf (S i1)) with
        | Some i2 => Some (JNum_f i (i2 - i), i2)
        | None => None end
      else None
  end.

Fixpoint parse_lit_fast (buf : buffer) (s : string) (i : nat) (v : Json_fast) : option (Json_fast * nat) :=
  match s with
  | EmptyString => Some (v, i)
  | String c rest =>
      if buf_eq_char buf i c then parse_lit_fast buf rest (S i) v else None
  end.

Fixpoint parse_value_fast (buf : buffer) (fuel : nat) (i : nat) : option (Json_fast * nat) :=
  match fuel with
  | O => None
  | S fuel' =>
      let i0 := skip_ws_fast buf i in
      match buffer_get buf i0 with
      | None => None
      | Some c =>
          if Ascii.eqb c "{"%char then parse_object_fast buf fuel' i0
          else if Ascii.eqb c "["%char then parse_array_fast buf fuel' i0
          else if Ascii.eqb c "034"%char then parse_string_fast buf i0
          else if Ascii.eqb c "t"%char then parse_lit_fast buf "rue"%string (S i0) (JBool_f true)
          else if Ascii.eqb c "f"%char then parse_lit_fast buf "alse"%string (S i0) (JBool_f false)
          else if Ascii.eqb c "n"%char then parse_lit_fast buf "ull"%string (S i0) JNull_f
          else if Ascii.eqb c "-"%char || is_digitb c then parse_number_fast buf i0
          else None
      end
  end

with parse_array_fast (buf : buffer) (fuel : nat) (i : nat) : option (Json_fast * nat) :=
  (* i is the opening '[' *)
  match fuel with
  | O => None
  | S fuel' =>
      let i1 := skip_ws_fast buf (S i) in
      if buf_eq_char buf i1 "]"%char then
        match fuel' with O => None | S _ => Some (JArr_f [], S i1) end
      else match parse_array_elems_fast buf fuel' i1 with
           | Some (vs, i2) => Some (JArr_f vs, i2)
           | None => None end
  end

with parse_array_elems_fast (buf : buffer) (fuel : nat) (i : nat) : option (list Json_fast * nat) :=
  (* i is the first element *)
  match fuel with
  | O => None
  | S fuel' =>
      match parse_value_fast buf fuel' i with
      | None => None
      | Some (v, i2) =>
          let i3 := skip_ws_fast buf i2 in
          match buffer_get buf i3 with
          | Some ","%char =>
              match parse_array_elems_fast buf fuel' (S i3) with
              | Some (vs, i4) => Some (v :: vs, i4)
              | None => None end
          | Some "]"%char => Some ([v], S i3)
          | _ => None
          end
      end
  end

with parse_object_fast (buf : buffer) (fuel : nat) (i : nat) : option (Json_fast * nat) :=
  (* i is the opening '{' *)
  match fuel with
  | O => None
  | S fuel' =>
      let i1 := skip_ws_fast buf (S i) in
      if buf_eq_char buf i1 "}"%char then
        match fuel' with O => None | S _ => Some (JObj_f [], S i1) end
      else match parse_object_members_fast buf fuel' i1 with
           | Some (ms, i2) => Some (JObj_f ms, i2)
           | None => None end
  end

with parse_object_members_fast (buf : buffer) (fuel : nat) (i : nat) : option (list (nat * nat * Json_fast) * nat) :=
  (* i is at (or before) the first key (a string) *)
  match fuel with
  | O => None
  | S fuel' =>
      let i0 := skip_ws_fast buf i in
      if buf_eq_char buf i0 "034"%char then
      match parse_string_fast buf i0 with
      | None => None
      | Some (JStr_f ks kl, i2) =>
          let i3 := skip_ws_fast buf i2 in
          if buf_eq_char buf i3 ":"%char then
            match parse_value_fast buf fuel' (S i3) with
            | None => None
            | Some (v, i4) =>
                let i5 := skip_ws_fast buf i4 in
                match buffer_get buf i5 with
                | Some ","%char =>
                    match parse_object_members_fast buf fuel' (S i5) with
                    | Some (ms, i6) => Some ((ks, kl, v) :: ms, i6)
                    | None => None end
                | Some "}"%char => Some ([(ks, kl, v)], S i5)
                | _ => None
                end
            end
          else None
      | _ => None
      end
      else None
  end.

Definition parse_json_fast (buf : buffer) : option Json_fast :=
  match parse_value_fast buf (3 * buffer_length buf + 2) 0 with
  | Some (v, j) => if Nat.eqb (skip_ws_fast buf j) (buffer_length buf) then Some v else None
  | None => None
  end.

(* ------------------------------------------------------------------------- *)
(* decode : Json_fast -> Json.  Materializes spans by re-parsing the raw      *)
(* substring with the certified parser.                                       *)
(* ------------------------------------------------------------------------- *)

Definition span_to_list (buf : buffer) (start len : nat) : list ascii :=
  firstn len (skipn start (buffer_to_list buf)).

Definition decode_string (buf : buffer) (start len : nat) : list ascii :=
  match parse_string ("034"%char :: span_to_list buf start len ++ "034"%char :: nil) with
  | Some (s, _) => s
  | None => []
  end.

Definition decode_number (buf : buffer) (start len : nat) : Z * Z :=
  match parse_number (span_to_list buf start len) with
  | Some ((m, e), _) => (m, e)
  | None => (0%Z, 0%Z)
  end.

Fixpoint decode (buf : buffer) (j : Json_fast) : Json :=
  match j with
  | JNull_f => JNull
  | JBool_f b => JBool b
  | JNum_f start len =>
      let '(m, e) := decode_number buf start len in JNumber m e
  | JStr_f start len => JString (decode_string buf start len)
  | JArr_f vs => JArray (List.map (decode buf) vs)
  | JObj_f ms => JObject (List.map (fun '(ks, kl, v) => (decode_string buf ks kl, decode buf v)) ms)
  end.

(* span_to_list buf start len is exactly the slice buf[start..start+len): its
   k-th character is the buffer character at index (start + k).  This
   characterization is what justifies extracting span_to_list to an O(len)
   substring slice instead of firstn/skipn over the whole buffer. *)
Lemma span_to_list_nth (buf : buffer) (start len k : nat) :
  List.nth_error (span_to_list buf start len) k =
  if k <? len then buffer_get buf (start + k) else None.
Proof.
  destruct buf as [l]. unfold span_to_list, buffer_get.
  rewrite List.nth_error_firstn. rewrite List.nth_error_skipn. reflexivity.
Qed.


(* ------------------------------------------------------------------------- *)
(* Simulation lemmas: the tokenizer on (Buf l) at index i agrees with the     *)
(* certified parser on (skipn i l).                                           *)
(* ------------------------------------------------------------------------- *)

Lemma skip_ws_loop_sim (l : list ascii) (fuel : nat) (i : nat) :
  List.length (skipn i l) <= fuel ->
  skipn (skip_ws_loop (Buf l) fuel i) l = skip_ws (skipn i l).
Proof.
  revert i. induction fuel as [| fuel' IH]; intros i Hfuel.
  - cbn. assert (E : skipn i l = []) by (apply length_zero_iff_nil; lia). rewrite E. cbn. reflexivity.
  - cbn [skip_ws_loop buffer_get buffer_length].
    destruct (nth_error l i) as [c |] eqn:En.
    + destruct (is_wsb c) eqn:Ew.
      * rewrite (skipn_cons_head ascii l i c En). cbn. rewrite Ew.
        rewrite (IH (S i)).
        -- reflexivity.
        -- rewrite (skipn_cons_head ascii l i c En) in Hfuel. simpl in Hfuel. apply Nat.succ_le_mono in Hfuel. exact Hfuel.
      * rewrite (skipn_cons_head ascii l i c En). cbn. rewrite Ew. reflexivity.
    + apply nth_error_None in En. assert (E : skipn i l = []) by (apply skipn_all2; lia). rewrite E. cbn. reflexivity.
Qed.

Lemma skip_digits_loop_sim (l : list ascii) (fuel : nat) (i : nat) :
  List.length (skipn i l) <= fuel ->
  skipn (skip_digits_loop (Buf l) fuel i) l = snd (take_digits (skipn i l)).
Proof.
  revert i. induction fuel as [| fuel' IH]; intros i Hfuel.
  - cbn. assert (E : skipn i l = []) by (apply length_zero_iff_nil; lia). rewrite E. cbn. reflexivity.
  - cbn [skip_digits_loop buffer_get buffer_length].
    destruct (nth_error l i) as [c |] eqn:En.
    + destruct (is_digitb c) eqn:Ew.
      * rewrite (skipn_cons_head ascii l i c En). cbn [take_digits]. rewrite Ew.
        rewrite (IH (S i)).
        -- destruct (take_digits (skipn (S i) l)) as [ds rest'] eqn:Et. cbn [take_digits]. reflexivity.
        -- rewrite (skipn_cons_head ascii l i c En) in Hfuel. simpl in Hfuel. apply Nat.succ_le_mono in Hfuel. exact Hfuel.
      * rewrite (skipn_cons_head ascii l i c En). cbn. rewrite Ew. reflexivity.
    + apply nth_error_None in En. assert (E : skipn i l = []) by (apply skipn_all2; lia). rewrite E. cbn. reflexivity.
Qed.

Lemma parse_lit_fast_sim (l : list ascii) (s : string) (i : nat) (v : Json_fast) :
  match parse_lit_fast (Buf l) s i v with
  | Some (v', j) => v' = v /\ parse_lit s (skipn i l) = Some (skipn j l)
  | None => parse_lit s (skipn i l) = None
  end.
Proof.
  revert i v. induction s as [| c s' IH]; intros i v.
  - cbn. split; [reflexivity | cbn; reflexivity].
  - simpl. unfold buf_eq_char, buffer_get. cbn.
    destruct (nth_error l i) as [c' |] eqn:En.
    + destruct (Ascii.eqb c c') eqn:Eeq.
      * apply (Ascii.eqb_eq c c') in Eeq. subst c'.
        rewrite (skipn_cons_head ascii l i c En). simpl.
        rewrite (Ascii.eqb_refl c). cbn. exact (IH (S i) v).
      * rewrite (skipn_cons_head ascii l i c' En). simpl. rewrite Eeq. reflexivity.
    + apply nth_error_None in En. assert (E : skipn i l = []) by (apply skipn_all2; lia). rewrite E. cbn. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* Extraction: buffer -> OCaml string.                                        *)
(* ------------------------------------------------------------------------- *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlNatInt ExtrOcamlZBigInt ExtrOcamlChar ExtrOcamlString.

Extract Inductive buffer => "string"
  [ "(fun l -> String.of_seq (List.to_seq l))" ]
  "(fun f b -> f (List.of_seq (String.to_seq b)))".

Extract Constant buffer_length => "String.length".
Extract Constant buffer_get => "(fun b i -> if i < String.length b then Some (String.get b i) else None)".
Extract Constant buffer_to_list => "(fun b -> List.of_seq (String.to_seq b))".
Extract Constant span_to_list =>
  "(fun b start len -> List.of_seq (String.to_seq (String.sub b start len)))".

Extraction Language OCaml.
Extraction "json_fast.ml" parse_json_fast decode.



Lemma parse_int_shorter (w rest : list ascii) (intv : Z) :
  parse_int w = Some (intv, rest) -> List.length rest < List.length w.
Proof.
  unfold parse_int. destruct w as [| d w']; cbn.
  - discriminate.
  - destruct (Ascii.eqb d "0"%char) eqn:Ez.
    + injection 1 as _ Hr. rewrite Hr. cbn. lia.
    + destruct (is_digit1_9b d) eqn:E19.
      * destruct (take_digits w') as [ds rest'] eqn:Et.
        injection 1 as _ Hr. apply take_digits_shape in Et. rewrite Et. rewrite Hr. cbn. rewrite List.length_app. lia.
      * discriminate.
Qed.

Lemma parse_frac_shorter (w rest : list ascii) (fv : Z * nat) :
  parse_frac w = Some (fv, rest) -> List.length rest < List.length w.
Proof.
  intros H. unfold parse_frac in *. destruct w as [| c w']; cbn in *.
  - discriminate.
  - destruct (Ascii.eqb c "."%char) eqn:Edot.
    + destruct (take_digits w') as [ds rest'] eqn:Et.
      cbn in H. destruct ds as [| d ds'].
      * discriminate.
      * injection H as _ Hr. apply take_digits_shape in Et. rewrite Et. rewrite Hr. cbn. rewrite List.length_app. lia.
    + discriminate.
Qed.

Lemma parse_exp_shorter (w rest : list ascii) (ev : bool * Z) :
  parse_exp w = Some (ev, rest) -> List.length rest < List.length w.
Proof.
  intros H. unfold parse_exp in *. destruct w as [| c w']; cbn in *.
  - discriminate.
  - destruct (is_expb c) eqn:Ee.
    + destruct w' as [| s w''].
      * discriminate.
      * cbn in H. destruct (Ascii.eqb s "-"%char) eqn:Eneg.
        -- destruct (take_digits w'') as [ds rest'] eqn:Et.
           cbn in H. destruct ds as [| d ds'].
           ++ discriminate.
           ++ injection H as _ Hr. apply take_digits_shape in Et. rewrite Et. rewrite Hr. cbn. rewrite List.length_app. lia.
        -- destruct (Ascii.eqb s "+"%char) eqn:Epos.
           ++ destruct (take_digits w'') as [ds rest'] eqn:Et.
              cbn in H. destruct ds as [| d ds'].
              ** discriminate.
              ** injection H as _ Hr. apply take_digits_shape in Et. rewrite Et. rewrite Hr. cbn. rewrite List.length_app. lia.
           ++ destruct (take_digits (s :: w'')) as [ds rest'] eqn:Et.
              cbn in H. destruct ds as [| d ds'].
              ** discriminate.
              ** injection H as _ Hr. apply take_digits_shape in Et. rewrite Et. rewrite Hr. cbn. rewrite List.length_app. lia.
    + discriminate.
Qed.


(* The certified leaf parsers are prefix-deterministic: running them on a
   prefix that they consumed yields the same value and the matching suffix. *)

Lemma take_digits_prefix (w rest ds w2 : list ascii) :
  take_digits (w ++ rest) = (ds, w2 ++ rest) -> take_digits w = (ds, w2).
Proof.
  revert ds w2 rest. induction w as [| c w' IH]; intros ds w2 rest H.
  - apply (take_digits_shape rest ds (w2 ++ rest)) in H.
    assert (Hnil : ds ++ w2 = []).
    { apply (app_inv_tail rest (ds ++ w2) []). rewrite <- app_assoc.
      symmetry in H. rewrite H. reflexivity. }
    apply app_eq_nil in Hnil as [Hd Hw]. subst ds w2. reflexivity.
  - destruct (is_digitb c) eqn:Ed.
    + simpl in H. rewrite Ed in H.
      destruct (take_digits (w' ++ rest)) as [ds' rest'] eqn:Et.
      simpl in H. injection H as Hds Hrest'. subst ds rest'.
      specialize (IH ds' w2 rest Et). simpl. rewrite Ed. rewrite IH. reflexivity.
    + simpl in H. rewrite Ed in H. injection H as Hds Hw.
      subst ds. apply (app_inv_tail rest (c :: w') w2) in Hw. subst w2.
      simpl. rewrite Ed. reflexivity.
Qed.

Lemma parse_int_prefix (w rest : list ascii) (intv : Z) (w2 : list ascii) :
  parse_int (w ++ rest) = Some (intv, w2 ++ rest) -> parse_int w = Some (intv, w2).
Proof.
  intros H. unfold parse_int in *. destruct w as [| d w']; simpl in *.
  - cbn in *. exfalso. assert (Hlt : List.length (w2 ++ rest) < List.length rest) by (apply (parse_int_shorter rest (w2 ++ rest) intv H)). rewrite List.length_app in Hlt. lia.
  - destruct (Ascii.eqb d "0"%char) eqn:Ez.
    + apply Ascii.eqb_eq in Ez. subst d.
      injection H as Hi Hw'. apply (app_inv_tail rest w' w2) in Hw'. subst w2.
      cbn. rewrite <- Hi. reflexivity.
    + destruct (is_digit1_9b d) eqn:E19.
      * destruct (take_digits (w' ++ rest)) as [ds rest'] eqn:Et.
        cbn in H. injection H as Hi Hrest'. subst rest'.
        apply (take_digits_prefix w' rest ds w2) in Et.
        unfold parse_int; simpl. rewrite Et. rewrite <- Hi. reflexivity.
      * cbn in H. discriminate.
Qed.

Lemma some_pair_inj {A B : Type} (a1 a2 : A) (b1 b2 : B) :
  @Some (A * B) (a1, b1) = @Some (A * B) (a2, b2) -> a1 = a2 /\ b1 = b2.
Proof.
  intro H. split.
  - apply (f_equal (fun x : option (A * B) => match x with Some p => fst p | None => a1 end)) in H. exact H.
  - apply (f_equal (fun x : option (A * B) => match x with Some p => snd p | None => b1 end)) in H. exact H.
Qed.

Lemma none_some_contra {A B : Type} (a : A) (b : B) :
  @None (A * B) = @Some (A * B) (a, b) -> False.
Proof.
  intro H. apply (f_equal (fun x : option (A * B) => match x with None => false | Some _ => true end)) in H. discriminate.
Qed.

Lemma parse_frac_prefix (w rest : list ascii) (fv : Z * nat) (w2 : list ascii) :
  parse_frac (w ++ rest) = Some (fv, w2 ++ rest) -> parse_frac w = Some (fv, w2).
Proof.
  intros H. unfold parse_frac in *. destruct w as [| c w']; simpl in *.
  - cbn in *. exfalso. assert (Hlt : List.length (w2 ++ rest) < List.length rest) by (apply (parse_frac_shorter rest (w2 ++ rest) fv H)). rewrite List.length_app in Hlt. lia.
  - destruct (Ascii.eqb c "."%char) eqn:Edot.
    + destruct (take_digits (w' ++ rest)) as [ds rest'] eqn:Et.
      cbn in H. destruct ds as [| d ds'].
      * exfalso. apply (none_some_contra fv (w2 ++ rest) H).
      * injection H as Hfv Hrest'. subst rest'.
        apply (take_digits_prefix w' rest (d :: ds') w2) in Et.
        unfold parse_frac; simpl. rewrite Et. rewrite <- Hfv. reflexivity.
    + cbn in H. discriminate.
Qed.

Opaque is_digitb.

Lemma parse_exp_prefix (w rest : list ascii) (ev : bool * Z) (w2 : list ascii) :
  parse_exp (w ++ rest) = Some (ev, w2 ++ rest) -> parse_exp w = Some (ev, w2).
Proof.
  intros H. unfold parse_exp in *. destruct w as [| c w']; simpl in *.
  - cbn in *. exfalso. assert (Hlt : List.length (w2 ++ rest) < List.length rest) by (apply (parse_exp_shorter rest (w2 ++ rest) ev H)). rewrite List.length_app in Hlt. lia.
  - destruct (is_expb c) eqn:Ee.
    + destruct w' as [| s w''].
      * cbn in *. destruct rest as [| s' rest'].
        -- rewrite List.app_nil_r in H. exfalso. apply (none_some_contra ev w2 H).
        -- cbn in H. destruct (Ascii.eqb s' "-"%char) eqn:Eneg'.
           ++ destruct (take_digits rest') as [ds rest3] eqn:Et'.
              cbn in H. destruct ds as [| d ds'].
              ** exfalso. apply (none_some_contra ev (w2 ++ s' :: rest') H).
              ** apply some_pair_inj in H as [Hev Hr]. apply take_digits_shape in Et'.
                 rewrite Et' in Hr. apply (f_equal (@List.length ascii)) in Hr. rewrite List.length_app in Hr. simpl in Hr. rewrite List.length_app in Hr. remember (Datatypes.length rest3) as Lr. remember (Datatypes.length w2) as Lw. remember (Datatypes.length ds') as Ld. exfalso. lia.
           ++ destruct (Ascii.eqb s' "+"%char) eqn:Epos'.
              ** destruct (take_digits rest') as [ds rest3] eqn:Et'.
                 cbn in H. destruct ds as [| d ds'].
                 --- exfalso. apply (none_some_contra ev (w2 ++ s' :: rest') H).
                 --- apply some_pair_inj in H as [Hev Hr]. apply take_digits_shape in Et'.
                     rewrite Et' in Hr. apply (f_equal (@List.length ascii)) in Hr. rewrite List.length_app in Hr. simpl in Hr. rewrite List.length_app in Hr. remember (Datatypes.length rest3) as Lr. remember (Datatypes.length w2) as Lw. remember (Datatypes.length ds') as Ld. exfalso. lia.
              ** destruct (take_digits (s' :: rest')) as [ds rest3] eqn:Et'.
                 cbn in H. destruct ds as [| d ds'].
                 --- exfalso. apply (none_some_contra ev (w2 ++ s' :: rest') H).
                 --- apply some_pair_inj in H as [Hev Hr]. apply take_digits_shape in Et'.
                     rewrite Et' in Hr. apply (f_equal (@List.length ascii)) in Hr. rewrite List.length_app in Hr. simpl in Hr. rewrite List.length_app in Hr. remember (Datatypes.length rest3) as Lr. remember (Datatypes.length w2) as Lw. remember (Datatypes.length ds') as Ld. exfalso. lia.
      * cbn in H. destruct (Ascii.eqb s "-"%char) eqn:Eneg.
        -- destruct (take_digits (w'' ++ rest)) as [ds rest'] eqn:Et.
           cbn in H. destruct ds as [| d ds'].
           ++ exfalso. apply (none_some_contra ev (w2 ++ rest) H).
           ++ apply some_pair_inj in H. destruct H as [Hev Hrest']. subst rest'.
              apply (take_digits_prefix w'' rest (d :: ds') w2) in Et.
              unfold parse_exp; simpl. rewrite Et. rewrite <- Hev. reflexivity.
        -- destruct (Ascii.eqb s "+"%char) eqn:Epos.
           ++ destruct (take_digits (w'' ++ rest)) as [ds rest'] eqn:Et.
              cbn in H. destruct ds as [| d ds'].
              ** exfalso. apply (none_some_contra ev (w2 ++ rest) H).
              ** apply some_pair_inj in H. destruct H as [Hev Hrest']. subst rest'.
                 apply (take_digits_prefix w'' rest (d :: ds') w2) in Et.
                 unfold parse_exp; simpl. rewrite Et. rewrite <- Hev. reflexivity.
           ++ cbn in H. destruct (is_digitb s) eqn:Ed.
              ** destruct (take_digits (w'' ++ rest)) as [ds rest'] eqn:Et.
                 cbn in H. destruct ds as [| d ds'].
                 --- apply some_pair_inj in H as [Hev Hrest']. subst rest'.
                     apply (take_digits_prefix w'' rest [] w2) in Et.
                     unfold parse_exp; simpl. rewrite Ed. rewrite Et. rewrite <- Hev. reflexivity.
                 --- apply some_pair_inj in H as [Hev Hrest']. subst rest'.
                     apply (take_digits_prefix w'' rest (d :: ds') w2) in Et.
                     unfold parse_exp; simpl. rewrite Ed. rewrite Et. rewrite <- Hev. reflexivity.
              ** exfalso. apply (none_some_contra ev (w2 ++ rest) H).
    + congruence.
Qed.


(* Re-parsing exactly the prefix parse_number consumed yields the same value
   with empty rest. *)
Lemma parse_number_shorter (w rest : list ascii) (me : Z * Z) :
  parse_number w = Some (me, rest) -> List.length rest < List.length w.
Proof.
  intros H. unfold parse_number in H.
  destruct w as [| c w']; cbn [parse_number] in H; [discriminate |].
  destruct (Ascii.eqb c "-"%char) eqn:Eminus.
  + cbn [parse_number] in H. destruct (parse_int w') as [[intv w2] |] eqn:Eint; [| exfalso; apply (none_some_contra me rest H)].
    destruct (parse_frac w2) as [[[fv flen] w2'] |] eqn:Efrac.
    * destruct (parse_exp w2') as [[[eneg ev] w3] |] eqn:Eexp.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H3 : List.length rest < List.length w2') by apply (parse_exp_shorter w2' rest (eneg, ev) Eexp).
         assert (H2 : List.length w2' < List.length w2) by apply (parse_frac_shorter w2 w2' (fv, flen) Efrac).
         assert (H1 : List.length w2 < List.length w') by apply (parse_int_shorter w' w2 intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H2 : List.length rest < List.length w2) by apply (parse_frac_shorter w2 rest (fv, flen) Efrac).
         assert (H1 : List.length w2 < List.length w') by apply (parse_int_shorter w' w2 intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
    * destruct (parse_exp w2) as [[[eneg ev] w3] |] eqn:Eexp.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H3 : List.length rest < List.length w2) by apply (parse_exp_shorter w2 rest (eneg, ev) Eexp).
         assert (H1 : List.length w2 < List.length w') by apply (parse_int_shorter w' w2 intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H1 : List.length rest < List.length w') by apply (parse_int_shorter w' rest intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
  + cbn [parse_number] in H. destruct (parse_int (c :: w')) as [[intv w2] |] eqn:Eint; [| exfalso; apply (none_some_contra me rest H)].
    destruct (parse_frac w2) as [[[fv flen] w2'] |] eqn:Efrac.
    * destruct (parse_exp w2') as [[[eneg ev] w3] |] eqn:Eexp.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H3 : List.length rest < List.length w2') by apply (parse_exp_shorter w2' rest (eneg, ev) Eexp).
         assert (H2 : List.length w2' < List.length w2) by apply (parse_frac_shorter w2 w2' (fv, flen) Efrac).
         assert (H1 : List.length w2 < List.length (c :: w')) by apply (parse_int_shorter (c :: w') w2 intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H2 : List.length rest < List.length w2) by apply (parse_frac_shorter w2 rest (fv, flen) Efrac).
         assert (H1 : List.length w2 < List.length (c :: w')) by apply (parse_int_shorter (c :: w') w2 intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
    * destruct (parse_exp w2) as [[[eneg ev] w3] |] eqn:Eexp.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H3 : List.length rest < List.length w2) by apply (parse_exp_shorter w2 rest (eneg, ev) Eexp).
         assert (H1 : List.length w2 < List.length (c :: w')) by apply (parse_int_shorter (c :: w') w2 intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
      -- cbn [parse_number] in H. apply some_pair_inj in H as [_ Hr]. rewrite Hr in *.
         assert (H1 : List.length rest < List.length (c :: w')) by apply (parse_int_shorter (c :: w') rest intv Eint).
         cbn. eauto 6 using Nat.lt_trans, Nat.lt_succ_diag_r.
Qed.



Transparent is_digitb.

Lemma parse_frac_none_prefix (w rest : list ascii) :
  parse_frac (w ++ rest) = None -> parse_frac w = None.
Proof.
  unfold parse_frac. intros H. destruct w as [| c w']; cbn in H.
  - reflexivity.
  - destruct (Ascii.eqb c "."%char) eqn:Edot; [| reflexivity].
    destruct (take_digits (w' ++ rest)) as [ds rest'] eqn:Et.
    destruct ds as [| d ds'].
    * pose proof (take_digits_shape (w' ++ rest) [] rest' Et) as Hshape.
      symmetry in Hshape. rewrite (List.app_nil_l rest') in Hshape. rewrite Hshape in Et.
      apply (take_digits_prefix w' rest [] w') in Et.
      cbn. rewrite Et. reflexivity.
    * symmetry in H. exfalso. apply (none_some_contra (digits_to_nat_fast (d :: ds'), List.length (d :: ds')) rest' H).
Qed.

Lemma parse_number_reparse (w rest : list ascii) (me : Z * Z) :
  parse_number (w ++ rest) = Some (me, rest) -> parse_number w = Some (me, []).
Proof.
  intros H. unfold parse_number in *.
  destruct w as [| c w'].
  - cbn in *. exfalso. assert (Hlt : List.length rest < List.length rest) by apply (parse_number_shorter rest rest me H). lia.
  - cbn in *. destruct (Ascii.eqb c "-"%char) eqn:Eminus.
    + destruct (parse_int (w' ++ rest)) as [[intv w2] |] eqn:Eint.
      * destruct (parse_frac w2) as [[[fv flen] w2'] |] eqn:Efrac.
        -- destruct (parse_exp w2') as [[[eneg ev] w3] |] eqn:Eexp.
           ++ (* frac + exp *)
              apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (w' ++ rest) intv w2 Eint) as [pi Hpi].
              destruct (parse_frac_shape w2 (fv, flen) w2' Efrac) as [pf Hpf].
              destruct (parse_exp_shape w2' (eneg, ev) w3 Eexp) as [pe Hpe].
              subst w3.
              assert (Hw2 : w2 = (pf ++ pe) ++ rest) by (rewrite <- Hpf; rewrite <- Hpe; apply app_assoc).
              rewrite Hw2 in *. rewrite <- Hpe in *.
              apply (parse_int_prefix w' rest intv (pf ++ pe)) in Eint.
              apply (parse_frac_prefix (pf ++ pe) rest (fv, flen) pe) in Efrac.
              apply (parse_exp_prefix pe rest (eneg, ev) []) in Eexp.
              cbn [parse_number]. rewrite Eint. rewrite Efrac. rewrite Eexp. reflexivity.
           ++ (* frac, no exp *)
              apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (w' ++ rest) intv w2 Eint) as [pi Hpi].
              destruct (parse_frac_shape w2 (fv, flen) w2' Efrac) as [pf Hpf].
              subst w2'.
              assert (Hw2 : w2 = pf ++ rest) by (rewrite <- Hpf; reflexivity).
              rewrite Hw2 in *.
              apply (parse_int_prefix w' rest intv pf) in Eint.
              apply (parse_frac_prefix pf rest (fv, flen) []) in Efrac.
              cbn [parse_number]. rewrite Eint. rewrite Efrac. reflexivity.
        -- (* no frac *)
          destruct (parse_exp w2) as [[[eneg ev] w3] |] eqn:Eexp.
           ++ apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (w' ++ rest) intv w2 Eint) as [pi Hpi].
              destruct (parse_exp_shape w2 (eneg, ev) w3 Eexp) as [pe Hpe].
              subst w3.
              assert (Hw2 : w2 = pe ++ rest) by (rewrite <- Hpe; reflexivity).
              rewrite Hw2 in *.
              apply (parse_int_prefix w' rest intv pe) in Eint.
              apply (parse_exp_prefix pe rest (eneg, ev) []) in Eexp.
              apply parse_frac_none_prefix in Efrac.
              cbn [parse_number]. rewrite Eint. rewrite Efrac. rewrite Eexp. reflexivity.
           ++ apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (w' ++ rest) intv w2 Eint) as [pi Hpi].
              subst w2.
              apply (parse_int_prefix w' rest intv []) in Eint.
              cbn [parse_number]. rewrite Eint. reflexivity.
      * exfalso. apply (none_some_contra me rest H).
    + destruct (parse_int (c :: w' ++ rest)) as [[intv w2] |] eqn:Eint.
      * destruct (parse_frac w2) as [[[fv flen] w2'] |] eqn:Efrac.
        -- destruct (parse_exp w2') as [[[eneg ev] w3] |] eqn:Eexp.
           ++ apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (c :: w' ++ rest) intv w2 Eint) as [pi Hpi].
              destruct (parse_frac_shape w2 (fv, flen) w2' Efrac) as [pf Hpf].
              destruct (parse_exp_shape w2' (eneg, ev) w3 Eexp) as [pe Hpe].
              subst w3.
              assert (Hw2 : w2 = (pf ++ pe) ++ rest) by (rewrite <- Hpf; rewrite <- Hpe; apply app_assoc).
              rewrite Hw2 in *. rewrite <- Hpe in *.
              apply (parse_int_prefix (c :: w') rest intv (pf ++ pe)) in Eint.
              apply (parse_frac_prefix (pf ++ pe) rest (fv, flen) pe) in Efrac.
              apply (parse_exp_prefix pe rest (eneg, ev) []) in Eexp.
              cbn [parse_number]. rewrite Eint. rewrite Efrac. rewrite Eexp. reflexivity.
           ++ apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (c :: w' ++ rest) intv w2 Eint) as [pi Hpi].
              destruct (parse_frac_shape w2 (fv, flen) w2' Efrac) as [pf Hpf].
              subst w2'.
              assert (Hw2 : w2 = pf ++ rest) by (rewrite <- Hpf; reflexivity).
              rewrite Hw2 in *.
              apply (parse_int_prefix (c :: w') rest intv pf) in Eint.
              apply (parse_frac_prefix pf rest (fv, flen) []) in Efrac.
              cbn [parse_number]. rewrite Eint. rewrite Efrac. reflexivity.
        -- destruct (parse_exp w2) as [[[eneg ev] w3] |] eqn:Eexp.
           ++ apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (c :: w' ++ rest) intv w2 Eint) as [pi Hpi].
              destruct (parse_exp_shape w2 (eneg, ev) w3 Eexp) as [pe Hpe].
              subst w3.
              assert (Hw2 : w2 = pe ++ rest) by (rewrite <- Hpe; reflexivity).
              rewrite Hw2 in *.
              apply (parse_int_prefix (c :: w') rest intv pe) in Eint.
              apply (parse_exp_prefix pe rest (eneg, ev) []) in Eexp.
              apply parse_frac_none_prefix in Efrac.
              cbn [parse_number]. rewrite Eint. rewrite Efrac. rewrite Eexp. reflexivity.
           ++ apply some_pair_inj in H as [Hme Hsuf]. rewrite <- Hme in *.
              destruct (parse_int_shape (c :: w' ++ rest) intv w2 Eint) as [pi Hpi].
              subst w2.
              apply (parse_int_prefix (c :: w') rest intv []) in Eint.
              cbn [parse_number]. rewrite Eint. reflexivity.
      * exfalso. apply (none_some_contra me rest H).
Qed.


(* The digit-run scanner agrees with take_digits. *)
Lemma skip_digits_fast_take (l : list ascii) (i : nat) :
  skipn (skip_digits_fast (Buf l) i) l = snd (take_digits (skipn i l)).
Proof.
  unfold skip_digits_fast, buffer_length.
  apply skip_digits_loop_sim. rewrite List.length_skipn. lia.
Qed.

Opaque Ascii.eqb.

(* Keep the digit-run scanner and char compare folded during the simulation
   proofs, so rewrite skip_digits_fast_take / buf_eq_char_sym still match. *)
Opaque skip_digits_fast.

(* buf_eq_char compares the char at i (as the *certified* parsers do:
   Ascii.eqb actual "."); swap the tokenizer's argument order. *)
Lemma buf_eq_char_sym (l : list ascii) (i : nat) (c : ascii) :
  buf_eq_char (Buf l) i c =
  match nth_error l i with Some c' => Ascii.eqb c' c | None => false end.
Proof.
  unfold buf_eq_char, buffer_get. destruct (nth_error l i) as [c' |].
  - apply Ascii.eqb_sym.
  - reflexivity.
Qed.

Lemma nth_error_none_skipn (A : Type) (l : list A) (k : nat) :
  nth_error l k = None -> skipn k l = [].
Proof.
  intros H. apply nth_error_None in H. apply skipn_all2. exact H.
Qed.

Lemma eqb_false_neq (x y : ascii) (H : x <> y) : Ascii.eqb x y = false.
Proof. apply Ascii.eqb_neq. exact H. Qed.

(* The exponent scanner agrees with parse_exp: it ends exactly where the
   certified parser's remaining suffix begins (or j = i1 when parse_exp fails,
   leaving the 'e' in place). *)
Lemma parse_exp_fast_span (l : list ascii) (i1 : nat) :
  match parse_exp_fast (Buf l) i1 with
  | Some j =>
      match parse_exp (skipn i1 l) with
      | None => j = i1
      | Some (ev, rest) => rest = skipn j l
      end
  | None => False
  end.
Proof.
  unfold parse_exp_fast, buffer_get, buffer_length.
  rewrite !buf_eq_char_sym.
  destruct (nth_error l i1) as [c |] eqn:Ei1.
  - destruct (is_expb c) eqn:Eexp.
    + (* exp present *)
      cbn [orb].
      destruct (nth_error l (S i1)) as [s |] eqn:Es.
      * destruct (Ascii.eqb_spec s "-"%char) as [Hneg | Hneg].
        -- subst s. (* sign '-' : i2 = S (S i1) *)
           assert (Hp : "-"%char <> "+"%char) by discriminate.
           rewrite (eqb_false_neq "-"%char "+"%char Hp). cbn [orb].
           destruct (nth_error l (S (S i1))) as [c' |] eqn:Ec'.
           ** destruct (is_digitb c') eqn:Ed.
              --- (* exp has a digit *)
                  rewrite (skip_digits_fast_take l (S (S i1))).
                  cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
                  cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
                  rewrite (skipn_cons_head ascii l (S i1) "-"%char Es).
                  cbn [parse_exp take_digits]. rewrite (Ascii.eqb_refl "-"%char). cbn [parse_exp take_digits].
                  rewrite (skipn_cons_head ascii l (S (S i1)) c' Ec').
                  cbn [parse_exp take_digits].
                  destruct (is_digitb c') eqn:Ed2.
                  ++++ destruct (take_digits (skipn (S (S (S i1))) l)) as [ds' rest'] eqn:Et.
                       cbn [parse_exp take_digits]. reflexivity.
                  ++++ congruence.
              --- (* no digit: exp fails, j = i1 *)
                  cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
                  cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
                  rewrite (skipn_cons_head ascii l (S i1) "-"%char Es).
                  cbn [parse_exp take_digits]. rewrite (Ascii.eqb_refl "-"%char). cbn [parse_exp take_digits].
                  rewrite (skipn_cons_head ascii l (S (S i1)) c' Ec').
                  cbn [parse_exp take_digits].
                  destruct (is_digitb c') eqn:Ed2.
                  ++++ congruence.
                  ++++ destruct (take_digits (skipn (S (S (S i1))) l)) as [ds' rest'] eqn:Et. cbn [parse_exp take_digits]. reflexivity.
           ** (* buffer ends right after '-' : j = i1 *)
              cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
              cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
              rewrite (skipn_cons_head ascii l (S i1) "-"%char Es).
              cbn [parse_exp take_digits]. rewrite (Ascii.eqb_refl "-"%char). cbn [parse_exp take_digits].
              rewrite (nth_error_none_skipn ascii l (S (S i1)) Ec'). reflexivity.
        -- destruct (Ascii.eqb_spec s "+"%char) as [Hpos | Hpos].
           ++ subst s. (* sign '+' : i2 = S (S i1) *)
              cbn [orb].
              destruct (nth_error l (S (S i1))) as [c' |] eqn:Ec'.
              ** destruct (is_digitb c') eqn:Ed.
                 --- rewrite (skip_digits_fast_take l (S (S i1))).
                     cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
                     cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
                     rewrite (skipn_cons_head ascii l (S i1) "+"%char Es).
                     cbn [parse_exp take_digits]. rewrite (eqb_false_neq "+"%char "-"%char ltac:(discriminate)). rewrite (Ascii.eqb_refl "+"%char). cbn [parse_exp take_digits].
                     rewrite (skipn_cons_head ascii l (S (S i1)) c' Ec').
                     cbn [parse_exp take_digits].
                     destruct (is_digitb c') eqn:Ed2.
                     ++++ destruct (take_digits (skipn (S (S (S i1))) l)) as [ds' rest'] eqn:Et. cbn [parse_exp take_digits]. reflexivity.
                     ++++ congruence.
                 --- cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
                     cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
                     rewrite (skipn_cons_head ascii l (S i1) "+"%char Es).
                     cbn [parse_exp take_digits]. rewrite (eqb_false_neq "+"%char "-"%char ltac:(discriminate)). rewrite (Ascii.eqb_refl "+"%char). cbn [parse_exp take_digits].
                     rewrite (skipn_cons_head ascii l (S (S i1)) c' Ec').
                     cbn [parse_exp take_digits].
                     destruct (is_digitb c') eqn:Ed2.
                     ++++ congruence.
                     ++++ destruct (take_digits (skipn (S (S (S i1))) l)) as [ds' rest'] eqn:Et. cbn [parse_exp take_digits]. reflexivity.
              ** cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
                 cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
                 rewrite (skipn_cons_head ascii l (S i1) "+"%char Es).
                 cbn [parse_exp take_digits]. rewrite (eqb_false_neq "+"%char "-"%char ltac:(discriminate)). rewrite (Ascii.eqb_refl "+"%char). cbn [parse_exp take_digits].
                 rewrite (nth_error_none_skipn ascii l (S (S i1)) Ec'). reflexivity.
           ++ (* no sign: i2 = S i1 *)
              cbn [orb]. rewrite Es. cbn [orb].
              destruct (is_digitb s) eqn:Ed.
              ** (* exp has a digit *)
                 rewrite (skip_digits_fast_take l (S i1)).
                 cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
                 cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
                 rewrite (skipn_cons_head ascii l (S i1) s Es).
                 cbn [parse_exp take_digits]. rewrite (proj2 (Ascii.eqb_neq s "-") Hneg). rewrite (proj2 (Ascii.eqb_neq s "+") Hpos). cbn [parse_exp take_digits].
                 cbn [parse_exp take_digits].
                 destruct (is_digitb s) eqn:Ed2.
                 ++++ destruct (take_digits (skipn (S (S i1)) l)) as [ds' rest'] eqn:Et. cbn [parse_exp take_digits]. reflexivity.
                 ++++ congruence.
              ** (* no digit *)
                 cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
                 cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
                 rewrite (skipn_cons_head ascii l (S i1) s Es).
                 cbn [parse_exp take_digits]. rewrite (proj2 (Ascii.eqb_neq s "-") Hneg). rewrite (proj2 (Ascii.eqb_neq s "+") Hpos). cbn [parse_exp take_digits].
                 cbn [parse_exp take_digits].
                 destruct (is_digitb s) eqn:Ed2.
                 ++++ congruence.
                 ++++ destruct (take_digits (skipn (S (S i1)) l)) as [ds' rest'] eqn:Et. cbn [parse_exp take_digits]. reflexivity.
      * (* no char after 'e' : exp fails *)
        cbn [orb].
        cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
        cbn [parse_exp take_digits]. rewrite Eexp. cbn [parse_exp take_digits].
        assert (Hsk : skipn (S i1) l = []) by (apply nth_error_none_skipn; exact Es).
        destruct (nth_error l (S i1)) as [s' |] eqn:En.
        -- congruence.
        -- destruct (skipn (S i1) l) as [| s' rest] eqn:Esk.
           ++ cbn. reflexivity.
           ++ congruence.
    + (* no exp *)
      cbn [orb].
      cbn [parse_exp take_digits]. rewrite (skipn_cons_head ascii l i1 c Ei1).
      cbn [parse_exp take_digits]. rewrite Eexp. reflexivity.
  - (* i1 out of bounds *)
    cbn [parse_exp take_digits]. rewrite (nth_error_none_skipn ascii l i1 Ei1). reflexivity.
Qed.



(* The exp scanner relation, stated with the remaining suffix (for use inside
   the frac/exp tail, where the frac already consumed a suffix). *)
Lemma parse_exp_fast_span_list (l : list ascii) (i1 : nat) :
  match parse_exp_fast (Buf l) i1 with
  | Some j =>
      match parse_exp (skipn i1 l) with
      | None => skipn i1 l = skipn j l
      | Some (ev, rest) => rest = skipn j l
      end
  | None => False
  end.
Proof.
  destruct (parse_exp_fast (Buf l) i1) as [j |] eqn:Efe.
  - pose proof (parse_exp_fast_span l i1) as Hpe. rewrite Efe in Hpe.
    destruct (parse_exp (skipn i1 l)) as [[ev rest] |].
    + cbn in Hpe. exact Hpe.
    + cbn in Hpe. subst j. reflexivity.
  - pose proof (parse_exp_fast_span l i1) as Hpe. rewrite Efe in Hpe. exact Hpe.
Qed.

(* A fraction (dot + digit) is consumed: its suffix is exactly where the
   digit-run scanner ends. *)
Lemma parse_frac_fast_suffix (l : list ascii) (k : nat) (c1 : ascii) :
  nth_error l k = Some "."%char ->
  nth_error l (S k) = Some c1 ->
  is_digitb c1 = true ->
  exists fv : Z * nat, parse_frac (skipn k l) = Some (fv, skipn (skip_digits_fast (Buf l) (S k)) l).
Proof.
  intros Hdot Hnth Hdig.
  unfold parse_frac. rewrite (skipn_cons_head ascii l k "."%char Hdot). rewrite (skipn_cons_head ascii l (S k) c1 Hnth).
  cbn [take_digits]. rewrite (Ascii.eqb_refl "."%char). cbn [take_digits].
  rewrite Hdig. cbn [take_digits].
  destruct (take_digits (skipn (S (S k)) l)) as [ds rest'] eqn:Et.
  cbn [take_digits].
  exists (digits_to_nat_fast (c1 :: ds), List.length (c1 :: ds)).
  rewrite (skip_digits_fast_take l (S k)). rewrite (skipn_cons_head ascii l (S k) c1 Hnth). cbn [take_digits]. rewrite Hdig. rewrite Et. cbn. reflexivity.
Qed.

(* A fraction with no digit (dot not followed by a digit) parses to None. *)
Lemma parse_frac_fast_none (l : list ascii) (k : nat) (c1 : ascii) :
  nth_error l k = Some "."%char ->
  nth_error l (S k) = Some c1 ->
  is_digitb c1 = false ->
  parse_frac (skipn k l) = None.
Proof.
  intros Hdot Hnth Hdig.
  unfold parse_frac. rewrite (skipn_cons_head ascii l k "."%char Hdot). rewrite (skipn_cons_head ascii l (S k) c1 Hnth).
  cbn [take_digits]. rewrite (Ascii.eqb_refl "."%char). cbn [take_digits]. rewrite Hdig. cbn. reflexivity.
Qed.

(* A fraction whose digit run is empty (dot at end of buffer) parses to None. *)
Lemma parse_frac_fast_none_end (l : list ascii) (k : nat) :
  nth_error l k = Some "."%char ->
  nth_error l (S k) = None ->
  parse_frac (skipn k l) = None.
Proof.
  intros Hdot Hnth.
  unfold parse_frac. rewrite (skipn_cons_head ascii l k "."%char Hdot). rewrite (nth_error_none_skipn ascii l (S k) Hnth).
  cbn [take_digits]. rewrite (Ascii.eqb_refl "."%char). cbn. reflexivity.
Qed.

(* The frac/exp tail scanner agrees with parse_frac/parse_exp: it ends exactly
   where the certified parsers' remaining suffix begins. *)
Lemma parse_frac_exp_fast_span (l : list ascii) (k : nat) :
  match parse_frac_exp_fast (Buf l) k with
  | Some j =>
      match parse_frac (skipn k l) with
      | None =>
          match parse_exp (skipn k l) with
          | None => j = k
          | Some (ev, rest) => rest = skipn j l
          end
      | Some (fv, w2') =>
          match parse_exp w2' with
          | None => w2' = skipn j l
          | Some (ev, rest) => rest = skipn j l
          end
      end
  | None => False
  end.
Proof.
  unfold parse_frac_exp_fast.
  rewrite buf_eq_char_sym.
  destruct (nth_error l k) as [c |] eqn:Ek.
  - destruct (Ascii.eqb_spec c "."%char) as [Hc | Hc].
    + subst c. cbn [orb].
      destruct (nth_error l (S k)) as [c1 |] eqn:En.
      * destruct (is_digitb c1) eqn:Edig.
        -- (* frac present: i1 = skip_digits_fast (Buf l) (S k) *)
           unfold parse_exp_fast, buffer_get, buffer_length.
           rewrite En. cbn [orb]. rewrite Edig. cbn [orb].
           destruct (parse_frac_fast_suffix l k c1 Ek En Edig) as [fv Hfrac].
           rewrite Hfrac. cbn [parse_exp]. exact (parse_exp_fast_span_list l (skip_digits_fast (Buf l) (S k))).
        -- (* '.' no digit: i1 = k *)
           unfold parse_exp_fast, buffer_get, buffer_length.
           rewrite En. cbn [orb]. rewrite Edig. cbn [orb].
           rewrite (parse_frac_fast_none l k c1 Ek En Edig). cbn [parse_exp].
           exact (parse_exp_fast_span l k).
      * (* '.' then buffer end: i1 = k *)
        unfold parse_exp_fast, buffer_get, buffer_length.
        rewrite En. cbn [orb].
        rewrite (parse_frac_fast_none_end l k Ek En). cbn [parse_exp].
        exact (parse_exp_fast_span l k).
    + (* c <> "." *)
      cbn [orb].
      unfold parse_exp_fast, buffer_get, buffer_length.
      assert (Hfr : parse_frac (skipn k l) = None).
      { apply parse_frac_none. intros d Hd. rewrite (nth_error_skipn_head l k) in Hd. rewrite Ek in Hd. injection Hd as Hd'. subst d. apply (proj2 (Ascii.eqb_neq c "."%char) Hc). }
      rewrite Hfr. cbn [parse_exp]. exact (parse_exp_fast_span l k).
  - (* k out of bounds *)
    cbn [orb].
    unfold parse_exp_fast, buffer_get, buffer_length.
    assert (Hfr : parse_frac (skipn k l) = None).
    { apply parse_frac_none. intros d Hd. rewrite (nth_error_skipn_head l k) in Hd. rewrite Ek in Hd. discriminate. }
    rewrite Hfr. cbn [parse_exp]. exact (parse_exp_fast_span l k).
Qed.

(* parse_int agrees with the buffer scan: "0" and digit1-9 give the right suffix. *)
Lemma parse_int_fast_zero (l : list ascii) (i1 : nat) :
  nth_error l i1 = Some "0"%char ->
  parse_int (skipn i1 l) = Some (0%Z, skipn (S i1) l).
Proof.
  intros H. unfold parse_int. rewrite (skipn_cons_head ascii l i1 "0"%char H). cbn [orb].
  rewrite (Ascii.eqb_refl "0"%char). reflexivity.
Qed.

Lemma parse_int_fast_digit (l : list ascii) (i1 : nat) (d : ascii) :
  nth_error l i1 = Some d ->
  is_digit1_9b d = true ->
  d <> "0"%char ->
  parse_int (skipn i1 l) = Some (digits_to_nat_fast (d :: fst (take_digits (skipn (S i1) l))), skipn (skip_digits_fast (Buf l) (S i1)) l).
Proof.
  intros Hnth Hdig Hnz.
  unfold parse_int. rewrite (skipn_cons_head ascii l i1 d Hnth). cbn [orb].
  rewrite (proj2 (Ascii.eqb_neq d "0"%char) Hnz). rewrite Hdig. cbn [orb].
  destruct (take_digits (skipn (S i1) l)) as [ds rest'] eqn:Et.
  cbn [orb].
  rewrite (skip_digits_fast_take l (S i1)). rewrite Et. cbn. reflexivity.
Qed.

(* The parse_number tail (frac/exp after the int) ends where parse_frac_exp_fast
   ends, so parse_number returns Some (me, skipn j l). *)
Lemma parse_number_frac_exp_tail (l : list ascii) (i1 : nat) (intv intz : Z) (neg : bool) :
  match parse_frac_exp_fast (Buf l) i1 with
  | Some j =>
      exists me : Z * Z,
        (match parse_frac (skipn i1 l) with
         | None =>
             match parse_exp (skipn i1 l) with
             | None => Some ((intz, 0%Z), skipn i1 l)
             | Some ((eneg, expv), w3) => Some ((intz, if eneg then Z.opp expv else expv), w3)
             end
         | Some ((fv, flen), w2') =>
             let mant := (intv * pow10 flen + fv)%Z in
             let mz := if neg then Z.opp mant else mant in
             match parse_exp w2' with
             | None => Some ((mz, Z.opp (Z.of_nat flen)), w2')
             | Some ((eneg, expv), w3) => Some ((mz, Z.sub (if eneg then Z.opp expv else expv) (Z.of_nat flen)), w3)
             end
         end) = Some (me, skipn j l)
  | None => False
  end.
Proof.
  destruct (parse_frac_exp_fast (Buf l) i1) as [j |] eqn:Efe.
  - pose proof (parse_frac_exp_fast_span l i1) as Hpe. rewrite Efe in Hpe. cbn in Hpe.
    destruct (parse_frac (skipn i1 l)) as [[[fv flen] w2'] |] eqn:Efrac.
    + cbn in Hpe. destruct (parse_exp w2') as [[[eneg expv] w3] |] eqn:Eexp.
      * cbn in Hpe. eexists. rewrite <- Hpe. reflexivity.
      * cbn in Hpe. eexists. rewrite <- Hpe. reflexivity.
    + cbn in Hpe. destruct (parse_exp (skipn i1 l)) as [[[eneg expv] w3] |] eqn:Eexp.
      * cbn in Hpe. eexists. rewrite <- Hpe. reflexivity.
      * cbn in Hpe. subst j. eexists. reflexivity.
  - pose proof (parse_frac_exp_fast_span l i1) as Hpe. rewrite Efe in Hpe. exfalso. exact Hpe.
Qed.

(* parse_int returns None for a char that is neither 0 nor digit1-9. *)
Lemma parse_int_fast_none (c : ascii) (w : list ascii) :
  c <> "0"%char -> is_digit1_9b c = false -> parse_int (c :: w) = None.
Proof.
  intros Hnz H19. unfold parse_int. cbn [orb].
  destruct (Ascii.eqb_spec c "0"%char) as [H0 | H0].
  - subst c. exfalso. apply Hnz. reflexivity.
  - rewrite H19. cbn [orb]. reflexivity.
Qed.

(* The number tokenizer agrees with parse_number: same remaining suffix. *)
Lemma parse_number_fast_span (l : list ascii) (i : nat) :
  match parse_number_fast (Buf l) i with
  | Some (v, j) => exists me : Z * Z, parse_number (skipn i l) = Some (me, skipn j l)
  | None => parse_number (skipn i l) = None
  end.
Proof.
  unfold parse_number_fast, buffer_get, buffer_length.
  rewrite buf_eq_char_sym.
  destruct (nth_error l i) as [c |] eqn:Ei.
  - destruct (Ascii.eqb_spec c "-"%char) as [Hc | Hc].
    + subst c. cbn [orb].
      destruct (nth_error l (S i)) as [d |] eqn:Ed.
      * destruct (Ascii.eqb_spec d "0"%char) as [H0 | H0].
        -- subst d. cbn [orb].
           unfold parse_number. rewrite (skipn_cons_head ascii l i "-"%char Ei). cbn [orb].
           rewrite (Ascii.eqb_refl "-"%char). cbn [orb].
           destruct (parse_int (skipn (S i) l)) as [[intv w2] |] eqn:Eint.
           ++++ rewrite (parse_int_fast_zero l (S i) Ed) in Eint. injection Eint as E1 E2. subst intv w2.
                destruct (parse_frac_exp_fast (Buf l) (S (S i))) as [j |] eqn:Efe.
                ++++++ cbn [orb]. pose proof (parse_number_frac_exp_tail l (S (S i)) 0%Z 0%Z true) as Ht. rewrite Efe in Ht. exact Ht.
                ++++++ pose proof (parse_number_frac_exp_tail l (S (S i)) 0%Z 0%Z true) as Ht. rewrite Efe in Ht. exfalso. exact Ht.
           ++++ exfalso. rewrite (parse_int_fast_zero l (S i) Ed) in Eint. discriminate.
        -- destruct (is_digit1_9b d) eqn:E19.
           ++ cbn [orb].
              unfold parse_number. rewrite (skipn_cons_head ascii l i "-"%char Ei). cbn [orb].
              rewrite (Ascii.eqb_refl "-"%char). cbn [orb].
              destruct (parse_int (skipn (S i) l)) as [[intv w2] |] eqn:Eint.
              ++++ rewrite (parse_int_fast_digit l (S i) d Ed E19 H0) in Eint. injection Eint as E1 E2. subst intv w2. cbn [orb].
                   destruct (parse_frac_exp_fast (Buf l) (skip_digits_fast (Buf l) (S (S i)))) as [j |] eqn:Efe.
                   ++++++ cbn [orb]. pose proof (parse_number_frac_exp_tail l (skip_digits_fast (Buf l) (S (S i))) (digits_to_nat_fast (d :: fst (take_digits (skipn (S (S i)) l)))) (Z.opp (digits_to_nat_fast (d :: fst (take_digits (skipn (S (S i)) l))))) true) as Ht. rewrite Efe in Ht. exact Ht.
                   ++++++ pose proof (parse_number_frac_exp_tail l (skip_digits_fast (Buf l) (S (S i))) (digits_to_nat_fast (d :: fst (take_digits (skipn (S (S i)) l)))) (Z.opp (digits_to_nat_fast (d :: fst (take_digits (skipn (S (S i)) l))))) true) as Ht. rewrite Efe in Ht. exfalso. exact Ht.
              ++++ exfalso. rewrite (parse_int_fast_digit l (S i) d Ed E19 H0) in Eint. discriminate.
           ++ cbn [orb].
              unfold parse_number. rewrite (skipn_cons_head ascii l i "-"%char Ei). cbn [orb].
              rewrite (Ascii.eqb_refl "-"%char). cbn [orb].
              rewrite (skipn_cons_head ascii l (S i) d Ed). cbn [orb]. cbn [parse_int].
              destruct (Ascii.eqb d "0"%char) eqn:Ez.
              ++++ exfalso. apply H0. apply Ascii.eqb_eq. exact Ez.
              ++++ rewrite E19. cbn [orb]. reflexivity.
      * unfold parse_number. rewrite (skipn_cons_head ascii l i "-"%char Ei). cbn [orb].
        rewrite (Ascii.eqb_refl "-"%char). cbn [orb].
        rewrite (nth_error_none_skipn ascii l (S i) Ed). cbn. reflexivity.
    + cbn [orb]. rewrite Ei. cbn [orb].
      destruct (Ascii.eqb_spec c "0"%char) as [H0 | H0].
      * subst c. cbn [orb].
        unfold parse_number. rewrite (skipn_cons_head ascii l i "0"%char Ei). cbn [orb].
        rewrite (eqb_false_neq "0"%char "-"%char ltac:(discriminate)). cbn [orb].
        cbn [parse_int]. rewrite (Ascii.eqb_refl "0"%char). cbn [orb].
        destruct (parse_frac_exp_fast (Buf l) (S i)) as [j |] eqn:Efe.
        ++++ cbn [orb]. pose proof (parse_number_frac_exp_tail l (S i) 0%Z 0%Z false) as Ht. rewrite Efe in Ht. exact Ht.
        ++++ pose proof (parse_number_frac_exp_tail l (S i) 0%Z 0%Z false) as Ht. rewrite Efe in Ht. exfalso. exact Ht.
      * destruct (is_digit1_9b c) eqn:E19.
        ++ cbn [orb].
           unfold parse_number. rewrite (skipn_cons_head ascii l i c Ei). cbn [orb].
           rewrite (eqb_false_neq c "-"%char Hc). cbn [orb].
           cbn [parse_int]. destruct (Ascii.eqb c "0"%char) eqn:Ez.
           ++++ exfalso. apply H0. apply Ascii.eqb_eq. exact Ez.
           ++++ rewrite E19. cbn [orb].
                destruct (take_digits (skipn (S i) l)) as [ds rest'] eqn:Et.
                cbn [orb].
                assert (Hsk : skipn (skip_digits_fast (Buf l) (S i)) l = rest') by (rewrite (skip_digits_fast_take l (S i)); rewrite Et; cbn; reflexivity).
                rewrite <- Hsk in *.
                destruct (parse_frac_exp_fast (Buf l) (skip_digits_fast (Buf l) (S i))) as [j |] eqn:Efe.
                ++++++ cbn [orb]. pose proof (parse_number_frac_exp_tail l (skip_digits_fast (Buf l) (S i)) (digits_to_nat_fast (c :: ds)) (digits_to_nat_fast (c :: ds)) false) as Ht. rewrite Efe in Ht. exact Ht.
                ++++++ pose proof (parse_number_frac_exp_tail l (skip_digits_fast (Buf l) (S i)) (digits_to_nat_fast (c :: ds)) (digits_to_nat_fast (c :: ds)) false) as Ht. rewrite Efe in Ht. exfalso. exact Ht.
        ++ cbn [orb].
           unfold parse_number. rewrite (skipn_cons_head ascii l i c Ei). cbn [orb].
           rewrite (eqb_false_neq c "-"%char Hc). cbn [orb]. cbn [parse_int].
           destruct (Ascii.eqb_spec c "0"%char) as [Hc0 | Hc0].
           ++++ exfalso. apply H0. exact Hc0.
           ++++ rewrite E19. cbn [orb]. reflexivity.
  - rewrite Ei. cbn.
    unfold parse_number. rewrite (nth_error_none_skipn ascii l i Ei). cbn. reflexivity.
Qed.



(* decode_number re-parses the number span and returns exactly the value that
   parse_number produces, so decode materializes the span faithfully. *)
Lemma decode_number_correct (l : list ascii) (s len : nat) (me : Z * Z) :
  parse_number (skipn s l) = Some (me, skipn (s + len) l) ->
  decode_number (Buf l) s len = me.
Proof.
  intros H. unfold decode_number, span_to_list, buffer_to_list.
  destruct me as [m e].
  pose proof (parse_number_reparse (firstn len (skipn s l)) (skipn len (skipn s l)) (m, e)) as Hre.
  rewrite firstn_skipn in Hre.
  rewrite (skipn_skipn len s l) in Hre.
  rewrite (Nat.add_comm len s) in Hre.
  specialize (Hre H).
  rewrite Hre. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* String simulation: find_string_end agrees with parse_string_chars_fast.    *)
(* ------------------------------------------------------------------------- *)

Transparent Ascii.eqb.

(* A \uXXXX escape decodes exactly like the certified parser. *)
Lemma parse_string_chars_fast_u (ha hb hc hd : ascii) (rest'' : list ascii) :
  is_hexb ha && is_hexb hb && is_hexb hc && is_hexb hd = true ->
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: hb :: hc :: hd :: rest'') =
    string_cons (codepoint_to_utf8 (hex_val ha * 4096 + hex_val hb * 256 + hex_val hc * 16 + hex_val hd)) (parse_string_chars_fast rest'').
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

Lemma parse_string_chars_fast_u_none (ha hb hc hd : ascii) (rest'' : list ascii) :
  is_hexb ha && is_hexb hb && is_hexb hc && is_hexb hd = false ->
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: hb :: hc :: hd :: rest'') = None.
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

(* A non-\u escape char (quote, backslash, slash, b, f, n, r, t). *)
Lemma parse_string_chars_fast_escape (e : ascii) (rest' : list ascii) :
  is_escape_char e = true ->
  exists bytes : list ascii,
    parse_string_chars_fast ("092"%char :: e :: rest') = string_cons bytes (parse_string_chars_fast rest').
Proof.
  unfold is_escape_char. intro H.
  destruct (Ascii.eqb_spec e "034"%char) as [H1 | H1].
  - subst e. exists ["034"%char]. cbn. reflexivity.
  - destruct (Ascii.eqb_spec e "092"%char) as [H2 | H2].
    + subst e. exists ["092"%char]. cbn. reflexivity.
    + destruct (Ascii.eqb_spec e "047"%char) as [H3 | H3].
      * subst e. exists ["047"%char]. cbn. reflexivity.
      * destruct (Ascii.eqb_spec e "b"%char) as [H4 | H4].
        -- subst e. exists ["008"%char]. cbn. reflexivity.
        -- destruct (Ascii.eqb_spec e "f"%char) as [H5 | H5].
           ++ subst e. exists ["012"%char]. cbn. reflexivity.
           ++ destruct (Ascii.eqb_spec e "n"%char) as [H6 | H6].
              ** subst e. exists ["010"%char]. cbn. reflexivity.
              ** destruct (Ascii.eqb_spec e "r"%char) as [H7 | H7].
                 --- subst e. exists ["013"%char]. cbn. reflexivity.
                 --- destruct (Ascii.eqb_spec e "t"%char) as [H8 | H8].
                     ++++ subst e. exists ["009"%char]. cbn. reflexivity.
                     ++++ exfalso. cbn in H. discriminate.
Qed.

(* The decoded bytes of a simple escape depend only on the escape char. *)
Definition escape_bytes (e : ascii) : list ascii :=
  if Ascii.eqb e "034"%char then ["034"%char]
  else if Ascii.eqb e "092"%char then ["092"%char]
  else if Ascii.eqb e "047"%char then ["047"%char]
  else if Ascii.eqb e "b"%char then ["008"%char]
  else if Ascii.eqb e "f"%char then ["012"%char]
  else if Ascii.eqb e "n"%char then ["010"%char]
  else if Ascii.eqb e "r"%char then ["013"%char]
  else if Ascii.eqb e "t"%char then ["009"%char]
  else nil.

Lemma parse_string_chars_fast_escape_det (e : ascii) (rest : list ascii) :
  is_escape_char e = true ->
  parse_string_chars_fast ("092"%char :: e :: rest) = string_cons (escape_bytes e) (parse_string_chars_fast rest).
Proof.
  unfold is_escape_char, escape_bytes. intro H.
  destruct (Ascii.eqb_spec e "034"%char) as [H1 | H1]; [subst e; reflexivity |].
  destruct (Ascii.eqb_spec e "092"%char) as [H2 | H2]; [subst e; reflexivity |].
  destruct (Ascii.eqb_spec e "047"%char) as [H3 | H3]; [subst e; reflexivity |].
  destruct (Ascii.eqb_spec e "b"%char) as [H4 | H4]; [subst e; reflexivity |].
  destruct (Ascii.eqb_spec e "f"%char) as [H5 | H5]; [subst e; reflexivity |].
  destruct (Ascii.eqb_spec e "n"%char) as [H6 | H6]; [subst e; reflexivity |].
  destruct (Ascii.eqb_spec e "r"%char) as [H7 | H7]; [subst e; reflexivity |].
  destruct (Ascii.eqb_spec e "t"%char) as [H8 | H8]; [subst e; reflexivity |].
  exfalso. cbn in H. discriminate.
Qed.

(* The closing quote is never a hex digit (used for short \u escapes). *)
Lemma is_hexb_quote : is_hexb "034"%char = false.
Proof. cbn [is_hexb is_digitb Ascii.eqb]. reflexivity. Qed.

Opaque Ascii.eqb.

Lemma parse_string_chars_fast_u3 (ha hb hc : ascii) :
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: hb :: hc :: []) = None.
Proof. cbn [parse_string_chars_fast]. reflexivity. Qed.

Lemma parse_string_chars_fast_u2 (ha hb : ascii) :
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: hb :: []) = None.
Proof. cbn [parse_string_chars_fast]. reflexivity. Qed.

Lemma parse_string_chars_fast_u1 (ha : ascii) :
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: []) = None.
Proof. cbn [parse_string_chars_fast]. reflexivity. Qed.

Lemma parse_string_chars_fast_u0 :
  parse_string_chars_fast ("092"%char :: "u"%char :: []) = None.
Proof. cbn [parse_string_chars_fast]. reflexivity. Qed.

Lemma parse_string_chars_fast_nochar :
  parse_string_chars_fast ("092"%char :: []) = None.
Proof. cbn [parse_string_chars_fast]. reflexivity. Qed.

(* A regular (non-quote, non-backslash) char c: consume it and recurse. *)
Lemma parse_string_chars_fast_char (c : ascii) (rest : list ascii) :
  Ascii.eqb c "034" = false ->
  Ascii.eqb c "092" = false ->
  parse_string_chars_fast (c :: rest) =
    match parse_string_chars_fast rest with
    | Some (cs, rest') => Some (c :: cs, rest')
    | None => None
    end.
Proof.
  intros Hq Hb. cbn [parse_string_chars_fast]. rewrite Hq, Hb. cbn.
  unfold is_string_charb. rewrite Hq, Hb. cbn. reflexivity.
Qed.

(* An escape char that is neither \u nor one of the 8 simple escapes fails. *)
Lemma parse_string_chars_fast_invalid_escape (e : ascii) (rest : list ascii) :
  is_escape_char e = false ->
  Ascii.eqb e "u"%char = false ->
  parse_string_chars_fast ("092"%char :: e :: rest) = None.
Proof.
  intros Hesc Hu.
  cbn [parse_string_chars_fast].
  destruct (Ascii.eqb_spec e "034"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  destruct (Ascii.eqb_spec e "092"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  destruct (Ascii.eqb_spec e "047"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  destruct (Ascii.eqb_spec e "b"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  destruct (Ascii.eqb_spec e "f"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  destruct (Ascii.eqb_spec e "n"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  destruct (Ascii.eqb_spec e "r"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  destruct (Ascii.eqb_spec e "t"%char) as [Heq | _]; [subst e; exfalso; cbn in Hesc; discriminate |].
  rewrite Hu. reflexivity.
Qed.

Lemma parse_u_escape_fast_spec (l : list ascii) (i : nat) (ha hb hc hd : ascii) :
  nth_error l (S (S i)) = Some ha ->
  nth_error l (S (S (S i))) = Some hb ->
  nth_error l (S (S (S (S i)))) = Some hc ->
  nth_error l (S (S (S (S (S i))))) = Some hd ->
  parse_u_escape_fast (Buf l) i = is_hexb ha && is_hexb hb && is_hexb hc && is_hexb hd.
Proof.
  intros Ha Hb Hc Hd. unfold parse_u_escape_fast, buffer_get. rewrite Ha, Hb, Hc, Hd. reflexivity.
Qed.

(* parse_u_escape_fast fails when a hex digit is missing. *)
Lemma parse_u_escape_fast_none3 (l : list ascii) (i : nat) (ha hb hc : ascii) :
  nth_error l (S (S i)) = Some ha ->
  nth_error l (S (S (S i))) = Some hb ->
  nth_error l (S (S (S (S i)))) = Some hc ->
  nth_error l (S (S (S (S (S i))))) = None ->
  parse_u_escape_fast (Buf l) i = false.
Proof.
  intros Ha Hb Hc Hd. unfold parse_u_escape_fast, buffer_get. rewrite Ha, Hb, Hc, Hd. reflexivity.
Qed.

Lemma parse_u_escape_fast_none2 (l : list ascii) (i : nat) (ha hb : ascii) :
  nth_error l (S (S i)) = Some ha ->
  nth_error l (S (S (S i))) = Some hb ->
  nth_error l (S (S (S (S i)))) = None ->
  parse_u_escape_fast (Buf l) i = false.
Proof.
  intros Ha Hb Hc. unfold parse_u_escape_fast, buffer_get. rewrite Ha, Hb, Hc. reflexivity.
Qed.

Lemma parse_u_escape_fast_none1 (l : list ascii) (i : nat) (ha : ascii) :
  nth_error l (S (S i)) = Some ha ->
  nth_error l (S (S (S i))) = None ->
  parse_u_escape_fast (Buf l) i = false.
Proof.
  intros Ha Hb. unfold parse_u_escape_fast, buffer_get. rewrite Ha, Hb. reflexivity.
Qed.

Lemma parse_u_escape_fast_none0 (l : list ascii) (i : nat) :
  nth_error l (S (S i)) = None ->
  parse_u_escape_fast (Buf l) i = false.
Proof.
  intros Ha. unfold parse_u_escape_fast, buffer_get. rewrite Ha. reflexivity.
Qed.

Lemma le_add6 (n m : nat) : 6 + n <= S m -> n <= m.
Proof. lia. Qed.

Lemma le_add2 (n m : nat) : 2 + n <= S m -> n <= m.
Proof. lia. Qed.

(* find_string_end_loop agrees with parse_string_chars_fast: it stops at the
   closing quote, and the decoded string is the prefix up to that quote. *)
Lemma find_string_end_loop_sim (l : list ascii) (fuel : nat) (i : nat) :
  List.length (skipn i l) <= fuel ->
  match find_string_end_loop (Buf l) fuel i with
  | Some j => exists cs : list ascii, parse_string_chars_fast (skipn i l) = Some (cs, skipn (S j) l)
  | None => parse_string_chars_fast (skipn i l) = None
  end.
Proof.
  revert i. induction fuel as [| fuel' IH]; intros i Hfuel.
  - cbn [find_string_end_loop].
    assert (Hnil : skipn i l = []) by (apply length_zero_iff_nil; lia).
    rewrite Hnil. cbn [parse_string_chars_fast]. reflexivity.
  - cbn [find_string_end_loop buffer_get buffer_length].
    destruct (nth_error l i) as [c |] eqn:En.
    + destruct (Ascii.eqb_spec c "034"%char) as [Hc | Hc].
      * subst c. cbn [find_string_end_loop].
        rewrite (skipn_cons_head ascii l i "034"%char En).
        cbn [parse_string_chars_fast]. rewrite (Ascii.eqb_refl "034"%char). cbn.
        eexists. reflexivity.
      * destruct (Ascii.eqb_spec c "092"%char) as [Hbs | Hbs].
        -- subst c. cbn [find_string_end_loop].
           destruct (nth_error l (S i)) as [e |] eqn:En2.
           ** destruct (Ascii.eqb_spec e "u"%char) as [Hu | Hu].
              --- (* \u escape *)
                  subst e. cbn [find_string_end_loop].
                  rewrite (skipn_cons_head ascii l i "092"%char En).
                  rewrite (skipn_cons_head ascii l (S i) "u"%char En2).
                  destruct (nth_error l (S (S i))) as [ha |] eqn:Eha.
                  ++++ destruct (nth_error l (S (S (S i)))) as [hb |] eqn:Ehb.
                       ++++++ destruct (nth_error l (S (S (S (S i))))) as [hc |] eqn:Ehc.
                              ++++++++ destruct (nth_error l (S (S (S (S (S i)))))) as [hd |] eqn:Ehd.
                                       (* all 4 hex present *)
                                       rewrite (parse_u_escape_fast_spec l i ha hb hc hd Eha Ehb Ehc Ehd).
                                       destruct (is_hexb ha && is_hexb hb && is_hexb hc && is_hexb hd) eqn:Ehex.
                                       ++++++++++ cbn [find_string_end_loop].
                                                  rewrite (skipn_cons_head ascii l (S (S i)) ha Eha).
                                                  rewrite (skipn_cons_head ascii l (S (S (S i))) hb Ehb).
                                                  rewrite (skipn_cons_head ascii l (S (S (S (S i)))) hc Ehc).
                                                  rewrite (skipn_cons_head ascii l (S (S (S (S (S i))))) hd Ehd).
                                                  rewrite (parse_string_chars_fast_u ha hb hc hd (skipn (S (S (S (S (S (S i)))))) l) Ehex).
                                                  assert (Hlen : List.length (skipn (i + 6) l) <= fuel').
                                                  { rewrite (skipn_cons_head ascii l i "092"%char En) in Hfuel.
                                                    rewrite (skipn_cons_head ascii l (S i) "u"%char En2) in Hfuel.
                                                    rewrite (skipn_cons_head ascii l (S (S i)) ha Eha) in Hfuel.
                                                    rewrite (skipn_cons_head ascii l (S (S (S i))) hb Ehb) in Hfuel.
                                                    rewrite (skipn_cons_head ascii l (S (S (S (S i)))) hc Ehc) in Hfuel.
                                                    rewrite (skipn_cons_head ascii l (S (S (S (S (S i))))) hd Ehd) in Hfuel.
                                                    assert (Hi6 : i + 6 = S (S (S (S (S (S i)))))) by lia.
                                                    rewrite <- Hi6 in Hfuel.
                                                    exact (le_add6 (List.length (skipn (i + 6) l)) fuel' Hfuel). }
                                                  remember (find_string_end_loop (Buf l) fuel' (i + 6)) as fe eqn:Efj.
                                                  destruct fe as [j |].
                                                  { assert (Hi6 : i + 6 = S (S (S (S (S (S i)))))) by lia.
                                                    rewrite <- Hi6.
                                                    pose proof (IH (i + 6) Hlen) as Hih. rewrite <- Efj in Hih. cbn in Hih. destruct Hih as [cs' Hcs']. eexists. unfold string_cons. rewrite Hcs'. cbn. reflexivity. }
                                                  { assert (Hi6 : i + 6 = S (S (S (S (S (S i)))))) by lia.
                                                    rewrite <- Hi6.
                                                    pose proof (IH (i + 6) Hlen) as Hih. rewrite <- Efj in Hih. cbn in Hih. unfold string_cons. rewrite Hih. reflexivity. }
                                       ++++++++++ cbn [find_string_end_loop].
                                                  rewrite (skipn_cons_head ascii l (S (S i)) ha Eha).
                                                  rewrite (skipn_cons_head ascii l (S (S (S i))) hb Ehb).
                                                  rewrite (skipn_cons_head ascii l (S (S (S (S i)))) hc Ehc).
                                                  rewrite (skipn_cons_head ascii l (S (S (S (S (S i))))) hd Ehd).
                                                  rewrite (parse_string_chars_fast_u_none ha hb hc hd (skipn (S (S (S (S (S (S i)))))) l) Ehex).
                                                  reflexivity.
                              ++++++++++ (* hd None *)
                                       rewrite (parse_u_escape_fast_none3 l i ha hb hc Eha Ehb Ehc Ehd).
                                       cbn [find_string_end_loop].
                                       rewrite (skipn_cons_head ascii l (S (S i)) ha Eha).
                                       rewrite (skipn_cons_head ascii l (S (S (S i))) hb Ehb).
                                       rewrite (skipn_cons_head ascii l (S (S (S (S i)))) hc Ehc).
                                       rewrite (nth_error_none_skipn ascii l (S (S (S (S (S i))))) Ehd).
                                       rewrite (parse_string_chars_fast_u3 ha hb hc). reflexivity.
                       ++++++++ (* hc None *)
                             rewrite (parse_u_escape_fast_none2 l i ha hb Eha Ehb Ehc).
                             cbn [find_string_end_loop].
                             rewrite (skipn_cons_head ascii l (S (S i)) ha Eha).
                             rewrite (skipn_cons_head ascii l (S (S (S i))) hb Ehb).
                             rewrite (nth_error_none_skipn ascii l (S (S (S (S i)))) Ehc).
                             rewrite (parse_string_chars_fast_u2 ha hb). reflexivity.
                  ++++++ (* hb None *)
                       rewrite (parse_u_escape_fast_none1 l i ha Eha Ehb).
                       cbn [find_string_end_loop].
                       rewrite (skipn_cons_head ascii l (S (S i)) ha Eha).
                       rewrite (nth_error_none_skipn ascii l (S (S (S i))) Ehb).
                       rewrite (parse_string_chars_fast_u1 ha). reflexivity.
                  ++++ (* ha None *)
                       rewrite (parse_u_escape_fast_none0 l i Eha).
                       cbn [find_string_end_loop].
                       rewrite (nth_error_none_skipn ascii l (S (S i)) Eha).
                       rewrite (parse_string_chars_fast_u0). reflexivity.
              --- (* non-u escape *)
                  destruct (is_escape_char e) eqn:Eesc.
                  ++++ (* valid escape: skip 2 *)
                       cbn [find_string_end_loop].
                       rewrite (skipn_cons_head ascii l i "092"%char En).
                       rewrite (skipn_cons_head ascii l (S i) e En2).
                       destruct (parse_string_chars_fast_escape e (skipn (S (S i)) l) Eesc) as [bytes Hbytes].
                       rewrite Hbytes.
                       assert (Hlen : List.length (skipn (i + 2) l) <= fuel').
                       { rewrite (skipn_cons_head ascii l i "092"%char En) in Hfuel.
                         rewrite (skipn_cons_head ascii l (S i) e En2) in Hfuel.
                         assert (Hi2 : i + 2 = S (S i)) by lia.
                         rewrite <- Hi2 in Hfuel.
                         exact (le_add2 (List.length (skipn (i + 2) l)) fuel' Hfuel). }
                       remember (find_string_end_loop (Buf l) fuel' (i + 2)) as fe eqn:Efj.
                       destruct fe as [j |].
                       { assert (Hi2 : i + 2 = S (S i)) by lia.
                         rewrite <- Hi2.
                         pose proof (IH (i + 2) Hlen) as Hih. rewrite <- Efj in Hih. cbn in Hih. destruct Hih as [cs' Hcs']. eexists. unfold string_cons. rewrite Hcs'. cbn. reflexivity. }
                       { assert (Hi2 : i + 2 = S (S i)) by lia.
                         rewrite <- Hi2.
                         pose proof (IH (i + 2) Hlen) as Hih. rewrite <- Efj in Hih. cbn in Hih. unfold string_cons. rewrite Hih. reflexivity. }
                  ++++ (* invalid escape *)
                       cbn [find_string_end_loop].
                       rewrite (skipn_cons_head ascii l i "092"%char En).
                       rewrite (skipn_cons_head ascii l (S i) e En2).
                       destruct (Ascii.eqb_spec e "u"%char) as [Heu | Heu]; [exfalso; apply Hu; exact Heu |].
                       rewrite (parse_string_chars_fast_invalid_escape e (skipn (S (S i)) l) Eesc (proj2 (Ascii.eqb_neq e "u"%char) Heu)).
                       reflexivity.
           ** (* no char after backslash *)
              rewrite (skipn_cons_head ascii l i "092"%char En).
              rewrite (nth_error_none_skipn ascii l (S i) En2).
              rewrite (parse_string_chars_fast_nochar). reflexivity.
        -- (* regular char *)
           cbn [find_string_end_loop].
           rewrite (skipn_cons_head ascii l i c En).
           rewrite (parse_string_chars_fast_char c (skipn (S i) l) (proj2 (Ascii.eqb_neq c "034"%char) Hc) (proj2 (Ascii.eqb_neq c "092"%char) Hbs)).
           assert (Hlen : List.length (skipn (S i) l) <= fuel').
           { rewrite (skipn_cons_head ascii l i c En) in Hfuel. cbn in Hfuel. apply Nat.succ_le_mono in Hfuel. exact Hfuel. }
           remember (find_string_end_loop (Buf l) fuel' (S i)) as fe eqn:Efj.
           destruct fe as [j |].
           { pose proof (IH (S i) Hlen) as Hih. rewrite <- Efj in Hih. cbn [find_string_end_loop] in Hih. destruct Hih as [cs' Hcs']. eexists. rewrite Hcs'. cbn. reflexivity. }
           { pose proof (IH (S i) Hlen) as Hih. rewrite <- Efj in Hih. cbn [find_string_end_loop] in Hih. rewrite Hih. reflexivity. }
    + rewrite (nth_error_none_skipn ascii l i En). cbn [find_string_end_loop]. cbn [parse_string_chars_fast]. reflexivity.
Qed.


(* parse_string_fast (opening quote at i) agrees with the certified parse_string. *)
Lemma parse_string_fast_span (l : list ascii) (i : nat) :
  nth_error l i = Some "034"%char ->
  match parse_string_fast (Buf l) i with
  | Some (v, j) => exists s : list ascii, parse_string (skipn i l) = Some (s, skipn j l)
  | None => parse_string (skipn i l) = None
  end.
Proof.
  intros Ei.
  assert (Hlen : List.length (skipn (S i) l) <= List.length l) by (rewrite length_skipn; lia).
  pose proof (find_string_end_loop_sim l (List.length l) (S i) Hlen) as Hs.
  rewrite (skipn_cons_head ascii l i "034"%char Ei).
  cbn [parse_string]. rewrite (Ascii.eqb_refl "034"%char). cbn [parse_string].
  unfold parse_string_fast, find_string_end, buffer_length.
  destruct (find_string_end_loop (Buf l) (List.length l) (S i)) as [endq |] eqn:Efj.
  - destruct Hs as [cs Hcs].
    cbn [find_string_end_loop]. eexists. rewrite Hcs. reflexivity.
  - cbn [find_string_end_loop]. exact Hs.
Qed.

(* ------------------------------------------------------------------------- *)
(* decode correctness and the mutual value/array/object simulation.           *)
(* ------------------------------------------------------------------------- *)

Lemma skip_ws_idem (w : list ascii) : skip_ws (skip_ws w) = skip_ws w.
Proof.
  induction w as [| c w' IH]; [reflexivity |].
  cbn [skip_ws]. destruct (is_wsb c) eqn:E.
  - exact IH.
  - cbn [skip_ws]. rewrite E. reflexivity.
Qed.

Lemma skipn_inj (l : list ascii) (a b : nat) :
  a <= List.length l -> b <= List.length l ->
  skipn a l = skipn b l -> a = b.
Proof.
  intros Ha Hb H.
  apply (f_equal (@List.length ascii)) in H.
  rewrite List.length_skipn in H. rewrite List.length_skipn in H.
  lia.
Qed.

Lemma buf_eq_char_false (l : list ascii) (i : nat) (c : ascii) :
  buf_eq_char (Buf l) i c = false ->
  forall c' : ascii, nth_error l i = Some c' -> c' <> c.
Proof.
  unfold buf_eq_char, buffer_get. intros H c' Hc.
  rewrite Hc in H. apply (proj1 (Ascii.eqb_neq c c')) in H.
  intro E. apply H. symmetry. exact E.
Qed.

Lemma parse_string_chars_fast_shape (w cs rest : list ascii) :
  parse_string_chars_fast w = Some (cs, rest) ->
  { raw : list ascii & w = raw ++ "034"%char :: rest }.
Proof.
  intros H.
  pose proof (parse_string_chars_fast_eq (List.length w) w (Nat.le_refl _)) as Heq.
  rewrite Heq in H.
  exact (parse_string_chars_shape (List.length w) w cs rest H).
Qed.

Lemma parse_string_chars_fast_progress (l : list ascii) (i j : nat) (cs : list ascii) :
  parse_string_chars_fast (skipn i l) = Some (cs, skipn j l) -> i < j.
Proof.
  intros H.
  destruct (parse_string_chars_fast_shape (skipn i l) cs (skipn j l) H) as [raw Hraw].
  apply (f_equal (@List.length ascii)) in Hraw.
  rewrite List.length_app in Hraw. cbn in Hraw.
  assert (Hi : i < List.length l).
  { assert (Hpos : 0 < List.length (skipn i l)).
    { rewrite Hraw. cbn. lia. }
    rewrite List.length_skipn in Hpos. lia. }
  rewrite !List.length_skipn in Hraw.
  destruct (Nat.lt_ge_cases j (List.length l)) as [Hj | Hj]; lia.
Qed.

Lemma parse_number_forward (l : list ascii) (i j : nat) (me : Z * Z) :
  parse_number (skipn i l) = Some (me, skipn j l) -> i <= j.
Proof.
  intros H.
  destruct (parse_number_shape (skipn i l) me (skipn j l) H) as [pre Hpre].
  assert (Hnonempty : skipn i l <> []).
  { intro E. rewrite E in H. cbn in H. discriminate. }
  apply (f_equal (@List.length ascii)) in Hpre.
  rewrite List.length_app in Hpre.
  rewrite !List.length_skipn in Hpre.
  assert (Hi : i < List.length l).
  { apply Nat.nle_gt. intro Hle. apply Hnonempty. exact (skipn_all2 l Hle). }
  destruct (Nat.lt_ge_cases j (List.length l)) as [Hj | Hj]; lia.
Qed.

Lemma firstn_app_le (A : Type) (l1 l2 : list A) (n : nat) :
  List.length l1 <= n -> firstn n (l1 ++ l2) = l1 ++ firstn (n - List.length l1) l2.
Proof.
  revert l2 n. induction l1 as [| x l1 IH]; intros l2 n Hle.
  - simpl. f_equal. lia.
  - simpl. destruct n as [| n']; [simpl in Hle; lia |].
    simpl. f_equal. apply IH. simpl in Hle. lia.
Qed.

(* Short \u escapes: the closing quote lands inside the 4 hex slots. *)
Lemma parse_string_chars_fast_short3 (ha hb hc : ascii) (rest : list ascii) :
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: hb :: hc :: "034"%char :: rest) = None.
Proof.
  cbn [parse_string_chars_fast]. try rewrite !andb_false_l. try rewrite !andb_false_r. reflexivity.
Qed.

Lemma parse_string_chars_fast_short2 (ha hb : ascii) (rest : list ascii) :
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: hb :: "034"%char :: rest) = None.
Proof.
  destruct rest as [| x rest]; cbn [parse_string_chars_fast].
  - reflexivity.
  - try rewrite !andb_false_l. try rewrite !andb_false_r. reflexivity.
Qed.

Lemma parse_string_chars_fast_short1 (ha : ascii) (rest : list ascii) :
  parse_string_chars_fast ("092"%char :: "u"%char :: ha :: "034"%char :: rest) = None.
Proof.
  destruct rest as [| x rest]; cbn [parse_string_chars_fast]; [reflexivity |].
  destruct rest as [| y rest]; cbn [parse_string_chars_fast].
  - reflexivity.
  - try rewrite !andb_false_l. try rewrite !andb_false_r. reflexivity.
Qed.

Lemma parse_string_chars_fast_short0 (rest : list ascii) :
  parse_string_chars_fast ("092"%char :: "u"%char :: "034"%char :: rest) = None.
Proof.
  destruct rest as [| x rest]; cbn [parse_string_chars_fast]; [reflexivity |].
  destruct rest as [| y rest]; cbn [parse_string_chars_fast]; [reflexivity |].
  destruct rest as [| z rest]; cbn [parse_string_chars_fast].
  - reflexivity.
  - try rewrite !andb_false_l. try rewrite !andb_false_r. reflexivity.
Qed.

(* Re-parsing the same raw body against a different trailing suffix yields the
   same decoded string (the parser is prefix-deterministic up to the closing
   quote). *)
Lemma parse_string_chars_fast_reparse_gen (body rest1 rest2 : list ascii) (str : list ascii) :
  parse_string_chars_fast (body ++ "034"%char :: rest1) = Some (str, rest1) ->
  parse_string_chars_fast (body ++ "034"%char :: rest2) = Some (str, rest2).
Proof.
  revert body rest1 rest2 str.
  apply (well_founded_induction wf_lt_length
    (fun body : list ascii => forall rest1 rest2 str : list ascii,
      parse_string_chars_fast (body ++ "034"%char :: rest1) = Some (str, rest1) ->
      parse_string_chars_fast (body ++ "034"%char :: rest2) = Some (str, rest2))).
  intros body IH rest1 rest2 str H.
  destruct body as [| c body'].
  - (* body = [] *)
    cbn [app] in H. cbn [app parse_string_chars_fast Ascii.eqb] in H.
    injection H as Hs. subst str.
    cbn [app parse_string_chars_fast Ascii.eqb]. reflexivity.
  - (* body = c :: body' *)
    cbn [app] in H.
    destruct (Ascii.eqb_spec c "034"%char) as [Hq | Hq].
    + (* c is the closing quote: impossible *)
      subst c. cbn [parse_string_chars_fast Ascii.eqb] in H.
      injection H as _ Hr.
      apply (f_equal (@List.length ascii)) in Hr.
      rewrite List.length_app in Hr. cbn in Hr. lia.
    + destruct (Ascii.eqb_spec c "092"%char) as [Hb | Hb].
      * (* c is a backslash *)
        subst c. destruct body' as [| e body''].
        -- (* backslash escapes the trailing quote: impossible *)
           cbn [app parse_string_chars_fast Ascii.eqb] in H.
           destruct (parse_string_chars_fast rest1) as [[cs' rest'] |] eqn:Ecs;
             cbn [string_cons] in H.
           ++ injection H as _ Hr. subst rest'.
              destruct (parse_string_chars_fast_shape rest1 cs' rest1 Ecs) as [raw' Hraw'].
              apply (f_equal (@List.length ascii)) in Hraw'.
              rewrite List.length_app in Hraw'. cbn in Hraw'. lia.
           ++ discriminate.
        -- cbn [app] in H. destruct (Ascii.eqb_spec e "u"%char) as [Hu | Hu].
           ** (* \u escape *)
              subst e.
              destruct body'' as [| ha body3].
              --- cbn [app] in H. rewrite (parse_string_chars_fast_short0 rest1) in H. discriminate.
              --- destruct body3 as [| hb body4].
                  +++ cbn [app] in H. rewrite (parse_string_chars_fast_short1 ha rest1) in H. discriminate.
                  +++ destruct body4 as [| hc body5].
                      ++++ cbn [app] in H. rewrite (parse_string_chars_fast_short2 ha hb rest1) in H. discriminate.
                      ++++ destruct body5 as [| hd body'''].
                           +++++ cbn [app] in H. rewrite (parse_string_chars_fast_short3 ha hb hc rest1) in H. discriminate.
                           +++++ (* 4 hex digits present *)
                                cbn [app] in H.
                                destruct (is_hexb ha && is_hexb hb && is_hexb hc && is_hexb hd) eqn:Ehex.
                                ------
                                  (* valid \uXXXX *)
                                  rewrite (parse_string_chars_fast_u ha hb hc hd (body''' ++ "034"%char :: rest1) Ehex) in H.
                                  cbn [string_cons] in H.
                                  destruct (parse_string_chars_fast (body''' ++ "034"%char :: rest1)) as [[cs' rest'] |] eqn:Ecs.
                                  ++++++++ injection H as Hs Hr. subst str rest'.
                                           pose proof (IH body''' ltac:(cbn; lia) rest1 rest2 cs' Ecs) as Hih.
                                           cbn [app].
                                           rewrite (parse_string_chars_fast_u ha hb hc hd (body''' ++ "034"%char :: rest2) Ehex).
                                           cbn [string_cons]. rewrite Hih. cbn. reflexivity.
                                  ++++++++ discriminate.
                                ------
                                  (* invalid \uXXXX: None *)
                                  rewrite (parse_string_chars_fast_u_none ha hb hc hd (body''' ++ "034"%char :: rest1) Ehex) in H.
                                  discriminate.
           ** (* non-\u escape *)
              destruct (is_escape_char e) eqn:Eesc.
              --- rewrite (parse_string_chars_fast_escape_det e (body'' ++ "034"%char :: rest1) Eesc) in H.
                  cbn [string_cons] in H.
                  destruct (parse_string_chars_fast (body'' ++ "034"%char :: rest1)) as [[cs' rest'] |] eqn:Ecs.
                  +++ injection H as Hs Hr. subst str rest'.
                      pose proof (IH body'' ltac:(cbn; lia) rest1 rest2 cs' Ecs) as Hih.
                      cbn [app]. rewrite (parse_string_chars_fast_escape_det e (body'' ++ "034"%char :: rest2) Eesc).
                      cbn [string_cons]. rewrite Hih. cbn. reflexivity.
                  +++ discriminate.
              --- rewrite (parse_string_chars_fast_invalid_escape e (body'' ++ "034"%char :: rest1) Eesc (proj2 (Ascii.eqb_neq e "u"%char) Hu)) in H.
                  discriminate.
      * (* regular char *)
        rewrite (parse_string_chars_fast_char c (body' ++ "034"%char :: rest1)
                  (proj2 (Ascii.eqb_neq c "034"%char) Hq) (proj2 (Ascii.eqb_neq c "092"%char) Hb)) in H.
        destruct (parse_string_chars_fast (body' ++ "034"%char :: rest1)) as [[cs' rest'] |] eqn:Ecs.
        -- injection H as Hs Hr. subst str rest'.
           pose proof (IH body' ltac:(cbn; lia) rest1 rest2 cs' Ecs) as Hih.
           cbn [app].
           rewrite (parse_string_chars_fast_char c (body' ++ "034"%char :: rest2)
                     (proj2 (Ascii.eqb_neq c "034"%char) Hq) (proj2 (Ascii.eqb_neq c "092"%char) Hb)).
           rewrite Hih. reflexivity.
        -- discriminate.
Qed.

Lemma parse_string_chars_fast_reparse (body rest : list ascii) (str : list ascii) :
  parse_string_chars_fast (body ++ "034"%char :: rest) = Some (str, rest) ->
  parse_string_chars_fast (body ++ "034"%char :: nil) = Some (str, []).
Proof.
  intros H. exact (parse_string_chars_fast_reparse_gen body rest nil str H).
Qed.



Lemma skipn_cons_inv (l : list ascii) (i : nat) (c : ascii) (w' : list ascii) :
  skipn i l = c :: w' -> nth_error l i = Some c /\ w' = skipn (S i) l.
Proof.
  revert l w'. induction i as [| i' IH]; intros l w' H.
  - cbn [skipn] in H. destruct l as [| a l']; [discriminate |].
    injection H as Hc Hw. subst a w'.
    split; [cbn; reflexivity | cbn; reflexivity].
  - cbn [skipn] in H. destruct l as [| a l']; [discriminate |].
    destruct (IH l' w' H) as [Hnth Hw].
    split; [exact Hnth | cbn; exact Hw].
Qed.

Lemma skipn_app_one (A : Type) (raw X : list A) (a : A) :
  skipn (List.length raw + 1) (raw ++ a :: X) = X.
Proof.
  induction raw as [| x raw IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

Lemma reparse_span_len (l : list ascii) (i len : nat) (raw : list ascii) :
  skipn i l = raw ++ "034"%char :: skipn (i + len + 1) l ->
  List.length raw <= len.
Proof.
  intros H.
  assert (Hb : List.length raw + 1 + i <= List.length l).
  { pose proof (f_equal (@List.length ascii) H) as Hlen.
    rewrite List.length_app in Hlen. cbn in Hlen.
    rewrite !List.length_skipn in Hlen. lia. }
  apply (f_equal (fun x : list ascii => skipn (List.length raw + 1) x)) in H.
  rewrite skipn_skipn in H.
  rewrite (skipn_app_one ascii raw (skipn (i + len + 1) l) "034"%char) in H.
  apply (f_equal (@List.length ascii)) in H.
  rewrite !List.length_skipn in H.
  lia.
Qed.

(* decode_string re-parses the exact span and yields the same decoded string. *)


Definition decode_member (buf : buffer) (m : nat * nat * Json_fast) : list ascii * Json :=
  match m with (ks, kl, v) => (decode_string buf ks kl, decode buf v) end.

Lemma skip_ws_fast_sim (l : list ascii) (i : nat) :
  skipn (skip_ws_fast (Buf l) i) l = skip_ws (skipn i l).
Proof.
  unfold skip_ws_fast, buffer_length.
  apply skip_ws_loop_sim. rewrite List.length_skipn. lia.
Qed.





(* Re-parsing the span with a prefix of the closing-quote suffix yields the
   same string (the decode_string `match Some (s, _) => s` ignores the rest). *)
Lemma parse_string_chars_fast_reparse_prefix (raw rest : list ascii) (k : nat) (str : list ascii) :
  parse_string_chars_fast (raw ++ "034"%char :: rest) = Some (str, rest) ->
  exists rest', parse_string_chars_fast (raw ++ firstn k ("034"%char :: rest) ++ "034"%char :: nil) = Some (str, rest').
Proof.
  intros H.
  destruct k as [| k'].
  - exists []. cbn [firstn]. exact (parse_string_chars_fast_reparse raw rest str H).
  - exists (firstn k' rest ++ "034"%char :: nil).
    cbn [firstn].
    change (parse_string_chars_fast (raw ++ "034"%char :: (firstn k' rest ++ "034"%char :: nil)) = Some (str, firstn k' rest ++ "034"%char :: nil)).
    rewrite (parse_string_chars_fast_reparse_gen raw rest (firstn k' rest ++ "034"%char :: nil) str H).
    reflexivity.
Qed.

Lemma decode_string_correct (l : list ascii) (i len : nat) (str : list ascii) :
  parse_string (skipn i l) = Some (str, skipn (S i + len + 1) l) ->
  decode_string (Buf l) (S i) len = str.
Proof.
  intros H.
  unfold decode_string, span_to_list, buffer_to_list.
  unfold parse_string in H.
  destruct (nth_error l i) as [c |] eqn:Ei.
  - rewrite (skipn_cons_head ascii l i c Ei) in H.
    cbn [parse_string] in H.
    destruct (Ascii.eqb c "034"%char) eqn:Equote; [| cbn in H; discriminate].
    cbn [parse_string] in H.
    pose proof (parse_string_chars_fast_shape (skipn (S i) l) str (skipn (S i + len + 1) l) H) as Hshape.
    destruct Hshape as [raw Hraw].
    pose proof (reparse_span_len l (S i) len raw Hraw) as Hle.
    rewrite Hraw.
    rewrite (firstn_app_le ascii raw ("034"%char :: skipn (S i + len + 1) l) len) by (exact Hle).
    rewrite Hraw in H.
    destruct (parse_string_chars_fast_reparse_prefix raw (skipn (S i + len + 1) l) (len - List.length raw) str H) as [rest' Hre].
    cbn [parse_string]. rewrite (Ascii.eqb_refl "034"%char). cbn [parse_string].
    rewrite <- (app_assoc raw (firstn (len - List.length raw) ("034"%char :: skipn (S i + len + 1) l)) ("034"%char :: nil)). rewrite Hre. cbn. reflexivity.
  - rewrite (nth_error_none_skipn ascii l i Ei) in H. cbn in H. discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* Mutual simulation: the fast tokenizer refines the certified parser.        *)
(* ------------------------------------------------------------------------- *)

Transparent skip_digits_fast.

(* nth_error l i = Some c implies i is a valid (strictly in-bounds) index. *)
Lemma nth_error_lt_len (A : Type) (l : list A) (i : nat) (c : A) :
  nth_error l i = Some c -> i < List.length l.
Proof.
  intros H. apply nth_error_Some. intro Hn. rewrite H in Hn. congruence.
Qed.

(* Indices returned by the leaf scanners are bounded by the buffer length. *)

Lemma skip_ws_loop_le (l : list ascii) (fuel i : nat) :
  i <= List.length l -> skip_ws_loop (Buf l) fuel i <= List.length l.
Proof.
  revert i. induction fuel as [| f' IH]; intros i Hi; cbn [skip_ws_loop buffer_get].
  - exact Hi.
  - destruct (nth_error l i) as [c |] eqn:En.
    + destruct (is_wsb c); [| exact Hi].
      apply IH. apply nth_error_lt_len in En. lia.
    + apply nth_error_None in En. lia.
Qed.

Lemma skip_ws_fast_le (l : list ascii) (i : nat) :
  i <= List.length l -> skip_ws_fast (Buf l) i <= List.length l.
Proof.
  intros Hi. unfold skip_ws_fast, buffer_length. apply skip_ws_loop_le. exact Hi.
Qed.

Lemma skip_digits_loop_le (l : list ascii) (fuel i : nat) :
  i <= List.length l -> skip_digits_loop (Buf l) fuel i <= List.length l.
Proof.
  revert i. induction fuel as [| f' IH]; intros i Hi; cbn [skip_digits_loop buffer_get].
  - exact Hi.
  - destruct (nth_error l i) as [c |] eqn:En.
    + destruct (is_digitb c); [| exact Hi].
      apply IH. apply nth_error_lt_len in En. lia.
    + apply nth_error_None in En. lia.
Qed.

Lemma skip_digits_fast_le (l : list ascii) (i : nat) :
  i <= List.length l -> skip_digits_fast (Buf l) i <= List.length l.
Proof.
  intros Hi. unfold skip_digits_fast, buffer_length. apply skip_digits_loop_le. exact Hi.
Qed.

Opaque skip_ws_fast skip_digits_fast.

(* find_string_end_loop returns Some j only at a closing quote, hence j < len. *)
Lemma find_string_end_loop_some_quote (l : list ascii) (fuel i j : nat) :
  find_string_end_loop (Buf l) fuel i = Some j -> nth_error l j = Some "034"%char.
Proof.
  revert i j. induction fuel as [| f' IH]; intros i j H; cbn [find_string_end_loop buffer_get] in H.
  - congruence.
  - destruct (nth_error l i) as [c |] eqn:En.
    + destruct (Ascii.eqb c "034"%char) eqn:Eq.
      * cbn [find_string_end_loop] in H. injection H as Hj. subst j.
        apply (Ascii.eqb_eq c "034"%char) in Eq. subst c. exact En.
      * destruct (Ascii.eqb c "092"%char) eqn:Ebs.
        -- cbn [find_string_end_loop] in H.
           destruct (nth_error l (S i)) as [e |] eqn:En2.
           ** destruct (Ascii.eqb e "u"%char) eqn:Eu.
              --- cbn [find_string_end_loop] in H.
                  destruct (parse_u_escape_fast (Buf l) i) eqn:Epu.
                  +++ destruct (find_string_end_loop (Buf l) f' (i + 6)) as [j' |] eqn:Efj; [| congruence].
                      injection H as Hj. subst j. exact (IH (i + 6) j' Efj).
                  +++ congruence.
              --- destruct (is_escape_char e) eqn:Eesc.
                  +++ destruct (find_string_end_loop (Buf l) f' (i + 2)) as [j' |] eqn:Efj; [| congruence].
                      injection H as Hj. subst j. exact (IH (i + 2) j' Efj).
                  +++ congruence.
           ** congruence.
        -- cbn [find_string_end_loop] in H.
           destruct (find_string_end_loop (Buf l) f' (S i)) as [j' |] eqn:Efj; [| congruence].
           injection H as Hj. subst j. exact (IH (S i) j' Efj).
    + cbn [find_string_end_loop] in H. congruence.
Qed.

Lemma parse_string_fast_le (l : list ascii) (i : nat) (v : Json_fast) (j : nat) :
  parse_string_fast (Buf l) i = Some (v, j) -> j <= List.length l.
Proof.
  intros H. unfold parse_string_fast, find_string_end, buffer_length in H.
  destruct (find_string_end_loop (Buf l) (List.length l) (S i)) as [endq |] eqn:Efj; [| congruence].
  injection H as Hv Hj. subst v j.
  pose proof (find_string_end_loop_some_quote l (List.length l) (S i) endq Efj) as Hq.
  apply nth_error_lt_len in Hq. lia.
Qed.

Lemma parse_lit_fast_le (l : list ascii) (s : string) (i : nat) (v v' : Json_fast) (j : nat) :
  i <= List.length l -> parse_lit_fast (Buf l) s i v = Some (v', j) -> j <= List.length l.
Proof.
  revert i v v' j. induction s as [| c s' IH]; intros i v v' j Hi H.
  - cbn [parse_lit_fast] in H. injection H as Hv' Hj. subst v' j. exact Hi.
  - cbn [parse_lit_fast] in H. unfold buf_eq_char, buffer_get in H.
    destruct (nth_error l i) as [c' |] eqn:En.
    + destruct (Ascii.eqb c c') eqn:Eeq; [| congruence].
      apply (IH (S i) v v' j).
      * apply nth_error_lt_len in En. lia.
      * exact H.
    + congruence.
Qed.

Lemma parse_exp_fast_le (l : list ascii) (i j : nat) :
  i <= List.length l -> parse_exp_fast (Buf l) i = Some j -> j <= List.length l.
Proof.
  intros Hi H.
  unfold parse_exp_fast, buffer_get in H.
  destruct (nth_error l i) as [c |] eqn:Ei.
  - destruct (is_expb c) eqn:Ee.
    + remember (buf_eq_char (Buf l) (S i) "+"%char) as b1 eqn:Eb1.
      remember (buf_eq_char (Buf l) (S i) "-"%char) as b2 eqn:Eb2.
      destruct b1.
      * cbn [orb] in H.
        destruct (nth_error l (S (S i))) as [d |] eqn:Ed.
        -- destruct (is_digitb d) eqn:Edig.
           ++ cbn in H. injection H as Hj. subst j.
              apply skip_digits_fast_le. apply nth_error_lt_len in Ed. lia.
           ++ injection H as Hj. subst j. exact Hi.
        -- injection H as Hj. subst j. exact Hi.
      * destruct b2.
        -- cbn [orb] in H.
           destruct (nth_error l (S (S i))) as [d |] eqn:Ed.
           ++ destruct (is_digitb d) eqn:Edig.
              ** cbn in H. injection H as Hj. subst j.
                 apply skip_digits_fast_le. apply nth_error_lt_len in Ed. lia.
              ** injection H as Hj. subst j. exact Hi.
           ++ injection H as Hj. subst j. exact Hi.
        -- cbn [orb] in H.
           destruct (nth_error l (S i)) as [d |] eqn:Ed.
           ++ destruct (is_digitb d) eqn:Edig.
              ** cbn in H. injection H as Hj. subst j.
                 apply skip_digits_fast_le. apply nth_error_lt_len in Ed. lia.
              ** injection H as Hj. subst j. exact Hi.
           ++ injection H as Hj. subst j. exact Hi.
    + injection H as Hj. subst j. exact Hi.
  - injection H as Hj. subst j. exact Hi.
Qed.

Lemma parse_frac_exp_fast_le (l : list ascii) (i j : nat) :
  i <= List.length l -> parse_frac_exp_fast (Buf l) i = Some j -> j <= List.length l.
Proof.
  intros Hi H.
  cbv [parse_frac_exp_fast] in H.
  set (i1 := if buf_eq_char (Buf l) i "."%char then
      match buffer_get (Buf l) (S i) with Some c => if is_digitb c then skip_digits_fast (Buf l) (S i) else i | None => i end
    else i) in H.
  apply (parse_exp_fast_le l i1 j).
  - subst i1. unfold buf_eq_char, buffer_get.
    destruct (nth_error l i) as [c |] eqn:Ei.
    + destruct (Ascii.eqb "."%char c) eqn:Edot.
      * destruct (nth_error l (S i)) as [d |] eqn:Ed.
        -- destruct (is_digitb d) eqn:Edig.
           ++ apply skip_digits_fast_le. apply nth_error_lt_len in Ed. lia.
           ++ exact Hi.
        -- exact Hi.
      * exact Hi.
    + exact Hi.
  - exact H.
Qed.

Lemma parse_number_fast_le (l : list ascii) (i : nat) (v : Json_fast) (j : nat) :
  i <= List.length l -> parse_number_fast (Buf l) i = Some (v, j) -> j <= List.length l.
Proof.
  intros Hi H.
  cbv [parse_number_fast] in H.
  set (i1 := if buf_eq_char (Buf l) i "-"%char then S i else i) in H.
  destruct (buffer_get (Buf l) i1) as [d |] eqn:Ed.
  - destruct (Ascii.eqb d "0"%char) eqn:Ez.
    + destruct (parse_frac_exp_fast (Buf l) (S i1)) as [i2 |] eqn:Efe.
      * cbn in H. injection H as Hv Hj. subst v j.
        apply (parse_frac_exp_fast_le l (S i1) i2).
        -- unfold buffer_get in Ed. apply nth_error_lt_len in Ed. lia.
        -- exact Efe.
      * cbn in H. congruence.
    + destruct (is_digit1_9b d) eqn:E19.
      * destruct (parse_frac_exp_fast (Buf l) (skip_digits_fast (Buf l) (S i1))) as [i2 |] eqn:Efe.
        -- cbn in H. injection H as Hv Hj. subst v j.
           apply (parse_frac_exp_fast_le l (skip_digits_fast (Buf l) (S i1)) i2).
           ++ apply skip_digits_fast_le. unfold buffer_get in Ed. apply nth_error_lt_len in Ed. lia.
           ++ exact Efe.
        -- cbn in H. congruence.
      * cbn in H. congruence.
  - cbn in H. congruence.
Qed.

(* Rewriting the tokenizer's literal match patterns into Ascii.eqb tests. *)
Transparent Ascii.eqb.

Lemma match_ascii_comma_close (c : ascii) (A : Type) (a b d : A) :
  match c with ","%char => a | "]"%char => b | _ => d end =
  if Ascii.eqb c ","%char then a else if Ascii.eqb c "]"%char then b else d.
Proof.
  destruct (Ascii.eqb_spec c ","%char) as [Hc | Hc].
  - subst c. reflexivity.
  - destruct (Ascii.eqb_spec c "]"%char) as [Hc' | Hc'].
    + subst c. reflexivity.
    + destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn.
      all: try reflexivity.
      all: (exfalso; apply Hc; reflexivity) || (exfalso; apply Hc'; reflexivity).
Qed.

Lemma match_ascii_comma_brace (c : ascii) (A : Type) (a b d : A) :
  match c with ","%char => a | "}"%char => b | _ => d end =
  if Ascii.eqb c ","%char then a else if Ascii.eqb c "}"%char then b else d.
Proof.
  destruct (Ascii.eqb_spec c ","%char) as [Hc | Hc].
  - subst c. reflexivity.
  - destruct (Ascii.eqb_spec c "}"%char) as [Hc' | Hc'].
    + subst c. reflexivity.
    + destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn.
      all: try reflexivity.
      all: (exfalso; apply Hc; reflexivity) || (exfalso; apply Hc'; reflexivity).
Qed.

Opaque Ascii.eqb.

(* parse_string_fast always returns a JStr_f span. *)
Lemma parse_string_fast_shape (l : list ascii) (i : nat) (v : Json_fast) (j : nat) :
  parse_string_fast (Buf l) i = Some (v, j) -> exists k kl, v = JStr_f k kl.
Proof.
  intros H. unfold parse_string_fast, find_string_end, buffer_length in H.
  destruct (find_string_end_loop (Buf l) (List.length l) (S i)) as [endq |] eqn:Efj; [| congruence].
  injection H as Hv Hj. subst v j. eexists; eexists; reflexivity.
Qed.

(* buf_eq_char = true means the char at i is exactly c. *)
Lemma buf_eq_char_true (l : list ascii) (i : nat) (c : ascii) :
  buf_eq_char (Buf l) i c = true -> nth_error l i = Some c.
Proof.
  intros H. rewrite buf_eq_char_sym in H.
  destruct (nth_error l i) as [c' |] eqn:En; [| congruence].
  apply Ascii.eqb_eq in H. subst c'. reflexivity.
Qed.

(* The five mutually-recursive tokenizer functions never return an index past
   the buffer end. *)
Lemma parse_fast_bound (fuel : nat) :
  (forall l i v j, i <= List.length l -> parse_value_fast (Buf l) fuel i = Some (v, j) -> j <= List.length l) /\
  (forall l i v j, S i <= List.length l -> parse_array_fast (Buf l) fuel i = Some (v, j) -> j <= List.length l) /\
  (forall l i vs j, i <= List.length l -> parse_array_elems_fast (Buf l) fuel i = Some (vs, j) -> j <= List.length l) /\
  (forall l i v j, S i <= List.length l -> parse_object_fast (Buf l) fuel i = Some (v, j) -> j <= List.length l) /\
  (forall l i ms j, i <= List.length l -> parse_object_members_fast (Buf l) fuel i = Some (ms, j) -> j <= List.length l).
Proof.
  induction fuel as [| fuel' IH].
  - repeat split; intros l i v j Hi H; cbn in H; congruence.
  - destruct IH as [BV [BA [BAE [BO BOM]]]].
    repeat split.
    + (* value *)
      intros l i v j Hi H.
      cbn [parse_value_fast buffer_get] in H.
      destruct (nth_error l (skip_ws_fast (Buf l) i)) as [c |] eqn:Ei0.
      * destruct (Ascii.eqb c "{"%char) eqn:E1.
        -- apply (BO l (skip_ws_fast (Buf l) i) v j).
           apply nth_error_lt_len in Ei0. lia.
           exact H.
        -- destruct (Ascii.eqb c "["%char) eqn:E2.
           ++ apply (BA l (skip_ws_fast (Buf l) i) v j).
              apply nth_error_lt_len in Ei0. lia.
              exact H.
           ++ destruct (Ascii.eqb c "034"%char) eqn:E3.
              ** apply (parse_string_fast_le l (skip_ws_fast (Buf l) i) v j). exact H.
              ** destruct (Ascii.eqb c "t"%char) eqn:E4.
                 --- apply (parse_lit_fast_le l "rue"%string (S (skip_ws_fast (Buf l) i)) (JBool_f true) v j).
                     +++ apply nth_error_lt_len in Ei0. lia.
                     +++ exact H.
                 --- destruct (Ascii.eqb c "f"%char) eqn:E5.
                     +++ apply (parse_lit_fast_le l "alse"%string (S (skip_ws_fast (Buf l) i)) (JBool_f false) v j).
                         *** apply nth_error_lt_len in Ei0. lia.
                         *** exact H.
                     +++ destruct (Ascii.eqb c "n"%char) eqn:E6.
                         *** apply (parse_lit_fast_le l "ull"%string (S (skip_ws_fast (Buf l) i)) JNull_f v j).
                             **** apply nth_error_lt_len in Ei0. lia.
                             **** exact H.
                         *** destruct (Ascii.eqb c "-"%char) eqn:E7; destruct (is_digitb c) eqn:E8; cbn [orb] in H.
                             **** apply (parse_number_fast_le l (skip_ws_fast (Buf l) i) v j).
                                  +++++ apply skip_ws_fast_le. exact Hi.
                                  +++++ exact H.
                             **** apply (parse_number_fast_le l (skip_ws_fast (Buf l) i) v j).
                                  +++++ apply skip_ws_fast_le. exact Hi.
                                  +++++ exact H.
                             **** apply (parse_number_fast_le l (skip_ws_fast (Buf l) i) v j).
                                  +++++ apply skip_ws_fast_le. exact Hi.
                                  +++++ exact H.
                             **** congruence.
      * congruence.
    + (* array *)
      intros l i v j Hi H.
      cbn [parse_array_fast buffer_get] in H.
      destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) (S i)) "]"%char) eqn:Ecl.
      * cbn in H. destruct fuel' as [| fuel''].
        -- congruence.
        -- injection H as Hv Hj. subst v j.
           apply buf_eq_char_true in Ecl. apply nth_error_lt_len in Ecl. lia.
      * cbn in H.
        destruct (parse_array_elems_fast (Buf l) fuel' (skip_ws_fast (Buf l) (S i))) as [[vs i2] |] eqn:Eae; [| cbn in H; congruence].
        injection H as Hv Hj. subst v j.
        apply (BAE l (skip_ws_fast (Buf l) (S i)) vs i2).
        -- apply skip_ws_fast_le. exact Hi.
        -- exact Eae.
    + (* elems *)
      intros l i vs j Hi H.
      cbn [parse_array_elems_fast buffer_get] in H.
      destruct (parse_value_fast (Buf l) fuel' i) as [[v i2] |] eqn:Ev; [| cbn in H; congruence].
      destruct (nth_error l (skip_ws_fast (Buf l) i2)) as [c |] eqn:Ei3; [| cbn in H; congruence].
      * cbn in H.
        rewrite match_ascii_comma_close in H.
        destruct (Ascii.eqb c ","%char) eqn:Ecomma.
        -- cbn in H.
           destruct (parse_array_elems_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i2))) as [[vs' i4] |] eqn:Eae; [| cbn in H; congruence].
           injection H as Hvs Hj. subst vs j.
           apply (BAE l (S (skip_ws_fast (Buf l) i2)) vs' i4).
           ++ apply nth_error_lt_len in Ei3. lia.
           ++ exact Eae.
        -- destruct (Ascii.eqb c "]"%char) eqn:Ecl.
           ++ cbn in H. injection H as Hvs Hj. subst vs j.
              apply nth_error_lt_len in Ei3. lia.
           ++ cbn in H. congruence.
    + (* object *)
      intros l i v j Hi H.
      cbn [parse_object_fast buffer_get] in H.
      destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) (S i)) "}"%char) eqn:Ecl.
      * cbn in H. destruct fuel' as [| fuel''].
        -- congruence.
        -- injection H as Hv Hj. subst v j.
           apply buf_eq_char_true in Ecl. apply nth_error_lt_len in Ecl. lia.
      * cbn in H.
        destruct (parse_object_members_fast (Buf l) fuel' (skip_ws_fast (Buf l) (S i))) as [[ms i2] |] eqn:Eom; [| cbn in H; congruence].
        injection H as Hv Hj. subst v j.
        apply (BOM l (skip_ws_fast (Buf l) (S i)) ms i2).
        -- apply skip_ws_fast_le. exact Hi.
        -- exact Eom.
    + (* members *)
      intros l i ms j Hi H.
      cbn [parse_object_members_fast buffer_get] in H.
      destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) i) "034"%char) eqn:Eq.
      * cbn in H.
        destruct (parse_string_fast (Buf l) (skip_ws_fast (Buf l) i)) as [[v i2] |] eqn:Es; [| cbn in H; congruence].
        pose proof (parse_string_fast_shape l (skip_ws_fast (Buf l) i) v i2 Es) as [k [kl Hv]].
        subst v. cbn in H.
        destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) i2) ":"%char) eqn:Ecolon.
        -- cbn in H.
           destruct (parse_value_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i2))) as [[v2 i4] |] eqn:Ev; [| cbn in H; congruence].
           cbn in H.
           destruct (nth_error l (skip_ws_fast (Buf l) i4)) as [c3 |] eqn:Ei5; [| cbn in H; congruence].
           ++ rewrite match_ascii_comma_brace in H.
              destruct (Ascii.eqb c3 ","%char) eqn:Ecomma.
              ** cbn in H.
                 destruct (parse_object_members_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i4))) as [[ms' i6] |] eqn:Eom; [| cbn in H; congruence].
                 injection H as Hms Hj. subst ms j.
                 apply (BOM l (S (skip_ws_fast (Buf l) i4)) ms' i6).
                 --- apply nth_error_lt_len in Ei5. lia.
                 --- exact Eom.
              ** destruct (Ascii.eqb c3 "}"%char) eqn:Ecl.
                 --- cbn in H. injection H as Hms Hj. subst ms j.
                     apply nth_error_lt_len in Ei5. lia.
                 --- cbn in H. congruence.
        -- cbn in H. congruence.
      * cbn in H. congruence.
Qed.

(* skip_ws_fast is idempotent at any already-skipped position. *)
Lemma skip_ws_fast_idem (l : list ascii) (i : nat) :
  i <= List.length l ->
  skip_ws_fast (Buf l) (skip_ws_fast (Buf l) i) = skip_ws_fast (Buf l) i.
Proof.
  intros Hi.
  pose proof (skip_ws_fast_sim l i) as H1.
  pose proof (skip_ws_fast_sim l (skip_ws_fast (Buf l) i)) as H2.
  rewrite H1 in H2.
  rewrite (skip_ws_idem (skipn i l)) in H2.
  rewrite <- H1 in H2.
  apply (skipn_inj l (skip_ws_fast (Buf l) (skip_ws_fast (Buf l) i)) (skip_ws_fast (Buf l) i)).
  - apply skip_ws_fast_le. apply skip_ws_fast_le. exact Hi.
  - apply skip_ws_fast_le. exact Hi.
  - exact H2.
Qed.

(* parse_string_fast's span decodes to the same string. *)
Lemma parse_string_fast_decode (l : list ascii) (i endq : nat) :
  find_string_end (Buf l) (S i) = Some endq ->
  nth_error l i = Some "034"%char ->
  parse_string (skipn i l) = Some (decode_string (Buf l) (S i) (endq - S i), skipn (S endq) l).
Proof.
  intros Efj Ei.
  assert (Hlen : List.length (skipn (S i) l) <= List.length l) by (rewrite List.length_skipn; lia).
  pose proof (find_string_end_loop_sim l (List.length l) (S i) Hlen) as Hfs.
  unfold find_string_end, buffer_length in Efj.
  rewrite Efj in Hfs.
  destruct Hfs as [cs Hcs].
  pose proof (parse_string_chars_fast_progress l (S i) (S endq) cs Hcs) as Hprog.
  assert (Hle : S i <= endq) by lia.
  pose proof (parse_string_fast_span l i Ei) as Hs.
  unfold parse_string_fast, find_string_end, buffer_length in Hs.
  rewrite Efj in Hs.
  destruct Hs as [s Hsp].
  assert (Hdec : decode_string (Buf l) (S i) (endq - S i) = s).
  { apply (decode_string_correct l i (endq - S i) s).
    assert (Hidx : S i + (endq - S i) + 1 = S endq) by lia.
    rewrite Hsp. rewrite Hidx. reflexivity. }
  rewrite Hdec. exact Hsp.
Qed.

(* ------------------------------------------------------------------------- *)
(* Mutual simulation: tokenizer refines the certified parser.                 *)
(* ------------------------------------------------------------------------- *)

Lemma parse_number_fast_shape (l : list ascii) (i j : nat) (v : Json_fast) :
  parse_number_fast (Buf l) i = Some (v, j) -> v = JNum_f i (j - i).
Proof.
  intros H. unfold parse_number_fast in H.
  set (i1 := if buf_eq_char (Buf l) i "-"%char then S i else i) in H.
  destruct (buffer_get (Buf l) i1) as [d |] eqn:Ed; [| cbn in H; congruence].
  destruct (Ascii.eqb d "0"%char) eqn:Ez.
  - cbn in H.
    destruct (parse_frac_exp_fast (Buf l) (S i1)) as [i2 |] eqn:Efe; [| cbn in H; congruence].
    injection H as Hv Hj. subst v j. reflexivity.
  - destruct (is_digit1_9b d) eqn:E19.
    + cbn in H.
      destruct (parse_frac_exp_fast (Buf l) (skip_digits_fast (Buf l) (S i1))) as [i2 |] eqn:Efe; [| cbn in H; congruence].
      injection H as Hv Hj. subst v j. reflexivity.
    + cbn in H. congruence.
Qed.

Lemma parse_array_fast_shape (l : list ascii) (fuel i : nat) (v : Json_fast) (j : nat) :
  parse_array_fast (Buf l) fuel i = Some (v, j) -> exists vs, v = JArr_f vs.
Proof.
  intros H. destruct fuel as [| fuel'].
  - cbn [parse_array_fast] in H. congruence.
  - cbn [parse_array_fast] in H.
    destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) (S i)) "]"%char) eqn:Ecl.
    + destruct fuel' as [| fuel''].
      ++ congruence.
      ++ injection H as Hv Hj. subst v j. eexists. reflexivity.
    + destruct (parse_array_elems_fast (Buf l) fuel' (skip_ws_fast (Buf l) (S i))) as [[vs i2] |] eqn:Eae; [| congruence].
      injection H as Hv Hj. subst v j. eexists. reflexivity.
Qed.

Lemma parse_object_fast_shape (l : list ascii) (fuel i : nat) (v : Json_fast) (j : nat) :
  parse_object_fast (Buf l) fuel i = Some (v, j) -> exists ms, v = JObj_f ms.
Proof.
  intros H. destruct fuel as [| fuel'].
  - cbn [parse_object_fast] in H. congruence.
  - cbn [parse_object_fast] in H.
    destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) (S i)) "}"%char) eqn:Ecl.
    + destruct fuel' as [| fuel''].
      ++ congruence.
      ++ injection H as Hv Hj. subst v j. eexists. reflexivity.
    + destruct (parse_object_members_fast (Buf l) fuel' (skip_ws_fast (Buf l) (S i))) as [[ms i2] |] eqn:Eom; [| congruence].
      injection H as Hv Hj. subst v j. eexists. reflexivity.
Qed.

Lemma buf_eq_char_from_eqb (l : list ascii) (i : nat) (c x : ascii) :
  nth_error l i = Some c -> Ascii.eqb c x = true -> buf_eq_char (Buf l) i x = true.
Proof.
  intros En Eeq. rewrite buf_eq_char_sym. rewrite En. exact Eeq.
Qed.

Lemma skip_ws_fast_skip_ws_idem (l : list ascii) (i : nat) :
  skip_ws (skipn (skip_ws_fast (Buf l) i) l) = skipn (skip_ws_fast (Buf l) i) l.
Proof.
  rewrite (skip_ws_fast_sim l i). rewrite (skip_ws_idem (skipn i l)). rewrite <- (skip_ws_fast_sim l i). reflexivity.
Qed.


Transparent parse_string.

Definition sim_value_stmt (fuel : nat) : Prop :=
  forall (l : list ascii) (i : nat),
  match parse_value_fast (Buf l) fuel i with
  | Some (v, j) => parse_value fuel (skip_ws (skipn i l)) = Some (decode (Buf l) v, skipn j l)
  | None => parse_value fuel (skip_ws (skipn i l)) = None
  end.

Definition sim_array_stmt (fuel : nat) : Prop :=
  forall (l : list ascii) (i : nat),
  S i <= List.length l ->
  match parse_array_fast (Buf l) fuel i with
  | Some (JArr_f vs, j) => parse_array fuel (skipn (S i) l) = Some (map (decode (Buf l)) vs, skipn j l)
  | _ => parse_array fuel (skipn (S i) l) = None
  end.

Definition sim_object_stmt (fuel : nat) : Prop :=
  forall (l : list ascii) (i : nat),
  S i <= List.length l ->
  match parse_object_fast (Buf l) fuel i with
  | Some (JObj_f ms, j) => parse_object fuel (skipn (S i) l) = Some (map (decode_member (Buf l)) ms, skipn j l)
  | _ => parse_object fuel (skipn (S i) l) = None
  end.

Definition sim_elems_stmt (fuel : nat) : Prop :=
  forall (l : list ascii) (i : nat),
  buf_eq_char (Buf l) (skip_ws_fast (Buf l) i) "]"%char = false ->
  match parse_array_elems_fast (Buf l) fuel i with
  | Some (vs, j) => parse_elements fuel (skip_ws (skipn i l)) = Some (map (decode (Buf l)) vs, "]"%char :: skipn j l)
  | None => parse_elements fuel (skip_ws (skipn i l)) = None
  end.

Definition sim_elems_more_stmt (fuel : nat) : Prop :=
  forall (l : list ascii) (i : nat),
  buf_eq_char (Buf l) i ","%char = true ->
  match parse_array_elems_fast (Buf l) fuel (S i) with
  | Some (vs, j) => parse_elements_more fuel (skipn i l) = Some (map (decode (Buf l)) vs, "]"%char :: skipn j l)
  | None => parse_elements_more fuel (skipn i l) = None
  end.

Definition sim_members_stmt (fuel : nat) : Prop :=
  forall (l : list ascii) (i : nat),
  buf_eq_char (Buf l) (skip_ws_fast (Buf l) i) "}"%char = false ->
  match parse_object_members_fast (Buf l) fuel i with
  | Some (ms, j) => parse_members fuel (skip_ws (skipn i l)) = Some (map (decode_member (Buf l)) ms, "}"%char :: skipn j l)
  | None => parse_members fuel (skip_ws (skipn i l)) = None
  end.

Definition sim_members_more_stmt (fuel : nat) : Prop :=
  forall (l : list ascii) (i : nat),
  buf_eq_char (Buf l) i ","%char = true ->
  match parse_object_members_fast (Buf l) fuel (S i) with
  | Some (ms, j) => parse_members_more fuel (skipn i l) = Some (map (decode_member (Buf l)) ms, "}"%char :: skipn j l)
  | None => parse_members_more fuel (skipn i l) = None
  end.

Lemma parse_fast_sim (fuel : nat) :
  sim_value_stmt fuel /\ sim_array_stmt fuel /\ sim_object_stmt fuel /\
  sim_elems_stmt fuel /\ sim_elems_more_stmt fuel /\ sim_members_stmt fuel /\ sim_members_more_stmt fuel.
Proof.
  induction fuel as [| fuel' IH].
  - repeat split; intros l i H;
      cbn [parse_value_fast parse_array_fast parse_array_elems_fast parse_object_fast parse_object_members_fast
           parse_value parse_array parse_object parse_elements parse_elements_more parse_members parse_members_more];
      try reflexivity; try congruence.
  - destruct IH as [IHv [IHa [IHo [IHe [IHem [IHm IHmm]]]]]].
    repeat split.
    + (* value *)
      intros l i.
      rewrite <- (skip_ws_fast_sim l i).
      cbn [parse_value_fast buffer_get].
      set (i0 := skip_ws_fast (Buf l) i).
      destruct (nth_error l i0) as [c |] eqn:Ei0.
      * rewrite (skipn_cons_head ascii l i0 c Ei0).
        cbn [parse_value].
        destruct (Ascii.eqb_spec c "{"%char) as [Hc | Hc].
        -- subst c. cbn [parse_value].
           destruct (parse_object_fast (Buf l) fuel' i0) as [[vo jo] |] eqn:Eo.
           ++ pose proof (IHo l i0) as Ho. assert (Hi0 : S i0 <= List.length l) by (apply nth_error_lt_len in Ei0; lia). specialize (Ho Hi0).
              rewrite Eo in Ho.
              pose proof (parse_object_fast_shape l fuel' i0 vo jo Eo) as [ms Hms]. subst vo.
              cbn -[skipn] in Ho. rewrite Ho. cbn [decode]. reflexivity.
           ++ pose proof (IHo l i0) as Ho. assert (Hi0 : S i0 <= List.length l) by (apply nth_error_lt_len in Ei0; lia). specialize (Ho Hi0).
              rewrite Eo in Ho. cbn -[skipn] in Ho. rewrite Ho in *. reflexivity.
        -- destruct (Ascii.eqb_spec c "["%char) as [Hsq | Hsq].
           ++ subst c. cbn [parse_value].
              destruct (parse_array_fast (Buf l) fuel' i0) as [[va ja] |] eqn:Ea.
              ** pose proof (IHa l i0) as Ha. assert (Hi0 : S i0 <= List.length l) by (apply nth_error_lt_len in Ei0; lia). specialize (Ha Hi0).
                 rewrite Ea in Ha.
                 pose proof (parse_array_fast_shape l fuel' i0 va ja Ea) as [vs Hvs]. subst va.
                 cbn -[skipn] in Ha. rewrite Ha. cbn [decode]. reflexivity.
              ** pose proof (IHa l i0) as Ha. assert (Hi0 : S i0 <= List.length l) by (apply nth_error_lt_len in Ei0; lia). specialize (Ha Hi0).
                 rewrite Ea in Ha. cbn -[skipn] in Ha. rewrite Ha in *. reflexivity.
           ++ destruct (Ascii.eqb_spec c "034"%char) as [Hquote | Hquote].
              ** subst c. cbn [parse_value].
                 destruct (parse_string_fast (Buf l) i0) as [[vs js] |] eqn:Es.
                 --- unfold parse_string_fast, buffer_length in Es.
                     destruct (find_string_end (Buf l) (S i0)) as [endq |] eqn:Efj; [| congruence].
                     injection Es as Hvs Hjs. subst vs js.
                     cbn [parse_value decode]. cbn [parse_value].
                     pose proof (parse_string_fast_decode l i0 endq Efj Ei0) as Hps.
                     rewrite <- (skipn_cons_head ascii l i0 "034"%char Ei0). rewrite Hps. reflexivity.
                 --- cbn [parse_value]. cbn [parse_value].
                     pose proof (parse_string_fast_span l i0 Ei0) as Hps. rewrite Es in Hps. rewrite <- (skipn_cons_head ascii l i0 "034"%char Ei0). rewrite Hps. reflexivity.
              ** destruct (Ascii.eqb_spec c "t"%char) as [Ht | Ht].
                 --- subst c. cbn [parse_value].
                     destruct (parse_lit_fast (Buf l) "rue"%string (S i0) (JBool_f true)) as [[vl jl] |] eqn:El.
                     +++ pose proof (parse_lit_fast_sim l "rue"%string (S i0) (JBool_f true)) as Hl. rewrite El in Hl. cbn -[skipn parse_lit] in Hl.
                         destruct Hl as [Hvl Hlit]. subst vl.
                         rewrite Hlit. cbn [decode]. reflexivity.
                     +++ pose proof (parse_lit_fast_sim l "rue"%string (S i0) (JBool_f true)) as Hl. rewrite El in Hl. rewrite Hl. cbn. reflexivity.
                 --- destruct (Ascii.eqb_spec c "f"%char) as [Hf | Hf].
                     +++ subst c. cbn [parse_value].
                         destruct (parse_lit_fast (Buf l) "alse"%string (S i0) (JBool_f false)) as [[vl jl] |] eqn:El.
                         *** pose proof (parse_lit_fast_sim l "alse"%string (S i0) (JBool_f false)) as Hl. rewrite El in Hl. cbn -[skipn parse_lit] in Hl.
                             destruct Hl as [Hvl Hlit]. subst vl.
                             rewrite Hlit. cbn [decode]. reflexivity.
                         *** pose proof (parse_lit_fast_sim l "alse"%string (S i0) (JBool_f false)) as Hl. rewrite El in Hl. rewrite Hl. cbn. reflexivity.
                     +++ destruct (Ascii.eqb_spec c "n"%char) as [Hn | Hn].
                         *** subst c. cbn [parse_value].
                             destruct (parse_lit_fast (Buf l) "ull"%string (S i0) JNull_f) as [[vl jl] |] eqn:El.
                             ++++ pose proof (parse_lit_fast_sim l "ull"%string (S i0) JNull_f) as Hl. rewrite El in Hl. cbn -[skipn parse_lit] in Hl.
                                  destruct Hl as [Hvl Hlit]. subst vl.
                                  rewrite Hlit. cbn [decode]. reflexivity.
                             ++++ pose proof (parse_lit_fast_sim l "ull"%string (S i0) JNull_f) as Hl. rewrite El in Hl. rewrite Hl. cbn. reflexivity.
                         *** cbn [parse_value].
                             destruct (Ascii.eqb c "-"%char) eqn:Eneg; destruct (is_digitb c) eqn:Edig; cbn [orb].
                             ++++ destruct (parse_number_fast (Buf l) i0) as [[vn jn] |] eqn:En.
                                  ----- pose proof (parse_number_fast_span l i0) as Hnsp. rewrite En in Hnsp.
                                        destruct Hnsp as [[m e] Hme].
                                        pose proof (parse_number_fast_shape l i0 jn vn En) as Hshape. subst vn.
                                        pose proof (parse_number_forward l i0 jn (m, e) Hme) as Hjle. assert (Hidx : jn = i0 + (jn - i0)) by lia.
                                        rewrite Hidx in Hme.
                                        assert (Hnum : decode_number (Buf l) i0 (jn - i0) = (m, e)) by (apply (decode_number_correct l i0 (jn - i0) (m, e)); exact Hme).
                                        rewrite <- (skipn_cons_head ascii l i0 c Ei0). rewrite Hme. cbn. cbn [decode]. rewrite Hnum. cbn. rewrite <- Hidx. reflexivity.
                                  ----- pose proof (parse_number_fast_span l i0) as Hnsp. rewrite En in Hnsp. rewrite <- (skipn_cons_head ascii l i0 c Ei0). rewrite Hnsp. cbn. reflexivity.
                             ++++ destruct (parse_number_fast (Buf l) i0) as [[vn jn] |] eqn:En.
                                  ----- pose proof (parse_number_fast_span l i0) as Hnsp. rewrite En in Hnsp.
                                        destruct Hnsp as [[m e] Hme].
                                        pose proof (parse_number_fast_shape l i0 jn vn En) as Hshape. subst vn.
                                        pose proof (parse_number_forward l i0 jn (m, e) Hme) as Hjle. assert (Hidx : jn = i0 + (jn - i0)) by lia.
                                        rewrite Hidx in Hme.
                                        assert (Hnum : decode_number (Buf l) i0 (jn - i0) = (m, e)) by (apply (decode_number_correct l i0 (jn - i0) (m, e)); exact Hme).
                                        rewrite <- (skipn_cons_head ascii l i0 c Ei0). rewrite Hme. cbn. cbn [decode]. rewrite Hnum. cbn. rewrite <- Hidx. reflexivity.
                                  ----- pose proof (parse_number_fast_span l i0) as Hnsp. rewrite En in Hnsp. rewrite <- (skipn_cons_head ascii l i0 c Ei0). rewrite Hnsp. cbn. reflexivity.
                             ++++ destruct (parse_number_fast (Buf l) i0) as [[vn jn] |] eqn:En.
                                  ----- pose proof (parse_number_fast_span l i0) as Hnsp. rewrite En in Hnsp.
                                        destruct Hnsp as [[m e] Hme].
                                        pose proof (parse_number_fast_shape l i0 jn vn En) as Hshape. subst vn.
                                        pose proof (parse_number_forward l i0 jn (m, e) Hme) as Hjle. assert (Hidx : jn = i0 + (jn - i0)) by lia.
                                        rewrite Hidx in Hme.
                                        assert (Hnum : decode_number (Buf l) i0 (jn - i0) = (m, e)) by (apply (decode_number_correct l i0 (jn - i0) (m, e)); exact Hme).
                                        rewrite <- (skipn_cons_head ascii l i0 c Ei0). rewrite Hme. cbn. cbn [decode]. rewrite Hnum. cbn. rewrite <- Hidx. reflexivity.
                                  ----- pose proof (parse_number_fast_span l i0) as Hnsp. rewrite En in Hnsp. rewrite <- (skipn_cons_head ascii l i0 c Ei0). rewrite Hnsp. cbn. reflexivity.
                             ++++ reflexivity.
      * cbn [parse_value_fast parse_value]. rewrite (nth_error_none_skipn ascii l i0 Ei0). reflexivity.
    + (* array *)
      intros l i Hi.
      cbn [parse_array_fast buffer_get].
      destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) (S i)) "]"%char) eqn:Ecl.
      * destruct fuel' as [| fuel''].
        -- cbn [parse_array_fast parse_array parse_elements]. reflexivity.
        -- cbn [parse_array_fast]. cbn [parse_array].
           rewrite <- (skip_ws_fast_sim l (S i)).
           apply buf_eq_char_true in Ecl. rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) (S i)) "]"%char Ecl).
           cbn [parse_elements skip_ws]. rewrite (Ascii.eqb_refl "]"%char). cbn [parse_array skip_ws]. cbn [map]. reflexivity.
      * cbn [parse_array_fast].
        destruct (parse_array_elems_fast (Buf l) fuel' (skip_ws_fast (Buf l) (S i))) as [[vs i2] |] eqn:Eae.
        -- cbn [parse_array]. rewrite <- (skip_ws_fast_sim l (S i)).
           pose proof (IHe l (skip_ws_fast (Buf l) (S i))) as He.
           assert (Hb : buf_eq_char (Buf l) (skip_ws_fast (Buf l) (skip_ws_fast (Buf l) (S i))) "]"%char = false).
           { rewrite (skip_ws_fast_idem l (S i) Hi). exact Ecl. }
           specialize (He Hb).
           rewrite Eae in He. cbn in He.
           rewrite (skip_ws_fast_skip_ws_idem l (S i)) in He.
           rewrite He. cbn. reflexivity.
        -- cbn [parse_array]. rewrite <- (skip_ws_fast_sim l (S i)).
           pose proof (IHe l (skip_ws_fast (Buf l) (S i))) as He.
           assert (Hb : buf_eq_char (Buf l) (skip_ws_fast (Buf l) (skip_ws_fast (Buf l) (S i))) "]"%char = false).
           { rewrite (skip_ws_fast_idem l (S i) Hi). exact Ecl. }
           specialize (He Hb).
           rewrite Eae in He. cbn in He.
           rewrite (skip_ws_fast_skip_ws_idem l (S i)) in He. rewrite He. reflexivity.
    + (* object *)
      intros l i Hi.
      cbn [parse_object_fast buffer_get].
      destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) (S i)) "}"%char) eqn:Ecl.
      * destruct fuel' as [| fuel''].
        -- cbn [parse_object_fast parse_object parse_members]. reflexivity.
        -- cbn [parse_object_fast]. cbn [parse_object].
           rewrite <- (skip_ws_fast_sim l (S i)).
           apply buf_eq_char_true in Ecl. rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) (S i)) "}"%char Ecl).
           cbn [parse_members skip_ws]. rewrite (Ascii.eqb_refl "}"%char). cbn [parse_object skip_ws]. cbn [map]. reflexivity.
      * cbn [parse_object_fast].
        destruct (parse_object_members_fast (Buf l) fuel' (skip_ws_fast (Buf l) (S i))) as [[ms i2] |] eqn:Eom.
        -- cbn [parse_object]. rewrite <- (skip_ws_fast_sim l (S i)).
           pose proof (IHm l (skip_ws_fast (Buf l) (S i))) as Hm.
           assert (Hb : buf_eq_char (Buf l) (skip_ws_fast (Buf l) (skip_ws_fast (Buf l) (S i))) "}"%char = false).
           { rewrite (skip_ws_fast_idem l (S i) Hi). exact Ecl. }
           specialize (Hm Hb).
           rewrite Eom in Hm. cbn in Hm.
           rewrite (skip_ws_fast_skip_ws_idem l (S i)) in Hm.
           rewrite Hm. cbn. reflexivity.
        -- cbn [parse_object]. rewrite <- (skip_ws_fast_sim l (S i)).
           pose proof (IHm l (skip_ws_fast (Buf l) (S i))) as Hm.
           assert (Hb : buf_eq_char (Buf l) (skip_ws_fast (Buf l) (skip_ws_fast (Buf l) (S i))) "}"%char = false).
           { rewrite (skip_ws_fast_idem l (S i) Hi). exact Ecl. }
           specialize (Hm Hb).
           rewrite Eom in Hm. cbn in Hm.
           rewrite (skip_ws_fast_skip_ws_idem l (S i)) in Hm. rewrite Hm. reflexivity.
    + (* elems *)
      intros l i Hb.
      cbn [parse_array_elems_fast buffer_get].
      rewrite <- (skip_ws_fast_sim l i).
      destruct (nth_error l (skip_ws_fast (Buf l) i)) as [c0 |] eqn:Ei0'.
      * cbn [parse_array_elems_fast]. rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
        destruct (parse_value_fast (Buf l) fuel' i) as [[v i2] |] eqn:Ev.
        -- pose proof (IHv l i) as Hv. rewrite Ev in Hv. cbn in Hv.
           rewrite <- (skip_ws_fast_sim l i) in Hv. rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hv.
           destruct (nth_error l (skip_ws_fast (Buf l) i2)) as [c |] eqn:Ei3;
           [| cbn [parse_elements];
              rewrite (proj2 (Ascii.eqb_neq c0 "]"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "]"%char Hb c0 Ei0'));
              rewrite Hv; cbn; rewrite <- (skip_ws_fast_sim l i2); rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i2) Ei3);
              destruct fuel' as [| fuel'']; cbn; reflexivity].
           cbn [parse_array_elems_fast].
           rewrite match_ascii_comma_close.
           destruct (Ascii.eqb c ","%char) eqn:Ecomma.
           ++ cbn [parse_array_elems_fast].
              destruct (parse_array_elems_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i2))) as [[vs' i4] |] eqn:Eae.
              ** pose proof (IHem l (skip_ws_fast (Buf l) i2) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i2) c ","%char Ei3 Ecomma)) as Hem.
                 rewrite Eae in Hem. cbn in Hem.
                 cbn [parse_elements]. rewrite (proj2 (Ascii.eqb_neq c0 "]"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "]"%char Hb c0 Ei0')).
                 cbn [parse_elements]. rewrite Hv. cbn. rewrite <- (skip_ws_fast_sim l i2). rewrite Hem. cbn [map]. reflexivity.
              ** pose proof (IHem l (skip_ws_fast (Buf l) i2) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i2) c ","%char Ei3 Ecomma)) as Hem.
                 rewrite Eae in Hem. cbn in Hem.
                 cbn [parse_elements]. rewrite (proj2 (Ascii.eqb_neq c0 "]"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "]"%char Hb c0 Ei0')).
                 cbn [parse_elements]. rewrite Hv. cbn. rewrite <- (skip_ws_fast_sim l i2). rewrite Hem. reflexivity.
           ++ destruct (Ascii.eqb c "]"%char) eqn:Ecl.
              ** apply (Ascii.eqb_eq c "]"%char) in Ecl. subst c. cbn [parse_array_elems_fast].
                 cbn [parse_elements]. rewrite (proj2 (Ascii.eqb_neq c0 "]"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "]"%char Hb c0 Ei0')).
                 cbn [parse_elements]. rewrite Hv. cbn. rewrite <- (skip_ws_fast_sim l i2).
                 destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv; discriminate | cbn [parse_elements_more]; rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) "]"%char Ei3); rewrite (Ascii.eqb_refl "]"%char); cbn [map]; reflexivity].
              ** cbn [parse_array_elems_fast].
                 cbn [parse_elements]. rewrite (proj2 (Ascii.eqb_neq c0 "]"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "]"%char Hb c0 Ei0')).
                 cbn [parse_elements]. rewrite Hv. cbn. rewrite <- (skip_ws_fast_sim l i2).
                 destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv; discriminate | cbn [parse_elements_more]; rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) c Ei3); rewrite Ecl; rewrite Ecomma; cbn; reflexivity].
        -- cbn [parse_array_elems_fast].
           cbn [parse_elements]. rewrite (proj2 (Ascii.eqb_neq c0 "]"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "]"%char Hb c0 Ei0')).
           cbn [parse_elements].
           pose proof (IHv l i) as Hv. rewrite Ev in Hv. cbn in Hv.
           rewrite <- (skip_ws_fast_sim l i) in Hv. rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hv. rewrite Hv. reflexivity.
      * cbn [parse_array_elems_fast].
        destruct fuel' as [| fuel''].
        -- cbn [parse_value_fast parse_array_elems_fast]. rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i) Ei0'). cbn [parse_elements]. reflexivity.
        -- cbn [parse_value_fast parse_array_elems_fast buffer_get]. rewrite Ei0'. rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i) Ei0'). cbn [parse_elements]. reflexivity.
    + (* elems_more *)
      intros l i Hb.
      cbn [parse_array_elems_fast buffer_get].
      destruct (parse_value_fast (Buf l) fuel' (S i)) as [[v i2] |] eqn:Ev.
      * pose proof (IHv l (S i)) as Hv. rewrite Ev in Hv.
        destruct (nth_error l (skip_ws_fast (Buf l) i2)) as [c |] eqn:Ei3.
        ** cbn [parse_array_elems_fast].
           rewrite match_ascii_comma_close.
           destruct (Ascii.eqb c ","%char) eqn:Ecomma.
           *** cbn [parse_array_elems_fast].
               destruct (parse_array_elems_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i2))) as [[vs' i4] |] eqn:Eae.
               **** pose proof (IHem l (skip_ws_fast (Buf l) i2) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i2) c ","%char Ei3 Ecomma)) as Hem.
                    rewrite Eae in Hem.
                    cbn [parse_elements_more].
                    rewrite (skipn_cons_head ascii l i ","%char (buf_eq_char_true l i ","%char Hb)).
                    cbn [parse_elements_more].
                    rewrite (proj2 (Ascii.eqb_neq ","%char "]"%char) ltac:(discriminate)).
                    cbn [parse_elements_more].
                    rewrite (Ascii.eqb_refl ","%char).
                    cbn [parse_elements_more].
                    rewrite Hv.
                    rewrite <- (skip_ws_fast_sim l i2).
                    rewrite Hem.
                    cbn [map]. reflexivity.
               **** pose proof (IHem l (skip_ws_fast (Buf l) i2) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i2) c ","%char Ei3 Ecomma)) as Hem.
                    rewrite Eae in Hem.
                    cbn [parse_elements_more].
                    rewrite (skipn_cons_head ascii l i ","%char (buf_eq_char_true l i ","%char Hb)).
                    cbn [parse_elements_more].
                    rewrite (proj2 (Ascii.eqb_neq ","%char "]"%char) ltac:(discriminate)).
                    cbn [parse_elements_more].
                    rewrite (Ascii.eqb_refl ","%char).
                    cbn [parse_elements_more].
                    rewrite Hv.
                    rewrite <- (skip_ws_fast_sim l i2).
                    rewrite Hem. reflexivity.
           *** destruct (Ascii.eqb c "]"%char) eqn:Ecl.
               **** cbn [parse_array_elems_fast].
                    cbn [parse_elements_more].
                    rewrite (skipn_cons_head ascii l i ","%char (buf_eq_char_true l i ","%char Hb)).
                    cbn [parse_elements_more].
                    rewrite (proj2 (Ascii.eqb_neq ","%char "]"%char) ltac:(discriminate)).
                    cbn [parse_elements_more].
                    rewrite (Ascii.eqb_refl ","%char).
                    cbn [parse_elements_more].
                    rewrite Hv.
                    rewrite <- (skip_ws_fast_sim l i2).
                    apply (Ascii.eqb_eq c "]"%char) in Ecl. subst c.
                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) "]"%char Ei3).
                    destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv; discriminate | cbn [parse_elements_more]; rewrite (Ascii.eqb_refl "]"%char); cbn [map]; reflexivity].
               **** cbn [parse_array_elems_fast].
                    cbn [parse_elements_more].
                    rewrite (skipn_cons_head ascii l i ","%char (buf_eq_char_true l i ","%char Hb)).
                    cbn [parse_elements_more].
                    rewrite (proj2 (Ascii.eqb_neq ","%char "]"%char) ltac:(discriminate)).
                    cbn [parse_elements_more].
                    rewrite (Ascii.eqb_refl ","%char).
                    cbn [parse_elements_more].
                    rewrite Hv.
                    rewrite <- (skip_ws_fast_sim l i2).
                    destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv; discriminate | cbn [parse_elements_more]; rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) c Ei3); rewrite Ecl; rewrite Ecomma; cbn; reflexivity].
        ** cbn [parse_array_elems_fast].
           cbn [parse_elements_more].
           rewrite (skipn_cons_head ascii l i ","%char (buf_eq_char_true l i ","%char Hb)).
           cbn [parse_elements_more].
           rewrite (proj2 (Ascii.eqb_neq ","%char "]"%char) ltac:(discriminate)).
           cbn [parse_elements_more].
           rewrite (Ascii.eqb_refl ","%char).
           cbn [parse_elements_more].
           rewrite Hv.
           rewrite <- (skip_ws_fast_sim l i2).
           rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i2) Ei3).
           destruct fuel' as [| fuel'']; cbn; reflexivity.
      * cbn [parse_array_elems_fast].
        cbn [parse_elements_more].
        rewrite (skipn_cons_head ascii l i ","%char (buf_eq_char_true l i ","%char Hb)).
        cbn [parse_elements_more].
        rewrite (proj2 (Ascii.eqb_neq ","%char "]"%char) ltac:(discriminate)).
        cbn [parse_elements_more].
        rewrite (Ascii.eqb_refl ","%char).
        cbn [parse_elements_more].
        pose proof (IHv l (S i)) as Hv. rewrite Ev in Hv. rewrite Hv. reflexivity.
    + (* members *)
      intros l i Hb.
      cbn [parse_object_members_fast buffer_get].
      rewrite <- (skip_ws_fast_sim l i).
      destruct (nth_error l (skip_ws_fast (Buf l) i)) as [c0 |] eqn:Ei0'.
      * cbn [parse_object_members_fast].
        destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) i) "034"%char) eqn:Eq.
        ** cbn [parse_object_members_fast].
           destruct (parse_string_fast (Buf l) (skip_ws_fast (Buf l) i)) as [[v i2] |] eqn:Es.
           *** unfold parse_string_fast, buffer_length in Es.
               destruct (find_string_end (Buf l) (S (skip_ws_fast (Buf l) i))) as [endq |] eqn:Efj; [| congruence].
               injection Es as Hv Hjs. subst v.
               pose proof (parse_string_fast_decode l (skip_ws_fast (Buf l) i) endq Efj (buf_eq_char_true l (skip_ws_fast (Buf l) i) "034"%char Eq)) as Hps.
               cbn [parse_object_members_fast].
               destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) i2) ":"%char) eqn:Ecolon.
               **** cbn [parse_object_members_fast].
                    destruct (parse_value_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i2))) as [[v2 i4] |] eqn:Ev.
                    ***** pose proof (IHv l (S (skip_ws_fast (Buf l) i2))) as Hv2. rewrite Ev in Hv2.
                          destruct (nth_error l (skip_ws_fast (Buf l) i4)) as [c3 |] eqn:Ei5.
                          ****** cbn [parse_object_members_fast].
                                  rewrite match_ascii_comma_brace.
                                  destruct (Ascii.eqb c3 ","%char) eqn:Ecomma.
                                  ******* cbn [parse_object_members_fast].
                                           destruct (parse_object_members_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i4))) as [[ms' i6] |] eqn:Eom.
                                           ******** pose proof (IHmm l (skip_ws_fast (Buf l) i4) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i4) c3 ","%char Ei5 Ecomma)) as Hmm2.
                                                    rewrite Eom in Hmm2.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
                                                    cbn [parse_members].
                                                    rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
                                                    cbn [parse_members].
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    rewrite Hmm2.
                                                    cbn [decode_member map]. reflexivity.
                                           ******** pose proof (IHmm l (skip_ws_fast (Buf l) i4) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i4) c3 ","%char Ei5 Ecomma)) as Hmm2.
                                                    rewrite Eom in Hmm2.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
                                                    cbn [parse_members].
                                                    rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
                                                    cbn [parse_members].
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    rewrite Hmm2. reflexivity.
                                  ******* destruct (Ascii.eqb c3 "}"%char) eqn:Ecl3.
                                           ******** cbn [parse_object_members_fast].
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
                                                    cbn [parse_members].
                                                    rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
                                                    cbn [parse_members].
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    apply (Ascii.eqb_eq c3 "}"%char) in Ecl3. subst c3.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i4) "}"%char Ei5).
                                                    destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv2; discriminate | cbn [parse_members_more]; rewrite (Ascii.eqb_refl "}"%char); cbn [decode_member map]; reflexivity].
                                           ******** cbn [parse_object_members_fast].
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
                                                    cbn [parse_members].
                                                    rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
                                                    cbn [parse_members].
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv2; discriminate | cbn [parse_members_more]; rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i4) c3 Ei5); rewrite Ecl3; rewrite Ecomma; cbn; reflexivity].
                          ****** cbn [parse_object_members_fast].
                                  rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
                                  cbn [parse_members].
                                  rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
                                  cbn [parse_members].
                                  rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
                                  rewrite Hps.
                                  rewrite Hjs.
                                  rewrite <- (skip_ws_fast_sim l i2).
                                  pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                  rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                  cbn [parse_members].
                                  rewrite (Ascii.eqb_refl ":"%char).
                                  cbn [parse_members].
                                  rewrite Hv2.
                                  rewrite <- (skip_ws_fast_sim l i4).
                                  rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i4) Ei5).
                                  destruct fuel' as [| fuel'']; cbn; reflexivity.
                    ***** cbn [parse_object_members_fast].
                          rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
                          cbn [parse_members].
                          rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
                          cbn [parse_members].
                          rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
                          rewrite Hps.
                          rewrite Hjs.
                          rewrite <- (skip_ws_fast_sim l i2).
                          pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                          rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                          cbn [parse_members].
                          rewrite (Ascii.eqb_refl ":"%char).
                          cbn [parse_members].
                          pose proof (IHv l (S (skip_ws_fast (Buf l) i2))) as Hv2. rewrite Ev in Hv2. rewrite Hv2. reflexivity.
               **** cbn [parse_object_members_fast].
                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
                    cbn [parse_members].
                    rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
                    cbn [parse_members].
                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
                    rewrite Hps.
                    rewrite Hjs.
                    rewrite <- (skip_ws_fast_sim l i2).
                    destruct (nth_error l (skip_ws_fast (Buf l) i2)) as [c' |] eqn:Ei2'.
                    ***** rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) c' Ei2').
                          cbn [parse_members].
                          rewrite (proj2 (Ascii.eqb_neq c' ":"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i2) ":"%char Ecolon c' Ei2')).
                          cbn [parse_members]. reflexivity.
                    ***** rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i2) Ei2'). reflexivity.
           *** cbn [parse_object_members_fast].
               rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
               cbn [parse_members].
               rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
               cbn [parse_members].
               pose proof (parse_string_fast_span l (skip_ws_fast (Buf l) i) (buf_eq_char_true l (skip_ws_fast (Buf l) i) "034"%char Eq)) as Hps.
               rewrite Es in Hps.
               rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0') in Hps.
               rewrite Hps. reflexivity.
        ** cbn [parse_object_members_fast].
           rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i) c0 Ei0').
           cbn [parse_members].
           rewrite (proj2 (Ascii.eqb_neq c0 "}"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "}"%char Hb c0 Ei0')).
           cbn [parse_members].
           cbn [parse_string].
           rewrite (proj2 (Ascii.eqb_neq c0 "034"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i) "034"%char Eq c0 Ei0')).
           cbn [parse_members]. reflexivity.
      * cbn [parse_object_members_fast].
        rewrite (buf_eq_char_sym l (skip_ws_fast (Buf l) i) "034"%char).
        rewrite Ei0'.
        cbn [parse_members]. rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i) Ei0'). reflexivity.
    + (* members_more *)
      intros l i Hb.
      cbn [parse_object_members_fast buffer_get].
      rewrite (skipn_cons_head ascii l i ","%char (buf_eq_char_true l i ","%char Hb)).
      cbn [parse_members_more].
      rewrite (proj2 (Ascii.eqb_neq ","%char "}"%char) ltac:(discriminate)).
      cbn [parse_members_more].
      rewrite (Ascii.eqb_refl ","%char).
      cbn [parse_members_more].
      rewrite <- (skip_ws_fast_sim l (S i)).
      destruct (nth_error l (skip_ws_fast (Buf l) (S i))) as [c0 |] eqn:Ei0'.
      * cbn [parse_object_members_fast].
        destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) (S i)) "034"%char) eqn:Eq.
        ** cbn [parse_object_members_fast].
           destruct (parse_string_fast (Buf l) (skip_ws_fast (Buf l) (S i))) as [[v i2] |] eqn:Es.
           *** unfold parse_string_fast, buffer_length in Es.
               destruct (find_string_end (Buf l) (S (skip_ws_fast (Buf l) (S i)))) as [endq |] eqn:Efj; [| congruence].
               injection Es as Hv Hjs. subst v.
               pose proof (parse_string_fast_decode l (skip_ws_fast (Buf l) (S i)) endq Efj (buf_eq_char_true l (skip_ws_fast (Buf l) (S i)) "034"%char Eq)) as Hps.
               cbn [parse_object_members_fast].
               destruct (buf_eq_char (Buf l) (skip_ws_fast (Buf l) i2) ":"%char) eqn:Ecolon.
               **** cbn [parse_object_members_fast].
                    destruct (parse_value_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i2))) as [[v2 i4] |] eqn:Ev.
                    ***** pose proof (IHv l (S (skip_ws_fast (Buf l) i2))) as Hv2. rewrite Ev in Hv2.
                          destruct (nth_error l (skip_ws_fast (Buf l) i4)) as [c3 |] eqn:Ei5.
                          ****** cbn [parse_object_members_fast].
                                  rewrite match_ascii_comma_brace.
                                  destruct (Ascii.eqb c3 ","%char) eqn:Ecomma.
                                  ******* cbn [parse_object_members_fast].
                                           destruct (parse_object_members_fast (Buf l) fuel' (S (skip_ws_fast (Buf l) i4))) as [[ms' i6] |] eqn:Eom.
                                           ******** pose proof (IHmm l (skip_ws_fast (Buf l) i4) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i4) c3 ","%char Ei5 Ecomma)) as Hmm2.
                                                    rewrite Eom in Hmm2.
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members_more].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members_more].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    rewrite Hmm2.
                                                    cbn [decode_member map]. reflexivity.
                                           ******** pose proof (IHmm l (skip_ws_fast (Buf l) i4) (buf_eq_char_from_eqb l (skip_ws_fast (Buf l) i4) c3 ","%char Ei5 Ecomma)) as Hmm2.
                                                    rewrite Eom in Hmm2.
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members_more].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members_more].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    rewrite Hmm2. reflexivity.
                                  ******* destruct (Ascii.eqb c3 "}"%char) eqn:Ecl3.
                                           ******** cbn [parse_object_members_fast].
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members_more].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members_more].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    apply (Ascii.eqb_eq c3 "}"%char) in Ecl3. subst c3.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i4) "}"%char Ei5).
                                                    destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv2; discriminate | cbn [parse_members_more]; rewrite (Ascii.eqb_refl "}"%char); cbn [decode_member map]; reflexivity].
                                           ******** cbn [parse_object_members_fast].
                                                    rewrite Hps.
                                                    rewrite Hjs.
                                                    rewrite <- (skip_ws_fast_sim l i2).
                                                    pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                                    rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                                    cbn [parse_members_more].
                                                    rewrite (Ascii.eqb_refl ":"%char).
                                                    cbn [parse_members_more].
                                                    rewrite Hv2.
                                                    rewrite <- (skip_ws_fast_sim l i4).
                                                    destruct fuel' as [| fuel'']; [cbn [parse_value] in Hv2; discriminate | cbn [parse_members_more]; rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i4) c3 Ei5); rewrite Ecl3; rewrite Ecomma; cbn; reflexivity].
                          ****** cbn [parse_object_members_fast].
                                  rewrite Hps.
                                  rewrite Hjs.
                                  rewrite <- (skip_ws_fast_sim l i2).
                                  pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                                  rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                                  cbn [parse_members_more].
                                  rewrite (Ascii.eqb_refl ":"%char).
                                  cbn [parse_members_more].
                                  rewrite Hv2.
                                  rewrite <- (skip_ws_fast_sim l i4).
                                  rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i4) Ei5).
                                  destruct fuel' as [| fuel'']; cbn; reflexivity.
                    ***** cbn [parse_object_members_fast].
                          rewrite Hps.
                          rewrite Hjs.
                          rewrite <- (skip_ws_fast_sim l i2).
                          pose proof (buf_eq_char_true l (skip_ws_fast (Buf l) i2) ":"%char Ecolon) as Hcolon.
                          rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) ":"%char Hcolon).
                          cbn [parse_members_more].
                          rewrite (Ascii.eqb_refl ":"%char).
                          cbn [parse_members_more].
                          pose proof (IHv l (S (skip_ws_fast (Buf l) i2))) as Hv2. rewrite Ev in Hv2. rewrite Hv2. reflexivity.
               **** cbn [parse_object_members_fast].
                    rewrite Hps.
                    rewrite Hjs.
                    rewrite <- (skip_ws_fast_sim l i2).
                    destruct (nth_error l (skip_ws_fast (Buf l) i2)) as [c' |] eqn:Ei2'.
                    ***** rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) i2) c' Ei2').
                          cbn [parse_members_more].
                          rewrite (proj2 (Ascii.eqb_neq c' ":"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) i2) ":"%char Ecolon c' Ei2')).
                          cbn [parse_members_more]. reflexivity.
                    ***** rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) i2) Ei2'). reflexivity.
           *** cbn [parse_object_members_fast].
               pose proof (parse_string_fast_span l (skip_ws_fast (Buf l) (S i)) (buf_eq_char_true l (skip_ws_fast (Buf l) (S i)) "034"%char Eq)) as Hps.
               rewrite Es in Hps. rewrite Hps. reflexivity.
        ** cbn [parse_object_members_fast].
           rewrite (skipn_cons_head ascii l (skip_ws_fast (Buf l) (S i)) c0 Ei0').
           cbn [parse_string].
           rewrite (proj2 (Ascii.eqb_neq c0 "034"%char) (buf_eq_char_false l (skip_ws_fast (Buf l) (S i)) "034"%char Eq c0 Ei0')).
           cbn [parse_members_more]. reflexivity.
      * cbn [parse_object_members_fast].
        rewrite (buf_eq_char_sym l (skip_ws_fast (Buf l) (S i)) "034"%char).
        rewrite Ei0'.
        rewrite (nth_error_none_skipn ascii l (skip_ws_fast (Buf l) (S i)) Ei0').
        cbn. reflexivity.
Qed.

Lemma parse_value_fast_sim (l : list ascii) (fuel : nat) (i : nat) :
  match parse_value_fast (Buf l) fuel i with
  | Some (v, j) => parse_value fuel (skip_ws (skipn i l)) = Some (decode (Buf l) v, skipn j l)
  | None => parse_value fuel (skip_ws (skipn i l)) = None
  end.
Proof. exact (proj1 (parse_fast_sim fuel) l i). Qed.

Lemma parse_array_fast_sim (l : list ascii) (fuel : nat) (i : nat) :
  S i <= List.length l ->
  match parse_array_fast (Buf l) fuel i with
  | Some (JArr_f vs, j) => parse_array fuel (skipn (S i) l) = Some (map (decode (Buf l)) vs, skipn j l)
  | _ => parse_array fuel (skipn (S i) l) = None
  end.
Proof. exact (proj1 (proj2 (parse_fast_sim fuel)) l i). Qed.

Lemma parse_object_fast_sim (l : list ascii) (fuel : nat) (i : nat) :
  S i <= List.length l ->
  match parse_object_fast (Buf l) fuel i with
  | Some (JObj_f ms, j) => parse_object fuel (skipn (S i) l) = Some (map (decode_member (Buf l)) ms, skipn j l)
  | _ => parse_object fuel (skipn (S i) l) = None
  end.
Proof. exact (proj1 (proj2 (proj2 (parse_fast_sim fuel))) l i). Qed.

Lemma parse_array_elems_fast_sim (l : list ascii) (fuel : nat) (i : nat) :
  buf_eq_char (Buf l) (skip_ws_fast (Buf l) i) "]"%char = false ->
  match parse_array_elems_fast (Buf l) fuel i with
  | Some (vs, j) => parse_elements fuel (skip_ws (skipn i l)) = Some (map (decode (Buf l)) vs, "]"%char :: skipn j l)
  | None => parse_elements fuel (skip_ws (skipn i l)) = None
  end.
Proof. exact (proj1 (proj2 (proj2 (proj2 (parse_fast_sim fuel)))) l i). Qed.

Lemma parse_object_members_fast_sim (l : list ascii) (fuel : nat) (i : nat) :
  buf_eq_char (Buf l) (skip_ws_fast (Buf l) i) "}"%char = false ->
  match parse_object_members_fast (Buf l) fuel i with
  | Some (ms, j) => parse_members fuel (skip_ws (skipn i l)) = Some (map (decode_member (Buf l)) ms, "}"%char :: skipn j l)
  | None => parse_members fuel (skip_ws (skipn i l)) = None
  end.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (parse_fast_sim fuel)))))) l i). Qed.

Lemma parse_json_fast_correct (l : list ascii) :
  match parse_json_fast (Buf l) with
  | Some v => parse_json l = Some (decode (Buf l) v)
  | None => parse_json l = None
  end.
Proof.
  unfold parse_json_fast, parse_json, buffer_length.
  pose proof (parse_value_fast_sim l (3 * Datatypes.length l + 2) 0) as Hsim.
  destruct (parse_value_fast (Buf l) (3 * Datatypes.length l + 2) 0) as [[v j] |] eqn:Ev.
  - replace (parse_value_fast (Buf l) (3 * Datatypes.length l + 2) 0) with (Some (v, j)) in Hsim by (symmetry; exact Ev).
    cbn in Hsim.
    destruct (Nat.eqb (skip_ws_fast (Buf l) j) (List.length l)) eqn:Eeq.
    + cbn. rewrite Hsim. cbn.
      rewrite Nat.eqb_eq in Eeq.
      rewrite <- (skip_ws_fast_sim l j). rewrite Eeq.
      assert (E : skipn (List.length l) l = []) by (apply skipn_all2; lia). rewrite E. reflexivity.
    + cbn. rewrite Hsim. cbn.
      destruct (skip_ws (skipn j l)) as [| c rest] eqn:Esk.
      * exfalso. rewrite Nat.eqb_neq in Eeq.
        assert (Hle : skip_ws_fast (Buf l) j <= List.length l).
        { apply skip_ws_fast_le.
          destruct (parse_fast_bound (3 * List.length l + 2)) as [BV _].
          apply (BV l 0 v j). lia. exact Ev. }
        apply Eeq.
        rewrite <- (skip_ws_fast_sim l j) in Esk.
        apply (f_equal (@List.length ascii)) in Esk.
        rewrite List.length_skipn in Esk.
        apply Nat.sub_0_le in Esk.
        apply Nat.le_antisymm; [exact Hle | exact Esk].
      * reflexivity.
  - replace (parse_value_fast (Buf l) (3 * Datatypes.length l + 2) 0) with (@None (Json_fast * nat)) in Hsim by (symmetry; exact Ev). cbn in Hsim. cbn. rewrite Hsim. reflexivity.
Qed.
