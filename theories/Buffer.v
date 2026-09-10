(* ------------------------------------------------------------------------- *)
(* Buffer-backed parser: index arithmetic over a byte accessor [s : nat ->    *)
(* ascii], certified equal to the list-based surface parser in Toml.v.        *)
(*                                                                             *)
(* The bridge lemmas ([*_spec]) prove each [*_at] twin agrees with the list   *)
(* parser via [to_list]. Soundness/completeness then carry over from Toml.v   *)
(* for free — no re-proof of the denotational statements.                      *)
(* ------------------------------------------------------------------------- *)

From Stdlib Require Import List Nat PeanoNat Ascii Lia.
From Parsebot Require Import Toml.
Import ListNotations.

(* ------------------------------------------------------------------------- *)
(* Buffer materialization and positional lemmas                               *)
(* ------------------------------------------------------------------------- *)

Definition to_list (s : nat -> ascii) (n : nat) : list ascii :=
  map s (seq 0 n).

Lemma nth_error_to_list : forall s n i, i < n -> nth_error (to_list s n) i = Some (s i).
Proof.
  intros s n i Hi. unfold to_list.
  rewrite nth_error_map, nth_error_seq.
  rewrite (proj2 (Nat.ltb_lt i n) Hi). simpl. reflexivity.
Qed.

Lemma skipn_to_list_nil : forall s n i, i >= n -> skipn i (to_list s n) = [].
Proof.
  intros s n i Hi. unfold to_list.
  rewrite skipn_map, skipn_seq.
  assert (H : n - i = 0) by lia. rewrite H. simpl. reflexivity.
Qed.

Lemma skipn_to_list_cons : forall s n i, i < n ->
  skipn i (to_list s n) = s i :: skipn (S i) (to_list s n).
Proof.
  intros s n i Hi. apply (skipn_cons_head _ _ _ (s i)).
  apply nth_error_to_list. exact Hi.
Qed.

Lemma skipn_to_list_nonempty : forall s n i, i < n -> skipn i (to_list s n) <> [].
Proof.
  intros s n i Hi. rewrite skipn_to_list_cons by assumption. discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* skip_ws                                                                    *)
(* ------------------------------------------------------------------------- *)

Fixpoint skip_ws_loop (s : nat -> ascii) (rem i : nat) : nat :=
  match rem with
  | 0 => i
  | S rem' => if is_ws (s i) then skip_ws_loop s rem' (S i) else i
  end.

Definition skip_ws_at (s : nat -> ascii) (i n : nat) : nat :=
  skip_ws_loop s (n - i) i.

Lemma skip_ws_loop_spec : forall s rem i,
  skipn (skip_ws_loop s rem i) (to_list s (i + rem)) = skip_ws (skipn i (to_list s (i + rem))).
Proof.
  intros s rem. induction rem as [| rem' IH]; intros i.
  - cbn [skip_ws_loop]. rewrite skipn_to_list_nil by lia. cbn [skip_ws]. reflexivity.
  - replace (i + S rem') with (S i + rem') by lia.
    cbn [skip_ws_loop]. destruct (is_ws (s i)) eqn:Ews.
    + rewrite (skipn_to_list_cons s (S i + rem') i) by lia. cbn [skip_ws]. rewrite Ews.
      rewrite (IH (S i)). reflexivity.
    + rewrite (skipn_to_list_cons s (S i + rem') i) by lia. cbn [skip_ws]. rewrite Ews. reflexivity.
Qed.

Lemma skip_ws_at_spec : forall s n i,
  skipn (skip_ws_at s i n) (to_list s n) = skip_ws (skipn i (to_list s n)).
Proof.
  intros s n i. unfold skip_ws_at.
  destruct (Nat.lt_ge_cases i n) as [Hlt | Hge].
  - replace (to_list s n) with (to_list s (i + (n - i))).
    + apply skip_ws_loop_spec.
    + f_equal. lia.
  - assert (H : n - i = 0) by lia. rewrite H. simpl.
    rewrite skipn_to_list_nil by lia. simpl. reflexivity.
Qed.

Lemma skip_ws_ne_nil : forall w, skip_ws w <> [] -> w <> [].
Proof.
  intros w H Hnil. subst w. simpl in H. contradiction.
Qed.

Lemma skipn_to_list_ne_nil : forall s n i, skipn i (to_list s n) <> [] -> i < n.
Proof.
  intros s n i H. destruct (Nat.lt_ge_cases i n) as [Hlt | Hge]; [exact Hlt |].
  exfalso. apply H. apply skipn_to_list_nil. exact Hge.
Qed.

Lemma skip_ws_at_strict : forall s n i, skip_ws_at s i n < n -> i < n.
Proof.
  intros s n i H.
  apply (skipn_to_list_ne_nil s n i). apply skip_ws_ne_nil.
  rewrite <- (skip_ws_at_spec s n i).
  apply skipn_to_list_nonempty. exact H.
Qed.

(* ------------------------------------------------------------------------- *)
(* take_digits                                                                *)
(* ------------------------------------------------------------------------- *)

Fixpoint take_digits_loop (s : nat -> ascii) (rem i : nat) : list ascii * nat :=
  match rem with
  | 0 => ([], i)
  | S rem' => if is_digit (s i)
      then let (ds, j) := take_digits_loop s rem' (S i) in (s i :: ds, j)
      else ([], i)
  end.

Definition take_digits_at (s : nat -> ascii) (i n : nat) : list ascii * nat :=
  take_digits_loop s (n - i) i.

Lemma take_digits_loop_spec : forall s rem i ds j,
  take_digits_loop s rem i = (ds, j) ->
  (ds, skipn j (to_list s (i + rem))) = take_digits (skipn i (to_list s (i + rem))).
Proof.
  intros s rem. induction rem as [| rem' IH]; intros i ds j H.
  - cbn [take_digits_loop] in H. injection H as Hds Hj. subst ds j.
    rewrite skipn_to_list_nil by lia. cbn [take_digits]. reflexivity.
  - replace (i + S rem') with (S i + rem') by lia.
    cbn [take_digits_loop] in H.
    destruct (is_digit (s i)) eqn:Ed in H.
    + simpl in H.
      destruct (take_digits_loop s rem' (S i)) as [ds' j'] eqn:E' in H.
      injection H as Hds Hj. subst ds j.
      rewrite (skipn_to_list_cons s (S i + rem') i) by lia. cbn [take_digits]. rewrite Ed.
      specialize (IH (S i) ds' j' E'). rewrite <- IH. simpl. reflexivity.
    + simpl in H. injection H as Hds Hj. subst ds j.
      rewrite (skipn_to_list_cons s (S i + rem') i) by lia. cbn [take_digits]. rewrite Ed.
      reflexivity.
Qed.

Lemma take_digits_at_spec : forall s i n,
  match take_digits_at s i n with
  | (ds, j) => (ds, skipn j (to_list s n)) = take_digits (skipn i (to_list s n))
  end.
Proof.
  intros s i n. unfold take_digits_at.
  destruct (Nat.lt_ge_cases i n) as [Hlt | Hge].
  - replace (to_list s n) with (to_list s (i + (n - i))).
    + destruct (take_digits_loop s (n - i) i) as [ds j] eqn:E.
      apply (take_digits_loop_spec s (n - i) i ds j E).
    + f_equal. lia.
  - assert (H : n - i = 0) by lia. rewrite H. simpl.
    rewrite skipn_to_list_nil by lia. simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* take_ident                                                                 *)
(* ------------------------------------------------------------------------- *)

Fixpoint take_ident_loop (s : nat -> ascii) (rem i : nat) : list ascii * nat :=
  match rem with
  | 0 => ([], i)
  | S rem' => if is_ident_char (s i)
      then let (ds, j) := take_ident_loop s rem' (S i) in (s i :: ds, j)
      else ([], i)
  end.

Definition take_ident_at (s : nat -> ascii) (i n : nat) : list ascii * nat :=
  take_ident_loop s (n - i) i.

Lemma take_ident_loop_spec : forall s rem i ds j,
  take_ident_loop s rem i = (ds, j) ->
  (ds, skipn j (to_list s (i + rem))) = take_ident (skipn i (to_list s (i + rem))).
Proof.
  intros s rem. induction rem as [| rem' IH]; intros i ds j H.
  - cbn [take_ident_loop] in H. injection H as Hds Hj. subst ds j.
    rewrite skipn_to_list_nil by lia. cbn [take_ident]. reflexivity.
  - replace (i + S rem') with (S i + rem') by lia.
    cbn [take_ident_loop] in H.
    destruct (is_ident_char (s i)) eqn:Ei in H.
    + simpl in H.
      destruct (take_ident_loop s rem' (S i)) as [ds' j'] eqn:E' in H.
      injection H as Hds Hj. subst ds j.
      rewrite (skipn_to_list_cons s (S i + rem') i) by lia. cbn [take_ident]. rewrite Ei.
      specialize (IH (S i) ds' j' E'). rewrite <- IH. simpl. reflexivity.
    + simpl in H. injection H as Hds Hj. subst ds j.
      rewrite (skipn_to_list_cons s (S i + rem') i) by lia. cbn [take_ident]. rewrite Ei.
      reflexivity.
Qed.

Lemma take_ident_at_spec : forall s i n,
  match take_ident_at s i n with
  | (ds, j) => (ds, skipn j (to_list s n)) = take_ident (skipn i (to_list s n))
  end.
Proof.
  intros s i n. unfold take_ident_at.
  destruct (Nat.lt_ge_cases i n) as [Hlt | Hge].
  - replace (to_list s n) with (to_list s (i + (n - i))).
    + destruct (take_ident_loop s (n - i) i) as [ds j] eqn:E.
      apply (take_ident_loop_spec s (n - i) i ds j E).
    + f_equal. lia.
  - assert (H : n - i = 0) by lia. rewrite H. simpl.
    rewrite skipn_to_list_nil by lia. simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* parse_int                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition parse_int_at (s : nat -> ascii) (i n : nat) : option (nat * nat) :=
  if i <? n then
    if is_digit (s i) then
      let (ds, j) := take_digits_at s (S i) n in
      Some (digits_to_nat (s i :: ds) 0, j)
    else None
  else None.

Lemma parse_int_at_spec : forall s i n,
  option_map (fun '(v, j) => (v, skipn j (to_list s n))) (parse_int_at s i n)
  = parse_int (skipn i (to_list s n)).
Proof.
  intros s i n. unfold parse_int_at, parse_int.
  destruct (i <? n) eqn:E.
  - apply Nat.ltb_lt in E.
    rewrite (skipn_to_list_cons s n i) by lia. cbn iota.
    destruct (is_digit (s i)) eqn:Ed.
    + cbn iota.
      pose proof (take_digits_at_spec s (S i) n) as Htd.
      unfold take_digits_at in Htd. unfold take_digits_at.
      destruct (take_digits_loop s (n - S i) (S i)) as [ds j] eqn:Etd in Htd |- *.
      rewrite <- Htd. simpl. reflexivity.
    + cbn iota. reflexivity.
  - apply Nat.ltb_ge in E.
    rewrite skipn_to_list_nil by lia. cbn iota. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* parse_ident                                                                *)
(* ------------------------------------------------------------------------- *)

Definition parse_ident_at (s : nat -> ascii) (i n : nat) : option (seg * nat) :=
  if i <? n then
    if is_ident_char (s i) then
      let (ds, j) := take_ident_at s (S i) n in
      Some (s i :: ds, j)
    else None
  else None.

Lemma parse_ident_at_spec : forall s i n,
  option_map (fun '(sg, j) => (sg, skipn j (to_list s n))) (parse_ident_at s i n)
  = parse_ident (skipn i (to_list s n)).
Proof.
  intros s i n. unfold parse_ident_at, parse_ident.
  destruct (i <? n) eqn:E.
  - apply Nat.ltb_lt in E.
    rewrite (skipn_to_list_cons s n i) by lia. cbn iota.
    destruct (is_ident_char (s i)) eqn:Ei.
    + cbn iota.
      pose proof (take_ident_at_spec s (S i) n) as Hti.
      unfold take_ident_at in Hti. unfold take_ident_at.
      destruct (take_ident_loop s (n - S i) (S i)) as [ds j] eqn:Eti in Hti |- *.
      rewrite <- Hti. simpl. reflexivity.
    + cbn iota. reflexivity.
  - apply Nat.ltb_ge in E.
    rewrite skipn_to_list_nil by lia. cbn iota. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* parse_key                                                                  *)
(* ------------------------------------------------------------------------- *)

Fixpoint parse_key_at (fuel : nat) (s : nat -> ascii) (i n : nat) : option (key * nat) :=
  match fuel with
  | O => None
  | S fuel' =>
      match parse_ident_at s i n with
      | None => None
      | Some (sg, j) =>
          if j <? n then
            if Ascii.eqb (s j) "."%char then
              match parse_key_at fuel' s (S j) n with
              | None => None
              | Some (ks, j') => Some (sg :: ks, j')
              end
            else Some ([sg], j)
          else Some ([sg], j)
      end
  end.

Lemma parse_key_at_spec : forall fuel s i n,
  option_map (fun '(k, j) => (k, skipn j (to_list s n))) (parse_key_at fuel s i n)
  = parse_key fuel (skipn i (to_list s n)).
Proof.
  induction fuel as [| fuel' IH]; intros s i n.
  - cbn [parse_key_at parse_key]. reflexivity.
  - cbn [parse_key_at parse_key].
    pose proof (parse_ident_at_spec s i n) as Hi.
    destruct (parse_ident_at s i n) as [[sg j0] |] eqn:Ei in Hi |- *.
    + cbn [option_map] in Hi.
      rewrite <- Hi. cbn iota.
      destruct (j0 <? n) eqn:E.
      * apply Nat.ltb_lt in E.
        rewrite (skipn_to_list_cons s n j0) by lia. cbn iota.
        destruct (Ascii.eqb (s j0) "."%char) eqn:Ed.
        -- pose proof (IH s (S j0) n) as Hk.
           destruct (parse_key_at fuel' s (S j0) n) as [[ks j1] |] eqn:Ek in Hk |- *.
           ++ cbn [option_map] in Hk. rewrite <- Hk. cbn [option_map]. reflexivity.
           ++ cbn [option_map] in Hk. rewrite <- Hk. cbn [option_map]. reflexivity.
        -- cbn [option_map]. rewrite (skipn_to_list_cons s n j0) by lia. reflexivity.
      * apply Nat.ltb_ge in E.
        cbn [option_map]. rewrite (skipn_to_list_nil s n j0) by lia. cbn iota. reflexivity.
    + cbn [option_map] in Hi. rewrite <- Hi. cbn [option_map]. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* parse_stmt                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition parse_stmt_at (fuel : nat) (s : nat -> ascii) (i n : nat) : option (stmt * nat) :=
  match fuel with
  | O => None
  | S fuel' =>
      if i <? n then
        if Ascii.eqb (s i) "["%char then
          if S i <? n then
            if Ascii.eqb (s (S i)) "["%char then
              match parse_key_at fuel' s (S (S i)) n with
              | Some (k, j) =>
                  if j <? n then
                    if Ascii.eqb (s j) "]"%char then
                      if S j <? n then
                        if Ascii.eqb (s (S j)) "]"%char then Some (SArray k, S (S j)) else None
                      else None
                    else None
                  else None
              | None => None
              end
            else
              match parse_key_at fuel' s (S i) n with
              | Some (k, j) =>
                  if j <? n then
                    if Ascii.eqb (s j) "]"%char then Some (STable k, S j) else None
                  else None
              | None => None
              end
          else None
        else
          match parse_key_at fuel' s i n with
          | Some (k, j) =>
              match skip_ws_at s j n with
              | j1 =>
                  if j1 <? n then
                    if Ascii.eqb (s j1) "="%char then
                      match parse_int_at s (skip_ws_at s (S j1) n) n with
                      | Some (v, j2) => Some (SKV k v, j2)
                      | None => None
                      end
                    else None
                  else None
              end
          | None => None
          end
      else None
  end.

Lemma parse_stmt_at_spec : forall fuel s i n,
  option_map (fun '(st, j) => (st, skipn j (to_list s n))) (parse_stmt_at fuel s i n)
  = parse_stmt fuel (skipn i (to_list s n)).
Proof.
  destruct fuel as [| fuel']; intros s i n.
  - cbn [parse_stmt_at parse_stmt]. reflexivity.
  - cbn [parse_stmt_at parse_stmt].
    destruct (i <? n) eqn:E.
    + apply Nat.ltb_lt in E.
      rewrite (skipn_to_list_cons s n i) by lia. cbn iota.
      destruct (Ascii.eqb (s i) "["%char) eqn:Ebr.
      * destruct (S i <? n) eqn:E2.
        -- apply Nat.ltb_lt in E2.
           rewrite (skipn_to_list_cons s n (S i)) by lia. cbn iota.
           destruct (Ascii.eqb (s (S i)) "["%char) eqn:Ebr2.
           ++ (* array: [[ key ]] *)
              pose proof (parse_key_at_spec fuel' s (S (S i)) n) as Hk.
              destruct (parse_key_at fuel' s (S (S i)) n) as [[k j0] |] eqn:Ek in Hk |- *.
              ** cbn [option_map] in Hk. rewrite <- Hk. cbn iota.
                 destruct (j0 <? n) eqn:Ej.
                 --- apply Nat.ltb_lt in Ej.
                     rewrite (skipn_to_list_cons s n j0) by lia. cbn iota.
                     destruct (Ascii.eqb (s j0) "]"%char) eqn:Er1.
                     +++ destruct (S j0 <? n) eqn:Ej2.
                         *** apply Nat.ltb_lt in Ej2.
                             rewrite (skipn_to_list_cons s n (S j0)) by lia. cbn iota.
                             destruct (Ascii.eqb (s (S j0)) "]"%char) eqn:Er2.
                             ++++ cbn [option_map]. reflexivity.
                             ++++ cbn [option_map]. reflexivity.
                         *** apply Nat.ltb_ge in Ej2.
                             cbn [option_map]. rewrite (skipn_to_list_nil s n (S j0)) by lia. cbn iota. reflexivity.
                     +++ cbn [option_map]. reflexivity.
                 --- apply Nat.ltb_ge in Ej.
                     cbn [option_map]. rewrite (skipn_to_list_nil s n j0) by lia. cbn iota. reflexivity.
              ** cbn [option_map] in Hk. rewrite <- Hk. cbn [option_map]. reflexivity.
           ++ (* table: [ key ] *)
              pose proof (parse_key_at_spec fuel' s (S i) n) as Hk2.
              rewrite (skipn_to_list_cons s n (S i)) in Hk2 by lia.
              destruct (parse_key_at fuel' s (S i) n) as [[k j0] |] eqn:Ek2 in Hk2 |- *.
              ** cbn [option_map] in Hk2. rewrite <- Hk2. cbn iota.
                 destruct (j0 <? n) eqn:Ej.
                 --- apply Nat.ltb_lt in Ej.
                     rewrite (skipn_to_list_cons s n j0) by lia. cbn iota.
                     destruct (Ascii.eqb (s j0) "]"%char) eqn:Er1.
                     +++ cbn [option_map]. reflexivity.
                     +++ cbn [option_map]. reflexivity.
                 --- apply Nat.ltb_ge in Ej.
                     cbn [option_map]. rewrite (skipn_to_list_nil s n j0) by lia. cbn iota. reflexivity.
              ** cbn [option_map] in Hk2. rewrite <- Hk2. cbn [option_map]. reflexivity.
        -- apply Nat.ltb_ge in E2.
           cbn [option_map]. rewrite (skipn_to_list_nil s n (S i)) by lia. cbn iota. reflexivity.
      * (* key = value *)
        pose proof (parse_key_at_spec fuel' s i n) as Hk3.
        rewrite (skipn_to_list_cons s n i) in Hk3 by lia.
        destruct (parse_key_at fuel' s i n) as [[k j0] |] eqn:Ek3 in Hk3 |- *.
        -- cbn [option_map] in Hk3. rewrite <- Hk3. cbn iota.
           pose proof (skip_ws_at_spec s n j0) as Hsw.
           remember (skip_ws_at s j0 n) as jws1 eqn:Esw.
           cbn iota.
           rewrite <- Hsw. cbn iota.
           destruct (jws1 <? n) eqn:Ej1.
           ++ apply Nat.ltb_lt in Ej1.
              rewrite (skipn_to_list_cons s n jws1) by lia. cbn iota.
              destruct (Ascii.eqb (s jws1) "="%char) eqn:Eeq.
              ** pose proof (skip_ws_at_spec s n (S jws1)) as Hsw2.
                 remember (skip_ws_at s (S jws1) n) as jws2 eqn:Esw2.
                 rewrite <- Hsw2.
                 pose proof (parse_int_at_spec s jws2 n) as Hpi.
                 destruct (parse_int_at s jws2 n) as [[v j3] |] eqn:Epi in Hpi |- *.
                 +++ cbn [option_map] in Hpi. rewrite <- Hpi. cbn [option_map]. cbn iota. reflexivity.
                 +++ cbn [option_map] in Hpi. rewrite <- Hpi. cbn [option_map]. cbn iota. reflexivity.
              ** cbn [option_map]. reflexivity.
           ++ apply Nat.ltb_ge in Ej1.
              cbn [option_map]. rewrite (skipn_to_list_nil s n jws1) by lia. cbn iota. reflexivity.
        -- cbn [option_map] in Hk3. rewrite <- Hk3. cbn [option_map]. reflexivity.
    + apply Nat.ltb_ge in E.
      cbn [option_map]. rewrite (skipn_to_list_nil s n i) by lia. cbn iota. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* parse_doc                                                                  *)
(* ------------------------------------------------------------------------- *)

Fixpoint parse_doc_at (fuel : nat) (s : nat -> ascii) (i n : nat) : option Document :=
  match skip_ws_at s i n with
  | j0 =>
      if j0 <? n then
        match fuel with
        | O => None
        | S fuel' =>
            match parse_stmt_at fuel' s j0 n with
            | None => None
            | Some (st, j1) =>
                match skip_ws_at s j1 n with
                | j2 =>
                    if j2 <? n then
                      if is_ws (s j1) then
                        match parse_doc_at fuel' s j1 n with
                        | None => None
                        | Some ss => Some (st :: ss)
                        end
                      else None
                    else Some [st]
                end
            end
        end
      else Some []
  end.

Lemma parse_doc_at_spec : forall fuel s i n,
  parse_doc_at fuel s i n = parse_doc fuel (skipn i (to_list s n)).
Proof.
  induction fuel as [| fuel' IH]; intros s i n.
  - cbn [parse_doc_at parse_doc].
    rewrite <- (skip_ws_at_spec s n i).
    remember (skip_ws_at s i n) as p eqn:Esw.
    cbn iota.
    destruct (p <? n) eqn:E.
    + apply Nat.ltb_lt in E.
      rewrite (skipn_to_list_cons s n p) by lia. cbn iota. reflexivity.
    + apply Nat.ltb_ge in E.
      rewrite (skipn_to_list_nil s n p) by lia. cbn iota. reflexivity.
  - cbn [parse_doc_at parse_doc].
    rewrite <- (skip_ws_at_spec s n i).
    remember (skip_ws_at s i n) as p eqn:Esw.
    cbn iota.
    destruct (p <? n) eqn:E.
    + apply Nat.ltb_lt in E.
      rewrite (skipn_to_list_cons s n p) by lia. cbn iota.
      pose proof (parse_stmt_at_spec fuel' s p n) as Hst.
      rewrite (skipn_to_list_cons s n p) in Hst by lia.
      destruct (parse_stmt_at fuel' s p n) as [[st j1] |] eqn:Est in Hst |- *.
      * cbn [option_map] in Hst. rewrite <- Hst. cbn iota.
        rewrite <- (skip_ws_at_spec s n j1).
        remember (skip_ws_at s j1 n) as q eqn:Esw1.
        cbn iota.
        destruct (q <? n) eqn:E2.
        -- apply Nat.ltb_lt in E2.
           rewrite (skipn_to_list_cons s n q) by lia. cbn iota.
           assert (Hj1 : j1 < n).
           { apply (skip_ws_at_strict s n j1). rewrite <- Esw1. exact E2. }
           rewrite (skipn_to_list_cons s n j1) by lia. cbn iota.
           destruct (is_ws (s j1)) eqn:Ews1.
           ++ rewrite <- (skipn_to_list_cons s n j1) by lia.
              rewrite (IH s j1 n). reflexivity.
           ++ reflexivity.
        -- apply Nat.ltb_ge in E2.
           rewrite (skipn_to_list_nil s n q) by lia. cbn iota. reflexivity.
      * cbn [option_map] in Hst. rewrite <- Hst. cbn iota. reflexivity.
    + apply Nat.ltb_ge in E.
      rewrite (skipn_to_list_nil s n p) by lia. cbn iota. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* top-level: validate a whole buffer                                        *)
(* ------------------------------------------------------------------------- *)

Definition parse_then_validate_at (s : nat -> ascii) (n : nat) : option Namespace :=
  match parse_doc_at (S (2 * n)) s 0 n with
  | None => None
  | Some doc => run [] doc
  end.

Lemma parse_then_validate_at_spec : forall s n,
  parse_then_validate_at s n = parse_then_validate (to_list s n).
Proof.
  intros s n. unfold parse_then_validate_at, parse_then_validate.
  rewrite (parse_doc_at_spec (S (2 * n)) s 0 n).
  cbn [skipn].
  assert (Hlen : List.length (to_list s n) = n).
  { unfold to_list. rewrite length_map, length_seq. reflexivity. }
  rewrite Hlen. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* Extraction: buffer-backed parser with machine-int [nat]                    *)
(* ------------------------------------------------------------------------- *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlNatInt ExtrOcamlChar.
Extraction "buffer.ml" parse_doc parse_doc_at parse_then_validate parse_then_validate_at.
