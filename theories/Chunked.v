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
