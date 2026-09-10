# Task: finish the RFC 8259 JSON completion — fix the broken lemmas in theories/Json.v

## Goal
`theories/Json.v` was just extended from the S5 "integer, no-escapes" subset to full RFC 8259
(floats + string escapes). The GRAMMAR and PARSER now compile; the SOUNDNESS / COMPLETENESS /
SHAPE lemmas are broken and must be fixed so the whole file compiles with ZERO `Admitted`/`admit`.

## Build (ONLY this shell)
```
cd /home/gavin/dev/Scidonia/parsebot && nix develop --command bash -c 'rocq compile -R theories Parsebot theories/Json.v 2>&1'
```
`exit: 0` (or no `Error`) means success. Compile stops at the first error; fix iteratively.

## What changed (do NOT undo; these are the deliverable)
1. **AST**: `JNumber : Z -> Z -> Json` (was `Z -> Json`). `JNumber m e` = mantissa × 10^e.
2. **Grammar**: `number_spec : Spec ascii unit json_nt (Z * Z)` — now `[minus] int [frac] [exp]`
   via `number_value neg intv fr ex` (a helper `Definition` you can prove lemmas about).
   `frac_spec : ... (nat * nat)` (value, digit-count), `exp_spec : ... (bool * nat)` (neg, value).
3. **Grammar**: `string_spec` now decodes escapes. `string_char_spec : ... (list ascii)`
   (unescaped char -> `[c]`, or an escape -> decoded bytes). `escape_spec` handles
   `\" \\ \/ \b \f \n \r \t \uXXXX`; `\uXXXX` uses `codepoint_to_utf8` (UTF-8 of a BMP point).
4. **Parser**: `parse_number : list ascii -> option ((Z * Z) * list ascii)` (returns ((m,e),rest)).
   New helpers `parse_int`, `parse_frac`, `parse_exp`, `parse_hex4`, `parse_escape`.
5. **Parser**: `parse_string_chars : nat -> list ascii -> option (list ascii * list ascii)` is now
   FUEL-based (escape consumes 2–6 chars, so structural recursion failed). `parse_string w`
   calls `parse_string_chars (List.length rest) rest`.
6. **value_spec** uses `Map (fun p : Z * Z => JNumber (fst p) (snd p)) number_spec`.

## What is broken (fix these; do NOT weaken any statement)
Run the compile; the first error is at ~line 910 (`parse_string_chars_sound`). There are ~12 lemmas
to fix, in order of appearance:

**Soundness / shape (parser → denote):**
- `parse_string_chars_sound` (~line 900): statement must become
  `parse_string_chars fuel w = Some (cs, rest) -> denote ... string_char_spec ... cs ...`
  (per-char, over the DECODED bytes). Needs induction on `fuel`, with an escape case.
- `parse_string_chars_shape` (~line 920): no longer `w = cs ++ quote :: rest` (cs is decoded).
  Replace with a lemma that `rest` is a SUFFIX of `w` (the parser only consumes input; the decoded
  `cs` is produced, not consumed): `{ pre : list ascii & pre ++ rest = w }`. Callers use it to
  thread the remaining input.
- `number_sound` (~line 960): statement becomes
  `parse_number w = Some ((m,e), rest) -> denote ... number_spec ... (m,e) ...`. Full rewrite
  mirroring the 4-level `Bind`/`Alt`/`Map` structure. Prove `number_value` agrees with the parser's
  `m`/`e` computation (they are the SAME code — `simpl`/`f_equal`/`lia` should close the arithmetic).
- `parse_string_sound` (~line 1030): update for `parse_string_chars (length rest) rest` and the
  decoded string. It decomposes into opening quote + `Many string_char_spec` + closing quote, with
  `List.concat` of the decoded chunks.
- `parse_string_shape` / `parse_number_shape` (~line 1120): shape lemmas (result is a suffix).
  `parse_number_shape` now returns `{ pre & pre ++ rest = w }` for `parse_number w = Some ((m,e), rest)`.
- `value_sound_call` and `parse_member_sound` / `parse_all_sound`: the number branch must reflect
  `number_spec : ... (Z*Z)` and `parse_number` returning `((m,e), rest)`.

**Completeness (denote → parser):**
- `parse_string_chars_complete` / `parse_string_complete` (~line 1900+): full rewrite for escapes +
  fuel. The inverse of the soundness lemmas.
- `parse_number_complete` (~line 2100+): full rewrite for the new number grammar (4-level Bind).
- `number_spec` "cannot start with whitespace" helper (~line 1733) and any other `number_spec`
  helper: update the `denote_bind_iff`/`denote_map_iff` type args (`bool Z`, `nat Z`, ... become
  the new `bool (Z*Z)`, `nat (Z*Z)`, and the `Map (fun p => JNumber (fst p) (snd p))` instances).
- Every `denote_map_iff ... Z Json JNumber number_spec ...` (grep `JNumber`) must become
  `denote_map_iff ... (Z * Z) Json (fun p : Z * Z => JNumber (fst p) (snd p)) number_spec ...`
  (the `Map` in `value_spec` is now `fun p => JNumber (fst p) (snd p)`).
- The acceptance examples near the end (`obj_input`, any `JNumber` constructor) must use the new
  `JNumber m e` arity.

## Key context (the `denote` calculus)
- `Spec` combinators in `theories/Spec.v`: `Pure`, `Tok`, `Seq`, `Alt`, `Map`, `Bind`, `Many`,
  `Exactly`, `Call`. `denote` is an inductive relation with constructors `d_pure d_tok d_seq
  d_alt_l d_alt_r d_map d_bind d_many_nil d_many_cons d_exactly_nil d_exactly_cons d_call`.
- Inversion lemmas (already in Spec.v): `denote_pure_iff`, `denote_tok_iff`, `denote_seq_iff`,
  `denote_alt_iff`, `denote_map_iff`, `denote_bind_iff`, `denote_many_iff`, `denote_call_iff`.
  They are `iffT` (Type-level iff): use `apply (fst (denote_map_iff ...)) in H` to invert.
- Existing proofs use helper lemmas `char_sound`, `digit1_9_sound`, `take_digits_sound`,
  `take_digits_shape`, `ws_part_skip`, `skip_ws_sound`, `parse_lit_sound`, `sep_by_*` — REUSE them;
  do not re-derive.
- `parse_value` is a mutual `Fixpoint`; the `Opaque parse_lit parse_string parse_number` directives
  (and `Transparent ...` around the leaf completeness lemmas) must be kept in sync — the leaf
  parser shapes must be available where `sep_by_shape`/`parse_all_shape` need them.

## Do NOT
- Do NOT weaken any soundness/completeness/shape statement (they are the certification deliverable).
- Do NOT change the grammar specs, the parser definitions, or `number_value` (they are correct and
  agree; the proofs must witness that agreement).
- Do NOT `Admitted`/`admit`/`Abort`/`Axiom` anything.

## Acceptance
- `rocq compile -R theories Parsebot theories/Json.v` exits 0.
- `grep -n "Admitted\|admit\|Abort\|Axiom\|Admit" theories/Json.v` prints nothing.
- The top-level `parse_all_sound`, `parse_json_sound`, and `parse_json_complete` statements keep
  their meaning (soundness + completeness of the FULL RFC 8259 parser now).

Report: (1) compile exit, (2) the final statements of `number_sound`, `parse_string_sound`,
`parse_number_complete`, `parse_string_complete`, `parse_json_complete`, (3) any deviation and why.
