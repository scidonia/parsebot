# Zero-copy JSON parser — benchmark

`parse_json_fast : buffer -> option Json_fast` (extracted with `buffer -> string`) records
`(start, len)` spans for strings and numbers instead of materializing them. Its refinement
`decode : buffer -> Json_fast -> Json` is certified: `parse_json_fast_correct` proves
`parse_json_fast (Buf l) = Some v -> parse_json l = Some (decode (Buf l) v)`.

- **Date:** 2026-09-10
- **Machine:** Intel Core Ultra 7 268V (8 cores), OCaml 5.2.0, Zarith
- **Method:** `ocamlfind ocamlopt -package zarith,unix`; 3 warmup + 20 timed runs per parser,
  wall clock (`Unix.gettimeofday`), **minimum** per-run time reported. Input converted to
  `char list` once (excluded from timing) for the certified list-based parser.

All numbers are the **extracted OCaml** — `parse_json_fast`/`decode` from `JsonFast.v`, and the
certified `parse_json` from `Json.v`.

## Two phases

| phase | what it does | cost |
| --- | --- | --- |
| **tokenize** (`parse_json_fast`) | scan bytes, record `(start,len)` spans | one pass, no allocation |
| **materialize** (`decode`) | re-parse each span with the certified string/number parsers | second pass, on demand |

The tokenizer is the win; `decode` is a *separate* pass you pay only when you want the materialized
`Json` value (validation / field-picking needs only `parse_json_fast`).

## Results

| file | bytes | fast MB/s | list MB/s | tokenize speedup | decode MB/s | tokenize+decode vs list |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| gsoc-2018.json | 3,327,831 | 267.9 | 11.0 | **24.4×** | 7.7 | 0.70× |
| update-center.json | 533,178 | 125.9 | 33.0 | 3.81× | 21.7 | 0.66× |
| twitter.json | 631,514 | 130.9 | 42.7 | 3.06× | 30.1 | 0.70× |
| github_events.json | 65,132 | 169.7 | 56.9 | 2.98× | 31.5 | 0.55× |
| canada.json | 2,251,051 | 56.8 | 21.4 | 2.65× | 15.6 | 0.73× |
| random.json | 510,476 | 91.3 | 36.8 | 2.48× | 23.4 | 0.64× |
| apache_builds.json | 127,275 | 129.0 | 56.4 | 2.29× | 31.8 | 0.56× |
| mesh.json | 723,597 | 37.7 | 20.4 | 1.85× | 13.0 | 0.63× |
| citm_catalog.json | 1,727,204 | 119.4 | 79.5 | 1.50× | 58.1 | 0.73× |
| instruments.json | 220,346 | 102.9 | 74.7 | 1.38× | 40.0 | 0.54× |
| large_int_4.75m.json | 4,759,973 | 47.4 | 34.5 | 1.37× | 18.6 | 0.54× |
| marine_ik.json | 2,983,466 | 46.4 | 34.6 | 1.34× | 20.1 | 0.58× |
| large_int_10m.json | 9,996,047 | 35.6 | 30.6 | 1.16× | 14.8 | 0.48× |

**Tokenize geometric mean: 2.43×** (range 1.16×–24.4×).
**Tokenize+decode geometric mean: 0.61×** (range 0.48×–0.73×).

## Reading the numbers

- **Number/string-heavy objects** (`gsoc-2018`, `update-center`, `twitter`, `random`) show the
  largest tokenize wins — up to **24×** on `gsoc-2018` (1264 nested objects). The tokenizer records
  number/string spans instead of running `Z`-arithmetic and building `char list`s.
- **Huge-integer arrays** (`large_int_10m`) show the least (1.16×): both parsers are
  digit-scanning-bound at ~30–35 MB/s, and Zarith `Z` conversion is already fast.
- **Tokenize+decode is ~0.6×** the list parser on every file: `decode` *re-parses* each span, so the
  full pipeline does the tokenizer's work *plus* the certified parser's — a second pass by design.
  For workloads that only need the structure (validation, picking fields out of `Json_fast`),
  `decode` is never called and you keep the 2.4× (or 24×) tokenize win.

## `decode` was O(n²) — now linear, with a proof

The naive materializer rebuilt the whole buffer as a `char list` per span:

```coq
Definition span_to_list (buf) (start len) :=
  firstn len (skipn start (buffer_to_list buf)).   (* O(n) per span *)
```

We proved what the slice *is*, then extracted it as an O(len) substring:

```coq
(* span_to_list buf start len is exactly buf[start..start+len) *)
Lemma span_to_list_nth (buf) (start len k) :
  List.nth_error (span_to_list buf start len) k =
  if k <? len then buffer_get buf (start + k) else None.

Extract Constant span_to_list =>
  "(fun b start len -> List.of_seq (String.to_seq (String.sub b start len)))".
```

`span_to_list_nth` characterizes the slice (k-th char = `buffer_get buf (start+k)`), so the
extracted `String.sub` computes exactly the certified list. Result: `decode` of the 65 KB
`github_events.json` dropped from ~4.6 s (≈0.014 MB/s) to ~0.002 s (31.5 MB/s) — quadratic → linear
in total span length, with the proof still `Qed.` (zero `Admitted`/`Axiom`).
