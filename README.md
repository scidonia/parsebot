# parsebot

**Inhabited Parsing** — synthesizing certified parsing algorithms from declarative grammars, verified in [Rocq](https://rocq-prover.org) (the Coq proof assistant).

## The core idea

A grammar is a **data structure**; a parser is a **function**; the proof that they agree is a **derivation** that *is* the parse.

The innovation: the *implementation* and the *certification proof* can both be produced by **AI** — from the **BNF** *plus explicit disambiguation decisions* (the BNF is relational/unordered; ordered choice, lookahead, and the ambiguity policy are separate declarative decisions).

## What's here

| path | contents |
| --- | --- |
| `theories/Spec.v` | the deep-embedded specification calculus: `Spec` (combinators), `Grammar`, `denote` (proof-relevant denotation), `Progress`, and the compositional `denote_*_iff` laws |
| `theories/Json.v` | JSON as the "control" grammar (S5): RFC-8259 grammar, fuel-bounded recursive-descent parser, soundness + completeness, extraction |
| `theories/JsonFast.v` | zero-copy JSON tokenizer: `parse_json_fast : buffer → option Json_fast` records `(start,len)` spans for strings/numbers; `parse_json_fast_correct` proves it refines `parse_json` via `decode`; extraction (`buffer → string`) |
| `theories/Chunked.v` | HTTP/1.1 chunked transfer coding (S6): value-dependent `Exactly n` grammar, soundness + completeness, linear-time decoder, extraction |
| `theories/Toml.v` | TOML (S8): integer scalars, dotted keys, tables, arrays-of-tables — surface parser *and* document state machine, soundness + completeness (the `ws1`-separator disambiguation), extraction |
| `theories/*.v` | earlier stages (AnBn, Smoke, Example, Fence, FenceCompile) |
| `docs/` | research plan + implementation plan |
| `slides/json/` | Slidev deck (dark): BNF, approach, types, benchmark results |
| `slides/http/` | Slidev deck (dark): declarative value-dependent grammar, soundness/completeness, benchmark |
| `slides/toml/` | Slidev deck (dark): specification, the `ws1` disambiguation decision, structure, benchmarks |

## Build

```bash
nix develop --command make
```

The flake pins **Rocq 9.1.1** — a bare `make` resolves to the wrong Rocq (opam 9.0.1).

## Status

- **Soundness — certified.** JSON (`parse_all_sound`, `parse_json_sound`), HTTP chunked (`parse_chunk_sound`, `parse_chunked_body_sound`), and TOML (`parse_doc_sound`, `step_spec_sound`, `direct_parse_equiv`, `parse_then_validate_iff_direct`) are all `Qed.` — the parser only ever produces real denotations.
- **Completeness — certified.** The converse `denote → parse` holds everywhere: JSON (`parse_json_complete`), HTTP chunked (`parse_chunk_complete`, `parse_body_complete`, `parse_chunked_body_complete`), and TOML (`key_complete`, `stmt_complete`, `doc_complete`). For TOML this is what the **one-or-more-`ws` statement separator** buys: it forces maximal-munch on the trailing integer, making the greedy parser agree with the relation.
- **Extraction — works.** `parse_json`, `parse_chunked_body`, and TOML's `parse_doc`/`parse_then_validate`/`direct_parse` extract to self-contained OCaml (extraction directives: `nat`/`Z` → Zarith `Z.t`, `ascii` → `char`, `Z.of_nat` → identity).
- **Refinement — certified.** The zero-copy JSON tokenizer is not re-proven against the grammar; it is proven to *agree* with the already-certified `parse_json` on every input (`parse_json_fast_correct : parse_json_fast (Buf l) = Some v → parse_json l = Some (decode (Buf l) v)`, plus the `None` branch) via a 7-way mutual simulation `parse_fast_sim`. The `decode` slice is characterized by `span_to_list_nth` and extracted to an `O(len)` `String.sub`. All `Qed.` — zero `Admitted`/`Axiom`.

## Benchmark

Extracted parsers are compiled with `ocamlfind ocamlopt -package zarith` against a hand-written `Big_int_Z.ml` shim (Zarith-backed). Drivers: `bench_driver.ml` (JSON), `bench_http.ml` (chunked), `bench_toml.ml` (TOML), `bench_json_fast.ml` (zero-copy JSON); generators in `bench_data/`; full results in `bench_results.md`.

- `parse_json` parses 4.75 MB in ~0.16 s (**~30 MB/s**); `parse_chunked_body` decodes ~10–13 MB/s (linear).
- **Zero-copy `parse_json_fast`** tokenizes at a **2.43× geometric mean** over the list-based `parse_json` (range 1.16×–24.4× on 13 files); **24.4×** on `gsoc-2018.json` (3.3 MB, 1 264 nested objects) — span-recording skips `Z`-arithmetic and `char list` building. `decode` (materialization) is a separate linear pass via an extracted `String.sub` slice.
- TOML `parse_doc` (surface parser) is linear — **~20–30 MB/s** on synthetic flat documents, on par with JSON.
- TOML `parse_then_validate` / `direct_parse` fold the flat-namespace state machine, whose `lookup : list (key × kind) → key → option kind` is a linear scan — **O(n²)** in the number of statements (a limitation of the naive *certified* `run`, not of extraction).

## Slides

```bash
cd slides/json && npm install && npm run dev      # JSON deck
cd slides/json-fast && npm install && npm run dev # zero-copy JSON deck (speedup + refinement proof)
cd slides/http && npm install && npm run dev     # HTTP deck
cd slides/toml && npm install && npm run dev     # TOML deck
npm run export       # slides-export.pdf (either deck)
```
