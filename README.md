# parsebot

**Inhabited Parsing** — synthesizing certified parsing algorithms from declarative grammars, verified in [Rocq](https://rocq-prover.org) (the Coq proof assistant).

## The core idea

A grammar is a **data structure**; a parser is a **function**; the proof that they agree is a **derivation** that *is* the parse.

The innovation: the *implementation* and the *certification proof* can both be produced by **AI** — from the **BNF** *plus explicit disambiguation decisions* (the BNF is relational/unordered; ordered choice, lookahead, and the ambiguity policy are separate declarative decisions).

## What's here

| path | contents |
| --- | --- |
| `theories/Spec.v` | the deep-embedded specification calculus: `Spec` (combinators), `Grammar`, `denote` (proof-relevant denotation), `Progress`, and the compositional `denote_*_iff` laws |
| `theories/Json.v` | JSON as the "control" grammar (S5): the RFC-8259 grammar, a fuel-bounded recursive-descent parser, soundness (`parse_all_sound`, `parse_json_sound`), and extraction |
| `theories/*.v` | earlier stages (AnBn, Smoke, Example, Fence, FenceCompile) |
| `docs/` | research plan + implementation plan |
| `slides/json/` | Slidev deck (dark): BNF, approach, types, benchmark results |
| `json.ml` | extracted, self-contained OCaml parser |

## Build

```bash
nix develop --command make
```

The flake pins **Rocq 9.1.1** — a bare `make` resolves to the wrong Rocq (opam 9.0.1).

## Status

- **Soundness — certified.** `parse_all_sound` (7-way mutual) and `parse_json_sound` are all `Qed.` — the parser only ever produces real denotations.
- **Completeness — scoped.** The converse `denote → parse` is *not* a free mirror: the predictive parser's `}`/`]` lookahead is stricter than the grammar's `ε` branches (`members`/`elements`), so it needs a context-aware proof plus a ws-absorption lemma.
- **Extraction — works.** `parse_json` extracts to self-contained OCaml. With extraction directives (`nat`/`Z` → Zarith `Z.t`, `ascii` → `char`, `Z.of_nat` → identity) it parses a 4.75 MB JSON file in ~0.16 s (~30 MB/s) — ~1000× faster than the naive extraction.

## Slides

```bash
cd slides/json && npm install
npm run dev          # interactive
npm run export       # slides-export.pdf
```
