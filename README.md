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
| `theories/Chunked.v` | HTTP/1.1 chunked transfer coding (S6): value-dependent `Exactly n` grammar, soundness + completeness, linear-time decoder, extraction |
| `theories/*.v` | earlier stages (AnBn, Smoke, Example, Fence, FenceCompile) |
| `docs/` | research plan + implementation plan |
| `slides/json/` | Slidev deck (dark): BNF, approach, types, benchmark results |
| `slides/http/` | Slidev deck (dark): declarative value-dependent grammar, soundness/completeness, benchmark |

## Build

```bash
nix develop --command make
```

The flake pins **Rocq 9.1.1** — a bare `make` resolves to the wrong Rocq (opam 9.0.1).

## Status

- **Soundness — certified.** JSON (`parse_all_sound`, `parse_json_sound`) and HTTP chunked (`parse_chunk_sound`, `parse_chunked_body_sound`) are all `Qed.` — the parser only ever produces real denotations.
- **Completeness — certified.** The converse `denote → parse` holds for both: JSON (`parse_json_complete`) and HTTP chunked (`parse_chunk_complete`, `parse_body_complete`, `parse_chunked_body_complete`).
- **Extraction — works.** `parse_json` and `parse_chunked_body` extract to self-contained OCaml. With extraction directives (`nat`/`Z` → Zarith `Z.t`, `ascii` → `char`, `Z.of_nat` → identity), `parse_json` parses 4.75 MB in ~0.16 s (~30 MB/s); `parse_chunked_body` decodes ~10–13 MB/s (linear).

## Slides

```bash
cd slides/json && npm install && npm run dev    # JSON deck
cd slides/http && npm install && npm run dev   # HTTP deck
npm run export       # slides-export.pdf (either deck)
```
