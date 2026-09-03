# Inhabited Parsing — Implementation Plan (First Steps)

**Status:** working; turns `inhabited-parsing-research-plan.md` (RP) into an ordered, verifiable step series.
**Date:** 2 September 2026

## 0. Positioning

- **Standalone.** No code reuse from LernaSpec, specsaver, DimSum, Narcissus or any other system. This project builds its own core.
- **Literature is for pinning formulations, not copying.** Where a prior system already has the exact type or theorem we need, we cite it and write our own.
- **Scope of this doc:** the first steps (S1–S4). Later steps are listed (§2) and elaborated when we reach them.
- **Every stage ships a runnable example.** Each step's deliverable includes a concrete, executable demonstration — a `theories/*.v` file whose progress is visible as `Eval compute` output (a `Dec` verdict, a `denote` derivation, a generated plan) — never definitions and theorems alone. The example is the stage's acceptance gate: no visible example, stage not done.

## 1. What the steps must demonstrate

One sentence: a declarative grammar is a specification whose algorithmic inhabitant is a **certified parser plan**, not merely a parse tree.

Three layers, in order (RP §1):

1. **Per-input inhabitation** — `Accepts S x a : Type`; an inhabitant is a derivation (RP §1.1).
2. **Algorithm inhabitation** — `parse : (x : Input) -> Dec (Σ a, Accepts S x a)`; totality makes termination implicit (RP §1.2).
3. **Plan inhabitation** — `Σ p : ParserPlan, Exact p S × Terminates p × AmbiguityPolicy p × ResourceBound p` (RP §1.3).

The step series climbs these layers, then walks the case-study ladder (RP §6).

## 2. Step series

| # | Step | Demonstrates (RP §) | Formal target | Literature anchor | Acceptance | Example |
|---|---|---|---|---|---|---|
| S0 | Toolchain | — | Rocq 9.1 + stdpp | — | `nix develop`; `make` compiles (done) | `theories/Smoke.v` compiles |
| S1 | Hand-written certified recogniser, tiny CFG (`a^n b^n`) | §1.1–1.2, WP1 | `parse : (x : Input) -> Dec (AnBn x 0 (length x))` | Gross–Chlipala | total, kernel-checked, index-based | `theories/AnBn.v` — `Eval compute in parse [A;A;B;B]` → `yes` |
| S2 | Deep-embedded `Spec` + proof-relevant `denote` | §4.1, WP2 | `denote : Grammar Γ N -> Spec Γ N A -> Γ -> nat -> A -> Γ -> nat -> Type` | Krishnaswami–Yallop; Narcissus | compositional laws proved | `theories/Example.v` — `d_ab : denote no_nts [A;B] ab_spec tt 0 (A,B) tt 2` |
| S3 | CommonMark fence fragment | §12, §6.2 | `CodeBlock = Bind FenceOpen (fun o => linesUntil (FenceClose o))` | — | §12 success criteria | `theories/Fence.v` — scanner on a fenced block, delimiter-match proof |
| S4 | First synthesised plan | §5, §1.3, WP3 | `compile : Spec Γ A -> Searchable S -> Dec (Σ p, Implements p S)` | Vermillion | ≥1 plan synthesised (§14) | `theories/FenceCompile.v` — `Eval compute (compile CodeBlock)` yields a plan |
| S5 | JSON control + two plans + extraction | §6.1, WP3 | ABNF → `Spec`; two certified plans | — | two distinct plans, OCaml extraction | `theories/Json.v` — extracted `json_parser` on RFC 8259 examples |
| S6 | HTTP/1.1 chunked | §6.3, WP4 | `Bind HexNatural (fun n => Exactly n Octet)` | Narcissus | §6.3 theorems | `theories/Chunked.v` — decodes a chunked body, framing proof |
| S7 | Haskell layout | §6.4, WP4 | `Layout : RawTokens -> ExplicitTokens -> Type` | — | layout ↔ explicit equivalence | `theories/Layout.v` — transduces a `let`/`where` fragment |
| S8 | TOML key/table state | §6.5, WP5 | `DocumentStep : Namespace -> Statement -> Namespace -> Type` | — | duplicate-key/table portions of toml-test | `theories/Toml.v` — toml-test duplicate-key subset |
| S9 | (stretch) C `typedef` | §6.6 | scoped name classification | — | scoped-classification proof | `theories/Typedef.v` — classifies a scoped fragment |

## 3. First steps in detail

### S1 — Hand-written certified recogniser for a tiny CFG

**Objective.** Establish the `Dec (Σ …)` shape end-to-end with zero synthesis machinery.

**Grammar.** `a^n b^n` over a two-token alphabet `{A, B}`. Non-regular (the canonical non-regular CFG), unambiguous, and the minimal grammar whose parser must decide `ε` vs. `a S b` — which is where the empty-segment check and index handling first appear.

**Formal target (index-based; the shape S2's `denote` will follow):**

```text
Token : Type                      (* A | B *)
Input := list Token

AnBn : Input -> nat -> nat -> Type        (* w[i .. j) is balanced *)
(* AB_nil  : AnBn w i i
   AB_cons : tok w i = Some A -> AnBn w (S i) j -> tok w j = Some B
             -> AnBn w i (S j) *)

parse : (x : Input) -> Dec (AnBn x 0 (length x))
```

**Rocq work.**

1. Define `Token`, `Input`, `tok w i := nth_error w i`.
2. Define `AnBn` as the index-based segment relation (two rules: `AB_nil`, `AB_cons`).
3. Write `parse_ab w i j : Dec (AnBn w i j)` by **structural recursion on the end index `j`** — positions are concrete `S`-stacks, so no `+` arithmetic appears in the recogniser. The `ε`-vs-`a S b` choice is a single `Nat.eq_dec i (S j')`.
4. Provide computable negative evidence: four short inversion lemmas (empty-impossible, first-not-`A`, last-not-`B`, inner-rejected).
5. `parse` is the whole-input instance; no separate soundness/completeness theorems — the `Dec` return type *is* both.

**Literature.** Gross & Chlipala, *Parsing Parses*, central parser type returns a parse tree or a proof none exists; the `Dec (AnBn …)` form collapses their two theorems into one type.

**Acceptance.** Kernel accepts `parse` (total). `Eval compute in parse [...]` returns the expected constructor on `[]`, `[A;A;B;B]`, and rejects `[A;B;A;B]`, `[A;B;B]`.

**Example.** `theories/AnBn.v` — `Eval compute in parse [A;A;B;B]` returns `yes (AB_cons …)`, and `parse [A;B;A;B]` returns `no (…)`. The stage's visible progress is a total decision procedure with concrete verdicts.

### S2 — Deep-embedded `Spec` + proof-relevant `denote`

**Objective.** The declarative core (RP §4.1) as a deep embedding with proof-relevant denotation.

**Two decisions to lock first.**

1. **Recursion (in `Spec` from the start).** RP §4.1's combinator list omits recursion, but JSON (S5) needs it and S3's fence blocks benefit from named nonterminals. The obvious `Rec : (Spec Γ A -> Spec Γ A) -> Spec Γ A` is rejected by Coq's strict-positivity check (negative occurrence in the domain). Resolution: a grammar is a **finite map of named nonterminals** — `Grammar Γ N := ∀ A, N A -> Spec Γ N A` — and `Spec` carries a reference node `Call : N A -> Spec Γ N A`. `denote` unfolds `Call n` by looking up `n` in the production map. This is exactly RP §1.1's `Derives : Grammar -> Nonterminal -> Input -> Output -> Type` (a system of equations), so it is the faithful reading, not a workaround. `denote` is therefore an **inductive relation** parameterised by the grammar, not a `Fixpoint` over a self-referential term.
2. **Cursor representation.** `Cursor := nat` (position into the shared `input : list Token`), from the start. Matches RP §1.2's `Recognises S γ i a γ' j` and §4.1's `denote … Cursor …`. Required later for memo keys `(nonterminal, position)` (RP §3) and cost/streaming (§5.2); adopting now avoids a rewrite. Cost: termination via measures/indices, not structural recursion on a shrinking list.

**Formal target (schematic):**

```text
Inductive Spec (Γ : Type) (N : Type -> Type) : Type -> Type :=
  | Pure  : A -> Spec Γ N A
  | Fail  : Spec Γ N A
  | Tok   : (Token -> Type) -> Spec Γ N Token
  | Seq   : Spec Γ N A -> Spec Γ N B -> Spec Γ N (A × B)
  | Alt   : Spec Γ N A -> Spec Γ N A -> Spec Γ N A
  | Map   : (A -> B) -> Spec Γ N A -> Spec Γ N B
  | Bind  : Spec Γ N A -> (A -> Spec Γ N B) -> Spec Γ N B
  | Guard : (A -> Type) -> Spec Γ N A -> Spec Γ N A
  | Many  : Progress S -> Spec Γ N A -> Spec Γ N (List A)
  | Get   : Spec Γ N Γ
  | Put   : Γ -> Spec Γ N unit
  | Local : Spec Γ N A -> Spec Γ N A
  | Call  : N A -> Spec Γ N A.          (* nonterminal reference *)

Grammar Γ N := ∀ A, N A -> Spec Γ N A      (* the production map *)

denote : Grammar Γ N -> Spec Γ N A -> Γ -> nat -> A -> Γ -> nat -> Type
(* denote G S γ i a γ' j : derivations showing S, begun in γ at position i,
   produces a and finishes in γ' at j (RP §4.1); inductive, unfolds Call n
   to G A n. Cursor := nat from the start. *)
```

**Rocq work.**

1. Define `Spec`, `Cursor`, `denote` (proof-relevant).
2. Prove one compositional law per combinator, e.g. `denote (Seq s1 s2) γ i (a,b) γ'' j ↔ ∃ γ' j', denote s1 γ i a γ' j' × denote s2 γ' j' b γ'' j`.
3. Define `Progress S` — the predicate that `S` consumes input, needed for `Many` termination and later for `Searchable` (RP §4.2).

**Literature.** Krishnaswami & Yallop for the grammar-expression discipline; Narcissus for `Bind` + environment (`Get`/`Put`/`Local`) in a relational spec.

**Acceptance.** `denote` laws kernel-checked; the fence fragment's `FenceOpen`/`FenceClose` relations stated and typechecking as `Spec` terms.

**Example.** `theories/Example.v` — the two-token grammar `A B` as a `Spec`, with hand-built derivation `d_ab : denote no_nts [A;B] ab_spec tt 0 (A,B) tt 2`, reducing to `d_seq (d_tok …) (d_tok …)`. Makes "parsing = proof search for a `denote` inhabitant" visible.

### S3 — CommonMark fence fragment (first discriminating experiment)

**Objective.** Value-indexed nonterminals via `Bind`; prove a scanner sound and complete. This is RP §12's experiment, done as the first *technical* demonstration.

**Formal target (RP §6.2):**

```text
FenceOpen : Σ c : {Backtick, Tilde}, Σ n : Nat, n >= 3
FenceClose (c, n) : Σ m : Nat, m >= n
CodeBlock : Bind FenceOpen (fun (c, n) => linesUntil (FenceClose (c, n)))
```

**Rocq work (RP §12 steps 1–4).**

1. Line-oriented input model.
2. Encode opener, closer, content collection, indentation removal as relations over `Spec` (`Bind`, `Many`, `Tok`, `Guard`).
3. Write a direct scanner plan parameterised by the opening-fence witness.
4. Prove sound + complete: `scanner x = Some a ↔ ∃ d, denote CodeBlock … x … a …`.

**Acceptance (RP §12 success criteria).**

- pass the official CommonMark fenced-block examples for the isolated fragment;
- prove closing-character equality and the fence-length inequality;
- prove content stripping matches the opening-indentation rule;
- single pass, no speculative backtracking across the block body.

The scanner here is hand-written; S4 makes it generated.

**Example.** `theories/Fence.v` — run the scanner on a concrete fenced block; it returns the parsed block and its closing-delimiter/fence-length proof, and rejects a mismatched closer.

### S4 — First synthesised plan

**Objective.** Turn the S3 scanner into a *generated* plan plus a kernel-checkable refinement proof.

**Formal target (schematic; RP §1.3, §5):**

```text
ParserPlan : Type                          (* small executable strategy; §5 subset *)
Implements : ParserPlan -> Spec Γ A -> Type    (* plan refines spec *)
compile : (S : Spec Γ A) -> Searchable S -> Dec (Σ p : ParserPlan, Implements p S)
```

**Plan subset for the fence fragment** (from RP §5): `ReadToken`, `ConsumeExactly n`, `ParseValueThen valueDependentPlan`, `Return`, plus a `Repeat measure` node for `linesUntil`.

**Rocq work.**

1. Define the `ParserPlan` subset and its operational semantics (small-step or direct interpreter).
2. Define `Implements p S := ∀ γ x, plan_result p x ⊆ denote S x` (result/trace refinement).
3. Define `Searchable S` — compositional admissibility (RP §4.2): finite branching, decidable guards, `Progress`, effective ambiguity policy, computable negative evidence.
4. Write `compile` by proof search: one local refinement theorem per `Spec` constructor (RP §5); discharge side obligations.
5. Prove the fence scanner is exactly what `compile` returns for `CodeBlock`.

**Acceptance (RP §14 decision criteria).**

- the fragment spec remains visibly declarative;
- at least one specialised plan is synthesised, not hand-written;
- soundness and rejection-completeness are kernel-checked;
- side conditions are discharged compositionally, not bespoke.

`Requirements`/`Satisfies` (RP §1.3) and cost semantics (RP §5.2) are deferred to S6 (HTTP streaming), not needed here.

**Example.** `theories/FenceCompile.v` — `Eval compute in (compile CodeBlock)` yields a plan, and the S3 input is accepted by the *generated* scanner rather than the hand-written one.

## 4. Decisions locked before S2 code

1. **`Dec` encoding** — `sumbool` (`{P} + {~P}`), matching Gross–Chlipala and giving extraction-friendly booleans + proofs.
2. **Cursor** — `nat` positions into a shared `input : list Token`, from the start (RP §1.2/§4.1 form).
3. **Recursion** — named nonterminals + `Call` node + a production map (`Grammar Γ N`), the RP §1.1 system-of-equations form; `denote` is an inductive relation that unfolds `Call`. The naive `Rec : (Spec -> Spec) -> Spec` is rejected by strict positivity.
4. **Ambiguity mode (RP §4.3)** — first prototypes use **Recognition** (one derivation or refutation). `Alt` stays relational/unordered at the spec layer; ordered choice is a plan-level decision (RP §4.1).
5. **Extraction (RP §8.4)** — OCaml, introduced at S5 (JSON); S1–S4 are proof-only.

## 5. Immediate next action

Start S3: `theories/Fence.v` — the fence fragment scanner + soundness/completeness, with its `Eval compute` example as the stage's acceptance gate. (S0–S2 and their examples — `Smoke.v`, `AnBn.v`, `Example.v` — are done.)
