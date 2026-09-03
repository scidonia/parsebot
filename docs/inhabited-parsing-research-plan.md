# Inhabited Parsing

## A research plan for synthesising certified algorithms from declarative grammars

**Status:** working research hypothesis  
**Date:** 2 September 2026

## Executive summary

The project asks whether a declarative grammar can serve as a specification whose computational inhabitant is not merely a parse tree for one input, but a complete parsing algorithm with stated operational properties.

For a grammar or format specification `S`, an input `x`, and an output `a`, we define a proof-relevant relation:

```text
Accepts S x a : Type
```

An inhabitant of `Accepts S x a` is evidence that `a` is a legitimate interpretation of `x`. A total exact parser has the schematic type:

```text
parse : (x : Input) -> Dec (Σ a : Output, Accepts S x a)
```

where `Dec P` contains either an inhabitant of `P` or a refutation of `P`. The longer-term synthesis target is:

```text
compile : (S : Spec) -> Searchable S -> CertifiedParser S
```

or, when operational requirements are included:

```text
synthesise : (S : Spec) -> (R : Requirements S) ->
             Dec (Σ p : ParserPlan, Implements p S × Satisfies p R)
```

The foundational idea is established rather than novel. Gross and Chlipala constructed a sound and complete dependently typed parser for arbitrary context-free grammars in Coq with essentially the first type above. Vermillion generates verified LL(1) parsers, and Narcissus derives correct encoders and decoders from relational binary-format descriptions.

The proposed contribution is the next layer:

1. a small declarative calculus covering ordinary context-free structure together with bounded data dependence, layout, and evolving environments;
2. a separate calculus of executable parser plans;
3. proof-producing synthesis or refinement from the first calculus to the second;
4. explicit inhabitation requirements for termination, ambiguity policy, streaming behaviour, memory and time;
5. evaluation on small but genuinely awkward fragments of real specifications.

The central hypothesis is that many formats that become procedural or ad hoc in PEG/packrat systems have concise relational specifications, and that their algorithms can be found by composing a manageable library of certified parsing strategies.

## 1. The precise research claim

### 1.1 Per-input inhabitation

A conventional grammar defines a language. A proof-relevant grammar defines a family of witness types:

```text
Derives : Grammar -> Nonterminal -> Input -> Output -> Type
```

For fixed `G`, `A`, `x`, and `a`, a value of:

```text
Derives G A x a
```

is simultaneously:

- a derivation tree;
- evidence that `x` is admitted by the grammar;
- evidence that `a` is an allowed semantic result.

This is per-input inhabitation. Parsing is constructive proof search for such an inhabitant.

### 1.2 Algorithm inhabitation

The more important object is uniform in the input:

```text
CertifiedParser S := (x : Input) -> Dec (Σ a, Accepts S x a)
```

An inhabitant of `CertifiedParser S` decides the specification on every input. In a total type theory, termination is implicit in the existence of the term. Soundness and rejection completeness follow from its result type.

For a practical partial-input parser, the relation should expose the remaining input:

```text
Recognises S γ i a γ' j : Type
```

This says that, starting in grammatical environment `γ` at cursor `i`, specification `S` produces `a`, finishes with environment `γ'`, and stops at cursor `j`. A whole-input parser additionally proves `j = length(input)` and the required final-state condition.

The explicit environment is important. It accommodates layout stacks, already-defined names, delimiter parameters, and similar dependencies without pretending that they are ordinary context-free productions.

### 1.3 Plan inhabitation

A correct parser function is still not necessarily an acceptable implementation. The research object should therefore be a dependent pair:

```text
Σ plan : ParserPlan,
    Exact plan S
  × Terminates plan
  × AmbiguityPolicy plan policy
  × ResourceBound plan budget
```

Here `ParserPlan` is an executable strategy: predictive descent, chart parsing, state-indexed memoisation, direct length consumption, layout transduction, or a composition of these.

This is the formulation that transfers to query planning. A parse tree is the witness for one instance; a certified parser plan is the reusable algorithmic inhabitant of the declarative specification.

## 2. What is and is not novel

The project should not claim that dependent types make certified parsing possible. Several strong results already exist:

- **Parsing Parses** implements a functional parser for arbitrary CFGs in Coq with soundness and completeness. Its central parser type returns either a parse-tree inhabitant or a proof that none exists.
- **Vermillion** generates LL(1) parsers proved sound, complete and terminating without fuel.
- **A Typed, Algebraic Approach to Parsing** uses a type system for context-free expressions from whose typing derivations predictive parsers can be read off.
- **Dependently Typed Grammars** represents productions and their semantic actions together and verifies grammar transformations in Agda.
- **Narcissus** takes relational binary-format specifications and uses proof search to derive correct encoders and decoders, including data-dependent network formats.
- **TRX** provides a verified interpreter for well-formed parsing-expression grammars.

Therefore the minimum defensible novelty claim is:

> A common proof-relevant specification and parser-plan framework for ordinary, data-dependent, layout-dependent and environment-dependent parsing, with proof-producing strategy selection and explicit operational requirements.

Even this claim must be tested against systems such as Narcissus, PADS-style data-description languages, verified parser combinators, EverParse/3D, and specialised indentation-sensitive parsing systems. The first research output should be a careful feature and theorem comparison, not an implementation announcement.

## 3. Why packrat is a useful foil—but not a straw man

Packrat parsing memoises results by something like:

```text
(nonterminal, input position)
```

For a pure PEG, this supports deterministic ordered choice and the familiar linear-time argument. The real-world cases below are not necessarily impossible to implement with a packrat library. Instead, they tend to require one of the following:

- a semantic predicate or monadic bind whose result depends on a value parsed earlier;
- a preprocessing pass that is outside the grammar;
- mutable or inherited state;
- an enlarged memoisation key such as `(nonterminal, position, environment)`;
- procedural code whose relationship to the declarative format must be proved separately;
- an ordered-choice interpretation that does not represent all derivations of an ambiguous declarative grammar.

If the environment has unboundedly many possible values at one position, classic packrat memoisation no longer gives a simple linear bound. Conversely, if a format is made easy by a deterministic preprocessing pass, that is not a failure: the preprocessor itself is a candidate certified plan stage.

The project should consequently make the narrower claim that these examples do not fit *cleanly into a pure, position-indexed PEG with the standard packrat story*. They remain perfectly parseable by extended PEGs, staged parsers, parser combinators or hand-written code.

## 4. Proposed declarative core

### 4.1 Relational semantics

Use a deep embedding with a proof-relevant denotation:

```text
denote : Spec Γ A -> Γ -> Cursor -> A -> Γ -> Cursor -> Type
```

`denote S γ i a γ' j` is the type of derivations showing that `S`, begun in context `γ` at `i`, may produce `a` and finish in `γ'` at `j`.

The initial core should contain:

```text
pure       : A -> Spec Γ A
fail       : Spec Γ A
token      : (Token -> Type) -> Spec Γ Token
sequence   : Spec Γ A -> Spec Γ B -> Spec Γ (A × B)
choice     : Spec Γ A -> Spec Γ A -> Spec Γ A
map        : (A -> B) -> Spec Γ A -> Spec Γ B
bind       : Spec Γ A -> (A -> Spec Γ B) -> Spec Γ B
guard      : (A -> Type) -> Spec Γ A -> Spec Γ A
many       : Progress S -> Spec Γ A -> Spec Γ (List A)
getContext : Spec Γ Γ
putContext : Γ -> Spec Γ Unit
local      : Spec Γ A -> Spec Γ A
```

`choice` at the specification layer is relational and unordered. Ordered choice, cuts, lookahead and memoisation belong to parser plans because they are execution decisions. This separation avoids silently changing a declarative language into PEG semantics.

`bind` expresses value dependence. For example:

```text
chunk := bind hexNatural (fun n => exactly n octets)
```

`guard` carries a decidable proposition at execution time but denotes the proposition itself. The elaborator should require or generate a `Decidable` witness before compilation.

### 4.2 Controlled expressiveness

Unrestricted `bind`, arbitrary predicates and arbitrary state can encode computations for which exact parsing is undecidable. The grammar language therefore needs a separate admissibility judgement:

```text
Searchable : Spec Γ A -> Type
```

Evidence for `Searchable S` should establish enough of the following:

- finite branching at every search point;
- decidable terminals and guards;
- well-founded recursive calls;
- progress for repetitions;
- finite or finitely representable relevant contexts;
- an ambiguity policy with an effective representation;
- computable negative evidence.

The key research question is whether this evidence can be assembled compositionally. If `Searchable` degenerates into a bespoke termination and completeness proof for every grammar, the approach has not succeeded.

### 4.3 Ambiguity as a declared output policy

The API should not hide ambiguity. Support four explicit modes:

| Mode | Required result |
| --- | --- |
| Recognition | One derivation or a refutation |
| Canonical parse | One derivation plus proof that it satisfies a declared selection relation |
| All parses | A finite or shared parse forest complete for all derivations |
| Unambiguous | One derivation plus proof that no distinct derivation exists; ambiguity is an error |

Nullable cycles can create infinitely many derivation trees for one finite input. The first prototype should either reject these grammars or quotient derivations by a declared equivalence. Cyclic shared forests are a later extension.

### 4.4 Operational policies must be separate from language meaning

Resource limits should not silently alter the accepted language. For example, RFC 9112 permits chunk sizes too large for a fixed-width machine integer. A deployed parser may impose a size limit, but the result should say either:

```text
Malformed proof
```

or:

```text
ValidButOutsidePolicy proof
```

rather than confusing policy rejection with grammatical rejection. This distinction is particularly valuable for secure protocol parsers.

## 5. Proposed parser-plan calculus

The plan language should be small and explicitly operational. Candidate nodes include:

```text
ReadToken
Call nonterminal
Predict table
Branch discriminator
Split candidates
Chart item
Memo key
ParseValueThen valueDependentPlan
ConsumeExactly n
TransformLayout stackPolicy
UpdateEnvironment delta
Loop measure
Return
```

Each constructor has a local refinement theorem. Plan synthesis then becomes proof search over these theorems.

The initial compiler should not try to discover arbitrary programs. It should:

1. normalise a specification;
2. infer nullable/first/follow and data-dependency information;
3. select a known strategy for each region;
4. emit side obligations;
5. discharge decidable and arithmetic obligations automatically;
6. return a plan and a kernel-checkable refinement proof.

This is analogous to query optimisation: the space of legal plans is generated by refinement rules; cost estimates choose among extensionally correct inhabitants.

### 5.1 Strategy library

An incremental library might contain:

- direct deterministic token consumption;
- LL(1) and precedence-climbing regions;
- general CFG fallback using Earley, GLL or GLR-style charts;
- packrat memoisation where the proof establishes an adequate finite key;
- dependent consumption for parsed lengths and delimiters;
- a certified layout-to-token transducer;
- finite-map environments for definitions and scopes;
- streaming buffers with explicit bounds.

The plan proof should permit mixed strategies. A Haskell fragment might first run a layout transducer and then use a deterministic grammar parser. HTTP chunked decoding might use ordinary token parsing for hexadecimal syntax and a specialised `ConsumeExactly n` plan for the body.

### 5.2 Cost and streaming

Correctness should be established before asymptotic cost. A later costed semantics can assign events such as token reads, table lookups, allocations and retained input slices. Desired theorem shapes include:

```text
Time plan x <= c₁ * length x + c₀
PeakBuffer plan x <= declaredLimit
```

For a streaming extension, parser execution can be represented as an interaction tree over events such as `Read`, `NeedMore`, `Emit`, and `Fail`. Refinement then relates observable traces to the pure whole-input relation. Interaction trees are useful here, but they need not be in the first trusted core.

## 6. Real-world case-study ladder

The cases are deliberately fragments, not heroic attempts to verify entire language implementations. Each isolates a different reason why a declarative specification and an execution plan diverge.

| Stage | Specification fragment | Dependency | Why pure packrat is awkward | Intended witness |
| --- | --- | --- | --- | --- |
| 0 | JSON (RFC 8259) | Ordinary recursive syntax | It is not awkward; this is the control | JSON AST and ABNF derivation |
| 1 | CommonMark fenced code blocks | Opening delimiter determines closing delimiter | Closing test depends on captured character and unbounded fence length | Block, contents, delimiter-match proof |
| 2 | HTTP/1.1 chunked bodies (RFC 9112) | Parsed hexadecimal value determines byte count | Requires value-dependent sequencing and careful overflow policy | Decoded bytes and framing derivation |
| 3 | Haskell 2010 layout fragment | Indentation stack and syntactic context | Result depends on inherited layout state; preprocessing is conventional | Inserted-brace token stream and equivalence proof |
| 4 | TOML 1.0 keys and tables | Definitions accumulated across the document | Acceptance depends on an evolving namespace, not position alone | Configuration value and no-redefinition derivation |
| 5, stretch | C declaration/expression fragment with `typedef` | Scoped name classification | The same token is classified using prior declarations; memo key needs environment | AST and scoped-classification proof |

### 6.1 Stage 0: JSON as the control

Use the ABNF in [RFC 8259](https://www.rfc-editor.org/info/rfc8259/) as the ordinary grammar. JSON is small, recursive, widely implemented, and should require no dependent machinery beyond semantic actions.

Goals:

- elaborate ABNF into the core specification;
- derive a sound and rejection-complete parser;
- return a derivation-indexed JSON AST;
- compare deterministic, packrat and general-CFG plans;
- demonstrate proof erasure and extraction;
- distinguish RFC grammar acceptance from optional implementation limits.

This case is a sanity check. If the framework cannot make JSON nearly as simple as a conventional parser combinator library, the core calculus is too burdensome.

### 6.2 Stage 1: CommonMark fenced code blocks

The [CommonMark specification](https://spec.commonmark.org/spec.html#fenced-code-blocks) defines an opening fence using at least three identical backticks or tildes. A closing fence must use the same character and be at least as long as the opener. Opening indentation also controls removal of indentation from content lines.

A direct relational fragment is:

```text
FenceOpen  : Σ c : {Backtick, Tilde}, Σ n : Nat, n >= 3
FenceClose : (c, n) -> Σ m : Nat, m >= n
CodeBlock  : bind FenceOpen (fun opener =>
               linesUntil (FenceClose opener))
```

The true witness also records indentation transformation and the rule that an unmatched fence consumes to the end of its containing block.

Why it is useful:

- the dependency is local and easy to understand;
- official examples provide a ready-made conformance suite;
- a semantic predicate makes it implementable in a PEG, but the relation between predicate and prose rule is usually outside the grammar;
- it tests value-indexed nonterminals without introducing a large language.

Success criteria:

- pass all official fenced-block examples relevant to the isolated fragment;
- prove closing-character equality and the fence-length inequality;
- prove that content stripping matches the opening indentation rule;
- generate a single-pass plan without speculative backtracking across the block body.

### 6.3 Stage 2: HTTP/1.1 chunked transfer coding

[RFC 9112, section 7.1](https://www.rfc-editor.org/rfc/rfc9112.html#section-7.1) specifies each non-final chunk as a hexadecimal size, optional extensions, CRLF, exactly that many data octets, and another CRLF. A zero-sized chunk terminates the sequence and may be followed by trailers.

The essential dependent grammar is:

```text
Chunk := bind HexNatural (fun n =>
           if n = 0 then LastChunk
           else sequence (Exactly n Octet) CRLF)
```

This is a better test than an artificial length-prefixed toy because it is deployed, security-sensitive, streaming, and contains explicit warnings about integer overflow.

Desired theorems:

- every accepted chunk consumes exactly the length denoted by its unbounded hexadecimal field;
- concatenating returned chunk payloads gives the decoded content;
- the first zero chunk ends the chunk sequence;
- malformed framing is rejected with negative evidence;
- machine-size and deployment limits are represented as policy outcomes, not false claims of grammatical invalidity;
- the streaming implementation retains no input before the current chunk except explicitly requested output.

The comparison baseline should include a hand-written state machine and an extended parser-combinator implementation. Calling the latter “packrat” is secondary: the research question is whether the relational specification can generate the specialised state machine without duplicating the length rule procedurally.

### 6.4 Stage 3: Haskell layout

The [Haskell 2010 Report](https://www.haskell.org/definition/haskell2010.pdf), sections 2.7 and 10.3, defines layout by inserting virtual braces and semicolons according to indentation and syntactic context. The indentation of a lexeme after `where`, `let`, `do`, or `of` is remembered; subsequent indentation may continue an item, begin a sibling, or close one or more layout lists.

Treat layout initially as a certified relation between token streams:

```text
Layout : RawTokens -> ExplicitTokens -> Type
```

and synthesise:

```text
layout : (raw : RawTokens) ->
         Dec (Σ explicit, Layout raw explicit)
```

Then compose it with a parser for the explicit-brace grammar and prove:

```text
ParsesLaidOut raw ast <->
Σ explicit, Layout raw explicit × ParsesExplicit explicit ast
```

This case tests whether the framework treats preprocessing as a first-class certified plan rather than an informal escape hatch.

Scope control:

- start with nested `let` and `where` blocks;
- include explicit braces interacting with implicit layout;
- delay the full report’s parse-error-dependent insertion rule until the simpler stack algorithm is stable;
- do not attempt the complete Haskell grammar in the first project.

### 6.5 Stage 4: TOML key and table state

The [TOML 1.0 specification](https://toml.io/en/v1.0.0) has relatively simple local syntax but document-level validity conditions. A key may not be defined more than once; tables cannot generally be redefined; and dotted keys and table headers interact in stateful ways. The official [toml-test repository](https://github.com/toml-lang/toml-test) supplies a language-independent conformance suite.

Represent parsing and well-formed construction together:

```text
DocumentStep : Namespace -> Statement -> Namespace -> Type
Document     : List Statement -> Config -> Type
```

The namespace records whether each path is absent, an implicit table, an explicitly defined table, an array of tables, or a scalar value. Each accepted statement carries evidence that its transition is permitted.

This tests an important boundary: is “parsing” only tree construction followed by validation, or may the declarative language specify valid semantic objects directly? The project should support both decompositions and prove them equivalent:

```text
parseThenValidate input = success cfg
    <->
directParse input = success cfg
```

Why packrat is awkward rather than impossible:

- parsing the surface syntax is easy;
- exact document acceptance depends on the accumulated key/table environment;
- memoising only by source position is insufficient if validation is interleaved;
- separating validation is practical, but ordinarily leaves a second correctness boundary.

Success criteria:

- cover the duplicate-key, dotted-key and table-redefinition portions of `toml-test`;
- produce a configuration whose construction witnesses uniqueness and legal table evolution;
- compare direct state-indexed parsing with parse-then-certified-validation.

### 6.6 Stretch: C `typedef` classification

A small C fragment provides a scoped-name challenge. Whether an identifier behaves as a typedef name depends on earlier declarations and shadowing. The full C grammar is too large for this project, so the candidate fragment should contain only:

- block scopes;
- `typedef` declarations;
- variable declarations;
- pointer declarators;
- enough expressions to exhibit declaration/expression ambiguity.

The environment maps identifiers to classifications, and the derivation records each lookup. This is a stronger state-indexed memoisation test than TOML, but it is also substantially easier to scope incorrectly. It should be attempted only after the TOML case.

### 6.7 Optional binary stretch: DNS compressed names

DNS name compression replaces suffixes with offsets into earlier packet data. A correct decoder must interpret references and rule out invalid pointer behaviour. This is an excellent test of offset-dependent parsing but overlaps materially with Narcissus, whose relational format includes state specifically to cover DNS packets. It is best used as a comparative replication rather than a novelty case.

## 7. Research questions and falsifiable hypotheses

### RQ1: Expressiveness

Can one small relational calculus state all five principal cases without embedding arbitrary parser code?

**H1:** JSON, fenced blocks, chunked bodies, the selected layout fragment and TOML namespace rules can each be specified with the common combinators plus small decidable domain predicates.

**Failure condition:** a case requires a large opaque semantic action whose correctness is essentially the parser proof in disguise.

### RQ2: Compositional searchability

Can exact parser existence be reduced to local admissibility evidence?

**H2:** at least 80% of `Searchable` obligations in the case studies are discharged by reusable rules or decision procedures.

**Failure condition:** each new format needs a bespoke global completeness proof comparable in size to a hand verification.

### RQ3: Strategy synthesis

Can proof search select and compose specialised plans rather than merely interpret the specification?

**H3:** the tool automatically constructs mixed plans for the CommonMark, HTTP and Haskell cases from grammar annotations limited to ambiguity and resource policy.

**Failure condition:** users must write a near-complete algorithm as “hints”.

### RQ4: Operational competitiveness

Can proof-carrying generated parsers approach ordinary implementations?

**H4:** after proof erasure, generated parsers run within 2–5× of a good hand-written or mainstream combinator baseline on the selected fragments, with no asymptotic regression.

The constant-factor target is deliberately modest. Early verified parser systems have often paid factors in this range; the more important initial result is that dependent cases do not trigger uncontrolled memo-table or proof-term growth.

### RQ5: Change resilience

Does keeping semantics separate from plan improve maintenance?

**H5:** small specification mutations require local re-synthesis or local proof repair, while the extensional correctness statement remains unchanged.

Measure changed specification lines, changed plan code, regenerated proof size and manual intervention time.

### RQ6: Trust and independent checking

Can an untrusted synthesiser return compact evidence checked by a small kernel?

**H6:** all generated plan correctness is accepted by the ordinary Rocq kernel without extending the trusted base with solver code. External SAT/SMT results, if used, must be reconstructed or checked.

## 8. Implementation strategy

### 8.1 Proof assistant

Use Rocq for the first prototype because the most directly relevant precedents—Parsing Parses, Vermillion and Narcissus—are in Coq/Rocq, and because extraction provides a quick path to executable code. Keep the external grammar syntax and plan IR proof-assistant-neutral.

Agda may produce more elegant intrinsically typed prototypes, but adopting it first would make comparison and reuse harder. Iris is not required for the pure core. It may become useful only when reasoning about shared mutable buffers or concurrent streaming consumers.

### 8.2 Trusted base

The trusted base should be:

- the Rocq kernel;
- the formal semantics of the specification and plan calculi;
- the extraction or compilation path, explicitly identified as trusted or separately verified.

The grammar elaborator, optimiser, tactic code, cost model and any AI component may be untrusted if they produce checkable terms.

### 8.3 Role of AI

AI is plausible as a heuristic search controller, not as the source of truth. It may:

- translate prose or ABNF into candidate specifications;
- propose admissibility lemmas and invariants;
- select plan refinements;
- repair proofs after grammar changes;
- generate adversarial examples from uncovered branches.

Every accepted grammar translation still needs review against the normative source, and every algorithmic claim must reduce to kernel-checked evidence. The research should compare deterministic tactic search with AI-guided search rather than presuming that AI is necessary.

### 8.4 Extraction target

Start with extracted OCaml for rapid validation. A later backend may lower the plan IR to Rust or Wasm, but that adds a compiler-correctness problem and should not block evaluation of the central hypothesis.

## 9. Work plan

### WP1 — Baseline and novelty map (months 1–3)

- Reproduce the core `Dec (ParseTree ...)` result for a tiny CFG.
- Run or port representative examples from Parsing Parses and Narcissus.
- Compare theorem statements, format expressiveness, ambiguity, streaming and synthesis mechanisms across related systems.
- Freeze the novelty claim and identify reusable code.
- Formalise JSON as the control.

**Gate:** continue only if the proposed core adds a clearly identifiable capability beyond existing libraries.

### WP2 — Specification calculus (months 3–7)

- Define the deep embedding and proof-relevant semantics.
- Define dependent sequencing, guards, context transitions and progress.
- Define ambiguity policies.
- Prove compositional semantic laws and normalisation correctness.
- Provide a small external syntax and elaborator.

**Deliverable:** machine-checked specifications for JSON and the CommonMark fence fragment.

### WP3 — Certified plan calculus and baseline compiler (months 6–11)

- Define plan semantics and `Implements`.
- Implement direct, LL-style, memoised and general-CFG fallback strategies.
- Prove local refinement rules.
- Build proof-producing compilation for ordinary grammars.
- Extract executable parsers and establish the benchmark harness.

**Deliverable:** at least two distinct certified plans for JSON derived from the same specification.

### WP4 — Data and layout dependence (months 10–16)

- Add value-dependent consumption.
- Implement CommonMark fences and HTTP chunking.
- Add context-indexed transduction for Haskell layout.
- Prove correctness of mixed plans.
- Introduce explicit policy outcomes for limits and integer representation.

**Deliverable:** certified extracted parsers for the three fragments, with conformance and generated adversarial tests.

### WP5 — Stateful document validity (months 15–20)

- Add finite-map namespace reasoning.
- Implement the TOML key/table fragment.
- Compare direct parsing against parse-then-validation.
- Attempt the C typedef fragment if the core remains small.

**Deliverable:** evidence about when semantic state belongs inside the grammar and when staged validation is superior.

### WP6 — Cost, streaming and evaluation (months 18–24)

- Add a costed operational semantics for selected plan nodes.
- Add streaming HTTP execution, optionally via interaction trees.
- Benchmark throughput, allocations, retained input and proof checking.
- Run grammar-evolution experiments.
- Publish the case-study corpus, negative inputs and checked proofs.

## 10. Evaluation design

### 10.1 Correctness

- Kernel-check every generated refinement proof.
- Exhaustively enumerate short inputs for small fragments and compare relational membership with execution.
- Run official example or conformance suites where available.
- Differential-test outputs against at least two mature implementations when semantics are unambiguous.
- Mutation-test both grammars and plans to confirm that proof obligations fail when intended.

### 10.2 Specification quality

Record:

- specification lines excluding generated code;
- number and size of opaque predicates;
- manual annotations;
- manual lemmas;
- percentage of searchability and refinement obligations automated;
- whether normative prose appears exactly once or is duplicated between grammar and parser hints.

The last metric is central. If the HTTP length rule must be restated in the parser hint, the synthesis has not achieved the intended single source of truth.

### 10.3 Performance

Measure:

- parse throughput by input size;
- peak and total allocation;
- retained input for streaming parsers;
- parser generation time;
- proof construction and kernel-checking time;
- proof artefact size before and after compression;
- asymptotic behaviour under adversarial invalid input.

Baselines:

- a conventional packrat/PEG implementation where natural;
- a hand-written state machine for HTTP chunking;
- conventional layout preprocessing for Haskell;
- parse-then-validate for TOML;
- an existing general CFG parser for JSON variants.

A 2026 empirical comparison of general CFG parsers suggests RNGLR/BRNGLR as useful generalised-parser baselines and shows that grammar shape can reverse relative performance among algorithms. The project should therefore compare plans generated from the same denotation rather than assuming one grammar normal form is operationally neutral.

### 10.4 Evolution

For every case, prepare three small revisions:

- a syntax extension;
- a restriction;
- an operational policy change that must not change the language.

Measure re-synthesis success and proof repair. This directly tests the claimed benefit of separating declarative meaning from algorithmic inhabitant.

## 11. Risks and scope controls

### Risk 1: Rediscovering Narcissus

Narcissus already uses relational specifications, state and proof search to derive encoders and decoders for non-context-free network formats.

**Control:** make a theorem-level comparison in WP1. Reuse or extend Narcissus if its format relation and derivation architecture already cover the proposed core. Novelty may need to shift toward multi-strategy parser plans, textual layout/state, ambiguity, cost, or algorithm selection.

### Risk 2: An overexpressive specification language

General dependent relations do not have decidable inhabitation.

**Control:** keep denotation expressive but make `Searchable S` explicit. Define decidable, compositional fragments rather than claiming compilation for every relation.

### Risk 3: Hiding the algorithm in annotations

A “declarative” system can require hints so detailed that they are merely parser programs in disguise.

**Control:** count and publish annotations; require that semantic conditions occur only in the specification; compare annotation size with the generated plan.

### Risk 4: Conflating parsing, validation and interpretation

TOML and C intentionally blur these stages.

**Control:** formalise both staged and fused decompositions and prove equivalence where possible. Treat the decomposition itself as a plan choice.

### Risk 5: Overclaiming against packrat

All selected examples can be implemented using sufficiently extensible parser libraries.

**Control:** claim cleaner declarative statement, checked correspondence and compositional operational evidence—not impossibility of packrat implementation.

### Risk 6: Full-language case studies swallowing the project

Haskell, CommonMark, TOML and C are large specifications.

**Control:** verify named fragments with explicit boundaries. Prefer complete proofs of small normative subsystems to partial proofs of full languages.

### Risk 7: Complexity proofs dominate the work

Machine-checked asymptotic analysis can become a separate research project.

**Control:** establish functional correctness and empirical cost first. Add cost semantics for only the plan nodes needed by HTTP streaming and one memoised example.

## 12. The first concrete experiment

The fastest discriminating experiment is not JSON. It is the CommonMark fence fragment.

1. Define a line-oriented input model.
2. Encode `FenceOpen`, `FenceClose opener`, content collection and indentation removal as relations.
3. Define a direct scanner plan parameterised by the opening fence witness.
4. Prove the scanner sound and complete for the fragment.
5. Run the relevant CommonMark examples.
6. Compare against a PEG implementation using a captured fence length and semantic predicate.
7. Measure how much of the proof is generic to dependent sequencing.

This experiment is small enough to complete quickly but strong enough to expose the key issue. If the reusable `bind` and scanning theorems make the proof short, proceed to HTTP chunking. If the proof becomes entirely CommonMark-specific, redesign before adding cases.

## 13. Expected outputs

1. A formal paper defining the specification calculus, parser-plan calculus and refinement relation.
2. A Rocq library of proof-relevant grammars and certified plan constructors.
3. A proof-producing parser-plan synthesiser.
4. Extracted executable parsers for the case-study fragments.
5. A curated corpus linking each normative rule to positive and negative tests.
6. An empirical paper on algorithm selection, proof cost and grammar evolution.
7. A general “declarative specification → algorithmic inhabitant” template suitable for subsequent work on query planning.

## 14. Decision criteria after the prototype

Continue toward the broader programme if:

- the CommonMark and HTTP specifications remain visibly declarative;
- at least one specialised plan is synthesised rather than hand-written;
- soundness and rejection completeness are kernel checked;
- side conditions are mostly discharged compositionally;
- proof erasure yields an implementation with the expected asymptotic behaviour;
- the same plan/refinement architecture plausibly extends to Haskell layout and TOML state.

Pivot or narrow the project if:

- Narcissus already supplies the desired abstraction with only superficial changes;
- algorithm hints duplicate most of the specification;
- negative evidence makes exact parsing impractical;
- environment-indexed memoisation causes unavoidable state explosion;
- operational properties cannot be stated modularly over plan composition.

## References

- Jason Gross and Adam Chlipala, [*Parsing Parses: A Pearl of Dependently Typed Programming and Proof*](https://people.csail.mit.edu/jgross/personal-website/papers/2015-parsing-parse-trees.pdf).
- Sam Lasser, Chris Casinghino, Kathleen Fisher and Cody Roux, [*A Verified LL(1) Parser Generator*](https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf).
- Neel Krishnaswami and Jeremy Yallop, [*A Typed, Algebraic Approach to Parsing*](https://www.cl.cam.ac.uk/~jdy22/papers/a-typed-algebraic-approach-to-parsing.pdf).
- Wouter Swierstra and Andres Löh, [*Dependently Typed Grammars*](https://www.andres-loeh.de/DependentlyTypedGrammars/DependentlyTypedGrammars.pdf).
- Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye and Adam Chlipala, [*Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats*](https://www.cs.purdue.edu/homes/bendy/papers/Narcissus/narcissus.pdf).
- Adam Koprowski and Henri Binsztok, [*TRX: A Formally Verified Parser Interpreter*](https://arxiv.org/pdf/1105.2576).
- Bryan Ford, [*Packrat Parsing: a Practical Linear-Time Algorithm with Backtracking*](https://dspace.mit.edu/handle/1721.1/87310).
- Huan Vo, Danushka Liyanage, Hong Jin Kang, Sasha Rubin and Rahul Gopinath, [*An Empirical Comparison of General Context-Free Parsers*](https://arxiv.org/abs/2606.08465).
- IETF, [RFC 8259: The JavaScript Object Notation Data Interchange Format](https://www.rfc-editor.org/info/rfc8259/).
- CommonMark, [*CommonMark Specification: Fenced code blocks*](https://spec.commonmark.org/spec.html#fenced-code-blocks).
- IETF, [RFC 9112: HTTP/1.1, section 7.1](https://www.rfc-editor.org/rfc/rfc9112.html#section-7.1).
- [*Haskell 2010 Language Report*](https://www.haskell.org/definition/haskell2010.pdf), sections 2.7 and 10.3.
- [*TOML v1.0.0 Specification*](https://toml.io/en/v1.0.0) and the [official TOML conformance tests](https://github.com/toml-lang/toml-test).

