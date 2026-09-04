---
theme: seriph
colorSchema: dark
highlighter: shiki
lineNumbers: false
title: Inhabited Parsing — Certified JSON
info: |
  Synthesizing a certified recursive-descent parser from a declarative
  JSON grammar, verified in Rocq (Coq).
drawings:
  persist: false
class: text-center
---

<style>
:root {
  --slidev-theme-background: #0d1117;
}
.slidev-layout {
  background: #0d1117 !important;
  color: #e6edf3 !important;
}
h1, h2, h3 { color: #f0f6fc !important; }
code { color: #ff7b72 !important; }
</style>

# Inhabited Parsing
## A certified recursive-descent parser for JSON

Synthesized from a *declarative grammar*, verified in **Rocq (Coq)**

<small>`theories/Json.v` · S5 — the "control" grammar</small>

---
layout: center
---

# The core idea

<div class="text-xl">

The **innovation**: the *implementation* and the *certification proof*
can both be produced by **AI** — from the **BNF** *plus explicit
disambiguation decisions*.

</div>

<div class="mt-8 text-lg text-gray-300">

grammar&nbsp;(declarative)&nbsp;+&nbsp;ambiguity&nbsp;policy &nbsp;⟹&nbsp; parser&nbsp;(executable) &nbsp;⟹&nbsp; proof&nbsp;(certificate)

</div>

<div class="mt-4 text-sm text-gray-400">

The BNF is <em>relational</em> — <code>Alt</code> is unordered, <code>Many</code> admits the empty
branch. The parser additionally commits to <em>ordered choice</em> and <em>lookahead</em>, under a
declared <em>ambiguity policy</em> (Recognition / Canonical / All-parses / Unambiguous). Those are
separate declarative decisions; the BNF alone is not enough.

</div>

---
layout: default
---

# JSON grammar — high-level BNF

```text
json-text  ::= ws value ws

value      ::= "null" | "true" | "false"
             | string | number | array | object

object     ::= "{" ws members ws "}"
members    ::= ε | member ws ( "," ws member ws )*
member     ::= string ws ":" ws value

array      ::= "[" ws elements ws "]"
elements   ::= ε | value ws ( "," ws value ws )*

string     ::= '"' char* '"'        -- no escapes in this slice
number     ::= [ "-" ] int          -- no leading zeros (RFC 8259)
int        ::= "0" | digit1-9 digit*
ws         ::= ( space | tab | lf | cr )*
```

<div class="text-sm text-gray-400">

Only `value` recurses — object/array nest values through the named nonterminal `NT_value`.

</div>

---
layout: center
---

# The pipeline

<style>
.pipeline { display: flex; flex-direction: column; gap: 0.9em; align-items: center; }
.pipe-row { display: flex; align-items: center; gap: 0.5em; }
.pipe-node { font-size: 1.55em; font-weight: 700; padding: 0.35em 0.55em;
  border-radius: 10px; border: 1px solid; line-height: 1.15; color: #fff; }
.pipe-node small { display: block; font-size: 0.58em; font-weight: 400; opacity: 0.9; }
.pipe-arr { font-size: 2.2em; color: #8b949e; }
.p-b { background: #1f6feb; border-color: #58a6ff; }
.p-p { background: #8957e5; border-color: #bc8cff; }
.p-g { background: #238636; border-color: #3fb950; }
.p-a { background: #9e6a03; border-color: #d29922; }
</style>

<div class="pipeline">
  <div class="pipe-row">
    <span class="pipe-node p-b">Grammar<small>deep Spec</small></span>
    <span class="pipe-arr">→</span>
    <span class="pipe-node p-p">denote<small>proof-relevant relation</small></span>
    <span class="pipe-arr">→</span>
    <span class="pipe-node p-g">Parser<small>fuel-bounded Fixpoint</small></span>
  </div>
  <div class="pipe-row">
    <span class="pipe-node p-g">Soundness<small>parse ⇒ denote</small></span>
    <span class="pipe-arr">→</span>
    <span class="pipe-node p-b">Extraction<small>OCaml</small></span>
    <span class="pipe-arr">←</span>
    <span class="pipe-node p-a">Completeness<small>denote ⇒ parse</small></span>
  </div>
</div>

---
layout: default
---

# Types at a glance — grammar & meaning

```ocaml
Spec Γ N A                                     (* grammar: a combinator tree, as data *)
Grammar Γ N := forall A, N A -> Spec Γ N A     (* productions table; recursion via Call *)
denote G S γ i a γ' j                          (* "S, at i in state γ, yields a at j in γ'" *)
```

| `Spec` parameter | what it is | in JSON |
| --- | --- | --- |
| `Γ` | environment / state | `unit` (stateless) |
| `N` | nonterminal *family* `N : Type -> Type` | `NT_value : json_nt Json` |
| `A` | result type produced | `Json` |

<div class="text-left text-sm mt-4">
`denote`'s seven slots: <code>S</code> (spec) · <code>γ i</code> start (state, position)
· <code>a</code> result · <code>γ' j</code> end (state, position).
It is <strong>`Type`-valued</strong> — a derivation <em>is</em> the certificate: the parsed
value `a` is an index of the proof.
</div>

---
layout: default
---

# Types at a glance — parser & data

```ocaml
parse_value (fuel : nat) (w : list ascii) : option (Json * list ascii)
parse_json  (w : list ascii) : option Json

Inductive Json : Type :=
| JNull | JBool (bool) | JNumber (Z) | JString (list ascii)
| JArray (list Json) | JObject (list (list ascii * Json)).
```

| slot | reading |
| --- | --- |
| `fuel : nat` | fuel bound — every recursive call decrements it (termination) |
| `list ascii` | input as a linked list of chars (indices are plain `nat`) |
| `option (… × rest)` | `None` = reject; `Some (value, rest)` = value + unconsumed suffix |

<div class="text-left text-sm mt-4">
Supporting proof types: <code>Progress</code> (termination evidence for `Many`),
<code>iffT A B := (A → B) × (B → A)</code> (Type-level iff for the `denote_*_iff` laws),
<code>{ pre & pre ++ rest = w }</code> ("consumed a prefix").
</div>

---
layout: default
---

# Step 1 — grammar as data

The `Spec` deep embedding over `ascii` tokens; recursion via `Call` + a `Grammar`.

```ocaml
Inductive Spec (Γ : Type) (N : Type -> Type) : Type -> Type :=
| Pure  : forall A, A -> Spec Γ N A
| Tok   : (Token -> Type) -> Spec Γ N Token
| Seq   : Spec Γ N A -> Spec Γ N B -> Spec Γ N (A * B)
| Alt   : Spec Γ N A -> Spec Γ N A -> Spec Γ N A
| Map   : (A -> B) -> Spec Γ N A -> Spec Γ N B
| Bind  : Spec Γ N A -> (A -> Spec Γ N B) -> Spec Γ N B
| Many  : Spec Γ N A -> Spec Γ N (list A)
| Call  : N A -> Spec Γ N A.   (* recursion *)

Definition Grammar (Γ : Type) (N : Type -> Type) :=
  forall A, N A -> Spec Γ N A.
```

<div class="text-sm text-gray-400">
Semantic actions live in <code>Map</code>/<code>Bind</code> — a derivation is a <em>derivation-indexed JSON value</em>.
</div>

---
layout: default
---

# Step 1 — `value_spec` concretely

```ocaml
Definition value_spec : Spec ascii unit json_nt Json :=
  Alt (Map (fun _ => JNull) (lit "null"))
    (Alt (Alt (Map (fun b => JBool b)
                    (Alt (Map (fun _ => true)  (lit "true"))
                         (Map (fun _ => false) (lit "false"))))
              (Map JString string_spec))
         (Alt (Map JNumber number_spec)
              (Alt (Map JArray  array_spec)
                   (Map JObject object_spec)))).
```

```text
json_grammar NT_value = value_spec
json_text = ws · Call NT_value · ws
```

---
layout: default
---

# Step 2 — the denotation

`denote` is an **inductive relation** — a derivation *is* the certificate.

```ocaml
Inductive denote : forall A, Spec Γ N A -> Γ -> nat -> A -> Γ -> nat -> Type :=
| d_pure : ...           (* Pure a: nothing consumed          *)
| d_tok  : nth_error w i = Some t -> P t -> ...   (* one token *)
| d_seq | d_alt_l | d_alt_r | d_map | d_bind
| d_many_nil | d_many_cons
| d_call : denote (G A n) γ i a γ' j -> denote (Call n) γ i a γ' j.

(*  denote G S γ i a γ' j  :=  "S, begun at i in env γ,
    produces a and ends at j in env γ'"   — proof-relevant (Type) *)
```

<div class="text-sm text-gray-400">
Because it is <code>Type</code>-valued, `Call` unfolds through the grammar with no termination obligation at the spec level.
</div>

---
layout: default
---

# Step 3 — the parser

A fuel-bounded **mutual** `Fixpoint`; first-character dispatch, ~8 levels deep.

```ocaml
Fixpoint parse_value (fuel : nat) (w : list ascii) : option (Json * list ascii) :=
  match fuel, w with
  | O, _ | _, [] => None
  | S fuel', c :: rest =>
      if c = "{" then (* object: parse_members, expect "}" *) ...
      else if c = "[" then (* array:  parse_elements, expect "]" *) ...
      else if c = '"' then (* string *) ...
      else if c = 't' / 'f' / 'n' then (* true / false / null *) ...
      else if digit / '-' then (* number *) ...
      else None
  end
(* mutual with parse_object · parse_array ·
   parse_members · parse_members_more ·
   parse_elements · parse_elements_more *)
```

<div class="text-sm text-gray-400">
`skip_ws` runs before/after tokens; indices are plain `nat` cursors.
</div>

---
layout: default
---

# Step 4 — soundness ✔

The parser only ever produces real denotations.

```ocaml
Lemma parse_all_sound : forall fuel,  (* 7-way mutual, by induction on fuel *)
  (forall prefix w v rest, parse_value fuel w = Some (v, rest) ->
      denote json_grammar (prefix ++ w) value_spec tt (length prefix)
             v tt (length prefix + length w - length rest)) * ... .

Lemma parse_json_sound (w : list ascii) (v : Json) :
  parse_json w = Some v ->
  denote json_grammar w json_text tt 0 v tt (length w).
```

<div class="text-green-400 text-sm">
Status: <strong>all `Qed.`</strong> — value/object/array/members/members_more/elements/elements_more + top level.
</div>

---
layout: default
---

# Step 5 — completeness (the subtlety)

The converse is **not** a free mirror — the grammar is more permissive than the *predictive* parser.

```ocaml
Lemma parse_json_complete (w : list ascii) (v : Json) :
  denote json_grammar w json_text tt 0 v tt (length w) ->
  parse_json w = Some v.   (* true at the top level *)
```

<div class="text-left text-sm mt-4">

- `members ::= ε` / `elements ::= ε` admit `Pure nil` for **any** input, but
  `parse_members`/`parse_elements` return `Some ([], w)` only when `w` starts with `}` / `]`.
- Counterexample: `denote "x" members_spec … nil …` holds, yet `parse_members _ "x" = None`.
- Fix: **context-aware** completeness — fold members/elements into object/array
  (whose spec carries the `}`/`]`), plus a ws-absorption lemma.

</div>

---
layout: default
---

# Step 6 — extraction & acceptance

```ocaml
Extraction Language OCaml.
Extraction "json.ml" parse_json.     (* 649-line, self-contained *)
```

```text
parse_json "null"        = Some JNull
parse_json "true"        = Some (JBool true)
parse_json "[1,2,3]"     = Some (JArray [JNumber 1; JNumber 2; JNumber 3])
parse_json "[true, null]"= Some (JArray [JBool true; JNull])
parse_json { "a" : 1 }   = Some (JObject [("a", JNumber 1)])
```

<div class="text-sm text-gray-400">
Build: <code>nix develop --command make</code> (flake pins Rocq 9.1.1). `Eval compute` gates run per stage.
</div>

---
layout: default
---

# Benchmark — the inputs

<div class="text-left text-lg">

- **`canada.json`** — 2.25 MB, from `nativejson-benchmark`: a GeoJSON
  `FeatureCollection` (~60k features) with floating-point coordinates.
  → **correctly rejected** in 0.02 s — floats sit outside the integer-only
  `number ::= [-] int` grammar (the parser is *sound*).
- **`large_int.json`** — synthetic array of objects
  `{"id","name","tags","child","flags"}` (integers, bools, null, nested arrays),
  scaled from **4.75 MB / 30k objects** up to **53 MB / 316k objects**.
  → **parsed end-to-end** as `array[N]`.

</div>

---
layout: default
---
# Performance — extraction directives

```ocaml
Extract Inductive nat   => Z.t      (* Big_int_Z.big_int = Zarith Z.t *)
Extract Inductive Z     => Z.t
Extract Inductive ascii => char
Extract Constant Z.of_nat => "(fun n -> n)"   (* else it recurses on the value *)
```

| extraction (4.75 MB) | time |
| --- | --- |
| naive (unary `nat` + binary `z` + `Ascii` records) | 164.27 s |
| native `int` + `char` (63-bit) | 0.137 s |
| **Zarith `Z.t` + `char` (arbitrary precision)** | **0.155 s** |

<div class="text-sm text-gray-400">
≈ <strong>1060×</strong> faster than the naive extraction; arbitrary precision costs only ~13% over native `int`.
</div>

---
layout: default
---

# Performance — scaling (Zarith)

| `large_int.json` | size | objects | time | throughput |
| --- | --- | --- | --- | --- |
| | 4.75 MB | 30k | 0.155 s | ~31 MB/s |
| | 10.1 MB | 63k | 0.350 s | ~29 MB/s |
| | 25.9 MB | 158k | 1.01 s | ~26 MB/s |
| | 52.9 MB | 316k | 2.74 s | ~19 MB/s |

---
layout: center
---

# Thanks

**Soundness** certified · **Extraction** to OCaml · **Completeness** precisely scoped

<small class="text-gray-400">`./slides/json` — `npm install && npm run dev`</small>
