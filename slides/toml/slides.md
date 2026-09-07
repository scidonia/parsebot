---
theme: seriph
colorSchema: dark
highlighter: shiki
lineNumbers: false
title: Inhabited Parsing — Certified TOML
info: |
  Synthesizing a certified recursive-descent parser from a declarative TOML
  grammar, verified in Rocq (Coq), with extraction and a benchmark.
drawings:
  persist: false
class: text-center
---

<style>
::root {
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
## A certified parser for TOML

Synthesized from a *declarative grammar*, verified in **Rocq (Coq)**
— surface parser **and** the document state machine

<small>`theories/Toml.v` · S8 — key/value pairs, dotted keys, tables, arrays-of-tables</small>

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
branch, and whitespace runs can be split arbitrarily. The parser additionally commits to
<em>ordered choice</em> and a declared <em>separator policy</em> — those are separate declarative
decisions, and TOML's surface makes exactly this point concretely.

</div>

---
layout: default
---

# TOML grammar — high-level BNF (S8 slice)

```text
document  ::= ws  stmt ( ws1 stmt )*  ws

stmt      ::= kv | table | array
kv        ::= key ws "=" ws int          -- key = value  (integer-only)
table     ::= "[" key "]"                -- [table]
array     ::= "[[" key "]]"              -- [[array-of-tables]]

key       ::= ident ( "." ident )*       -- bare / dotted, no quoting
ident     ::= ident-char+                -- any non-ws, non-structural char
int       ::= digit+                     -- non-negative, maximal munch

ws        ::= ( space | tab | lf | cr )*      -- zero or more
ws1       ::= ( space | tab | lf | cr )+      -- one or more  ← the separator
```

<div class="text-sm text-gray-400">

`ws1` (not `ws0`) between statements is a **declared disambiguation decision**, not part of
the relational BNF — it is what makes the greedy parser agree with the relation.

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

<div class="mt-6 text-sm text-gray-400">

TOML adds a **second layer**: the document *state machine* (<code>step</code>/<code>run</code>)
is itself a declarative spec — `Get`/`Put`/`Guard` over a <code>Namespace</code>.

</div>

---
layout: default
---

# Types at a glance — grammar & meaning

```ocaml
Spec Γ N A                                     (* grammar: a combinator tree, as data *)
Grammar Γ N := forall A, N A -> Spec Γ N A     (* productions table; recursion via Call *)
denote G w S γ i a γ' j                        (* "S, at i in state γ, yields a at j in γ'" *)
```

| `Spec` parameter | what it is | surface layer | state layer |
| --- | --- | --- | --- |
| `Token` | token type (section var) | `ascii` | `unit` |
| `Γ` | environment / state | `unit` (stateless) | `Namespace` |
| `N` | nonterminal family | `tom_nt` (empty — no recursion) | `tom_nt` |
| `A` | result type produced | `stmt` / `Document` | `unit` |

<div class="text-left text-sm mt-4">
`denote` is <strong>`Type`-valued</strong> — a derivation <em>is</em> the certificate: the parsed
value `a` is an index of the proof. Two grammars over the same `tom_nt`:
<code>surface_grammar : Grammar ascii unit tom_nt</code> and
<code>tom_grammar : Grammar unit Namespace tom_nt</code>.
</div>

---
layout: default
---

# Types at a glance — parser & data

```ocaml
parse_doc  (fuel : nat) (w : list ascii) : option Document
parse_then_validate (w : list ascii) : option Namespace
direct_parse (fuel : nat) (ns : Namespace) (w : list ascii) : option Namespace

Definition seg : Type := list ascii.            (* a key segment *)
Definition key : Type := list seg.              (* a dotted path   *)
Definition Namespace : Type := list (key * kind).

Inductive kind : Type := KImplicit | KTable | KArrayTable | KScalar.
Inductive stmt : Type :=
| SKV (k : key) (v : nat) | STable (k : key) | SArray (k : key).
Definition Document : Type := list stmt.
```

<div class="text-sm text-gray-400">
The surface parser reads characters → <code>Document</code>. The state machine folds
<code>step</code> over it: <code>run ns (s :: rest) = step ns s >>= fun ns' → run ns' rest</code>.
<code>parse_then_validate = parse_doc ∘ run []</code>; <code>direct_parse</code> interleaves the two
(single pass, §6.5), certified equivalent to parse-then-validate.
</div>

---
layout: default
---

# Step 1 — grammar as data

The `Spec` deep embedding; recursion via `Call` + a `Grammar`.

```ocaml
Inductive Spec (Γ : Type) (N : Type -> Type) : Type -> Type :=
| Pure  : A -> Spec Γ N A
| Fail  : Spec Γ N A
| Tok   : (Token -> Type) -> Spec Γ N Token
| Seq   : Spec Γ N A -> Spec Γ N B -> Spec Γ N (A * B)
| Alt   : Spec Γ N A -> Spec Γ N A -> Spec Γ N A
| Map   : (A -> B) -> Spec Γ N A -> Spec Γ N B
| Bind  : Spec Γ N A -> (A -> Spec Γ N B) -> Spec Γ N B
| Many  : Spec Γ N A -> Spec Γ N (list A)
| Guard : (A -> Type) -> Spec Γ N A -> Spec Γ N A
| Get | Put γ | Local | Call (n : N A).
```

<div class="text-sm text-gray-400">
Semantic actions live in <code>Map</code>/<code>Bind</code>; <code>Get</code>/<code>Put</code>/<code>Guard</code>
express the *state machine* (the second layer). A derivation is a derivation-indexed value.
</div>

---
layout: default
---

# Step 1 — the surface productions, concretely

```ocaml
Definition ch c := Map (fun _ : ascii => tt) (Tok (fun c' => c' = c)).

Definition ws_spec  := Map (fun _ : list unit => tt) (Many (Map (fun _ => tt) (Tok is_ws))).
Definition ws1_spec := Map (fun _ => tt) (Seq (Map (fun _ => tt) (Tok is_ws))
                                            (Many (Map (fun _ => tt) (Tok is_ws)))).

Definition int_spec := Map (fun p => digits_to_nat (fst p :: snd p) 0)
                           (Seq digit_spec (Many digit_spec)).
Definition ident_spec := Map (fun p => fst p :: snd p)
                             (Seq (Tok is_ident_char) (Many (Tok is_ident_char))).
Definition key_spec := Map (fun p => fst p :: snd p)
                           (Seq ident_spec (Many (Map (fun p => snd p)
                                                     (Seq (ch ".") ident_spec)))).
```

<div class="text-sm text-gray-400">
`ws1_spec` = `ws · ws*` — one-or-more. `int_spec` = `digit digit*`. `key_spec` = `ident ( . ident )*`.
</div>

---
layout: default
---

# Step 1 — statements & the document

```ocaml
Definition kv_spec := Bind key_spec (fun k =>
  Bind ws_spec (fun _ => Bind (ch "=") (fun _ =>
    Bind ws_spec (fun _ => Map (fun v : nat => SKV k v) int_spec)))).

Definition table_spec := Bind (ch "[") (fun _ =>
  Bind key_spec (fun k => Bind (ch "]") (fun _ => Pure (STable k)))).

Definition array_spec := Bind (ch "[") (fun _ => Bind (ch "[") (fun _ =>
  Bind key_spec (fun k => Bind (ch "]") (fun _ =>
    Bind (ch "]") (fun _ => Pure (SArray k)))))).

Definition stmt_spec := Alt kv_spec (Alt table_spec array_spec).

Definition doc_spec := Bind ws_spec (fun _ =>
  Bind (Alt (Pure []) (Map (fun p => fst p :: snd p)
                          (Seq stmt_spec (Many (Bind ws1_spec (fun _ => stmt_spec))))))
       (fun doc => Bind ws_spec (fun _ => Pure doc))).
```

<div class="text-sm text-gray-400">
`doc_spec = ws · ( ε | stmt ( ws1 stmt )* ) · ws`. The separator is **`ws1_spec`** — the disambiguation.
</div>

---
layout: default
---

# The declarative disambiguation choices

The BNF is relational; the parser commits to these **separate, declared** decisions:

| decision | what it pins down | why it matters |
| --- | --- | --- |
| **ordered choice** | `stmt = kv \| table \| array`, tried in order | first char `[` disambiguates table/array from `kv`; `[[` picks array |
| **separator = `ws1`** | statements split on *≥1* whitespace, not `ws0` | forces maximal-munch on the trailing integer — the crux |
| **maximal munch** | `int = digit+`, greedy | `12` parses as one value, never `1` then `2` |
| **bare keys only** | `ident-char = ¬(ws ∨ "=" ∨ "[" ∨ "]" ∨ ".")` | no quoted keys in this slice |
| **no `Call` recursion** | `tom_nt` is empty | a document is a *flat* list; repetition is `Many`, not nesting |
| **flat namespace** | dotted keys promote prefixes to implicit tables | `a.b` ⇒ `a` is `KImplicit`; no table scoping |

<div class="text-sm text-gray-400">
Each is a *choice the AI must make and state*, not something the BNF dictates — exactly the
"BNF + disambiguation policy" split.
</div>

---
layout: default
---

# Why `ws1` (not `ws0`) is the crux

With `ws0` separators, the relation is **more permissive than the greedy parser**:

```text
a=12b=3    denotable as  [SKV a 12 ; SKV b 3]   (greedy, correct)
           denotable as  [SKV a 1  ; SKV 2b 3]  (relation also admits this)
a=12=3     denotable as  [SKV a 1  ; SKV 2 3]   but parse_doc = None
```

<div class="text-left text-sm mt-4">

- <code>Many digit_spec</code> is *non-maximal*: `12` can denote as `1` then `2`. With `ws0`,
  a following statement can absorb the leftover digit — so `denote ⇒ parse` (**completeness**) fails.
- With **`ws1`**: a statement *must* be followed by at least one whitespace before the next,
  so the integer inside a `kv` is forced to consume **all** its digits. Maximal-munch becomes
  a *consequence of the separator*, and `doc_complete` holds.

</div>

<div class="text-green-400 text-sm">
This is the headline result: <strong>choosing `ws1` is what makes the grammar unambiguous</strong>,
not a change to the parser.
</div>

---
layout: default
---

# Step 2 — the denotation

`denote` is an **inductive relation** — a derivation *is* the certificate.

```ocaml
Inductive denote : forall A, Spec Γ N A -> Γ -> nat -> A -> Γ -> nat -> Type :=
| d_pure : denote (Pure a) γ i a γ i
| d_tok  : nth_error w i = Some t -> P t -> denote (Tok P) γ i t γ (S i)
| d_seq | d_alt_l | d_alt_r | d_map | d_bind | d_guard
| d_many_nil | d_many_cons
| d_get | d_put | d_local
| d_call : denote (G A n) γ i a γ' j -> denote (Call n) γ i a γ' j.

(*  denote G w S γ i a γ' j  :=  "S, begun at i in env γ,
    produces a and ends at j in env γ'"   — proof-relevant (Type) *)
```

<div class="text-sm text-gray-400">
`d_many_cons` *chooses* a split; the relation admits every split. Completeness must show the
greedy split is the one the parser picks — hence the `ws1` argument.
</div>

---
layout: default
---

# Step 3 — the parser

A fuel-bounded recursive-descent `Fixpoint` (first-character dispatch), plus the state machine.

```ocaml
Fixpoint parse_doc (fuel : nat) (w : list ascii) : option Document :=
  match skip_ws w with
  | [] => Some []
  | _ => match fuel with
         | O => None
         | S fuel' =>
             match parse_stmt fuel' (skip_ws w) with
             | None => None
             | Some (s, rest) =>
                 match skip_ws rest with
                 | [] => Some [s]
                 | _ => match rest with
                        | c :: _ => if is_ws c then parse_doc fuel' rest ↦ cons s
                                   else None
                        end
                 end
             end
  end
```

```ocaml
Fixpoint run (ns : Namespace) (doc : Document) : option Namespace :=
  match doc with [] => Some ns | s :: rest => step ns s >>= fun ns' => run ns' rest end.
```

<div class="text-sm text-gray-400">
`parse_stmt` dispatches on the first char: `[` → table/array (then `[[`), else `key = value`.
`step`/`run` implement the flat-namespace semantics (`define`/`lookup`).
</div>

---
layout: default
---

# Step 4 — soundness ✔

The parser only ever produces real denotations.

```ocaml
Lemma parse_doc_tail_sound : (* the Many (ws1 · stmt) tail *)
  parse_doc fuel w = Some ss -> ws_part w <> [] ->
  denote surface_grammar (prefix ++ w) (Many (Bind ws1_spec (fun _ => stmt_spec)))
    tt (length prefix) ss tt (length prefix + length w - length (ws_trail w)).

Lemma parse_doc_body_sound : (* Alt (Pure []) (Map (Seq stmt (Many ...))) *)
  parse_doc fuel w = Some ss ->
  denote surface_grammar (prefix ++ skip_ws w) (Alt (Pure []) (Map ...))
    tt (length prefix) ss tt (length prefix + length (skip_ws w) - length (ws_trail (skip_ws w))).

Lemma parse_doc_sound : forall fuel w doc,
  parse_doc fuel w = Some doc -> denote surface_grammar w doc_spec tt 0 doc tt (length w).
```

<div class="text-green-400 text-sm">
Status: <strong>all `Qed.`</strong> — key/value/table/array/statement/document, plus the state machine
(<code>step_spec_sound</code>, <code>direct_parse_equiv</code>, <code>parse_then_validate_iff_direct</code>).
</div>

---
layout: default
---

# Step 5 — completeness (the subtlety)

The converse is **not** free — it holds *because* of the `ws1` separator.

```ocaml
Lemma key_complete :  (* key: maximal ident, then '.' / '=' dispatch *)
  denote ... key_spec ... -> (non-ident, non-dot after) -> parse_key ... = Some (k, suffix).

Lemma stmt_complete : (* statement: maximal integer *)
  denote ... stmt_spec ... -> (non-digit after) -> parse_stmt ... = Some (s, suffix).

Lemma doc_complete : forall w doc,
  denote surface_grammar w doc_spec tt 0 doc tt (length w) ->
  parse_doc (length w) w = Some doc.
```

<div class="text-left text-sm mt-4">

- `stmt_complete` demands maximality — "the char after the statement is a non-digit". It is
  supplied by the **`ws1_spec`** that follows: a separator must begin with whitespace, so the
  integer's last digit cannot be followed by another digit.
- `doc_complete` is proved by induction on the document, reconstructing `Many (ws1 · stmt)`
  step by step and threading the maximality witness.

</div>

---
layout: default
---

# Step 6 — extraction & acceptance

```ocaml
Extraction Language OCaml.
Extraction "toml.ml" parse_then_validate direct_parse parse_doc.
```

```text
parse_then_validate "title = 42"            = Some [("title", KScalar)]
parse_then_validate "a.b = 7"               = Some [("a.b", KScalar); ("a", KImplicit)]
parse_then_validate "[t]\nid = 1"           = Some [(id, KScalar); (t, KTable)]
parse_then_validate "[[a]]\nitem = 1"       = Some [(item, KScalar); (a, KArrayTable)]
```

<div class="text-sm text-gray-400">
Build: <code>nix develop --command make</code> (flake pins Rocq 9.1.1). Extracted types are clean:
<code>stmt = SKV of key × Z.t | STable of key | SArray of key</code>; proofs vanish.
</div>

---
layout: default
---

# Benchmark — extraction directives

```ocaml
Extract Inductive nat   => Z.t      (* Big_int_Z.big_int = Zarith Z.t *)
Extract Inductive Z     => Z.t
Extract Inductive ascii => char
Extract Constant Z.of_nat => "(fun n -> n)"   (* else it recurses on the value *)
```

<div class="text-sm text-gray-400">
`nat`/`Z` → Zarith `Z.t` (arbitrary precision), `ascii` → `char`. A hand-written `Big_int_Z.ml`
shim supplies the `Big_int`-named API over `Z.t`.
</div>

---
layout: default
---

# Benchmark — surface parser scales linearly

`parse_doc` (surface parser only) on a synthetic flat document
(`key{i} = v` + `grp{i}.leaf{i} = v` per item):

| items | size | statements | time | throughput |
| --- | --- | --- | --- | --- |
| 2k | 86 KB | 4.0k | 0.005 s | ~18 MB/s |
| 4k | 176 KB | 8.1k | 0.006 s | ~28 MB/s |
| 6k | 267 KB | 12.1k | 0.009 s | ~30 MB/s |
| 80k | 3.9 MB | 162k | 0.155 s | ~25 MB/s |
| 160k | 8.1 MB | 323k | 0.416 s | ~19 MB/s |

<div class="text-sm text-gray-400">
Linear, on par with the JSON parser (~30 MB/s). The tail-off is `big_int` fuel arithmetic and
cache pressure, not algorithmic growth.
</div>

---
layout: default
---

# Benchmark — the state machine is O(n²)

`parse_then_validate` / `direct_parse` fold the **flat-namespace** state machine, whose
`lookup : list (key × kind) → key → option kind` is a **linear scan** of a growing list.

| items | size | `parse_doc` | `parse_then_validate` | `direct_parse` |
| --- | --- | --- | --- | --- |
| 2k | 86 KB | 0.005 s | 0.200 s | 0.199 s |
| 4k | 176 KB | 0.006 s | 0.778 s | 0.807 s |
| 6k | 267 KB | 0.009 s | 2.46 s | 2.99 s |

<div class="text-left text-sm mt-4">

- Each `step` re-scans the namespace → **quadratic** in the number of statements
  (4× time per 2× input).
- This is the *naive certified* implementation, not an extraction artifact. Optimizing
  `lookup` to a map would change `run`/`step` and require re-proving `DocumentStep` —
  out of scope for S8.

</div>

---
layout: center
---

# Thanks

**Soundness** certified · **Completeness** certified (the `ws1` fix) · **Extraction** to OCaml

<small class="text-gray-400">`./slides/toml` — `npm install && npm run dev`</small>
