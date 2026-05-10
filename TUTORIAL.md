# Tutorial: navigating the fexpr-trivial mechanization

This tutorial walks a reader through the artifact: what it proves, in
what order to read the files, and where to look for each piece of
Wand's argument. It assumes basic familiarity with CBV λ-calculus
and Lean 4 syntax; no Mathlib is used.

## 1. The claim, in plain English

Wand's setting is the call-by-value λ-calculus extended with two
reflective operators:

- **`fexpr V`**: a value that, when applied to operand `M`, captures
  `M`'s *syntax* as a code (a Mogensen–Scott encoding `⌜M⌝`) and
  passes that code to `V`. The reduction rule is

      (fexpr V) M  →  V ⌜M⌝.

- **`eval ⌜M⌝`**: the inverse, decoding a code back to its source
  term:

      eval ⌜M⌝  →  M.

These two rules let a context **observe the syntactic shape of its
operand**. The natural equational theory `EqM` of this calculus closes
under β + the two reflective rules + full structural congruence
(`appL`, `appR`, `lamIn`, `fexprIn`, `evalIn`).

**Wand's claim**: `EqM` is *not contextually sound*. There is a
context that distinguishes a β-equivalent pair on convergence — so
the equational theory equates terms that operationally differ.

We mechanize exactly this, in Wand's notion: define `EqM`, then
exhibit a concrete `EqM`-related pair `(M, N)` with `Converges M`
and `¬ Converges N`.

## 2. How to build & explore

```sh
cd fexpr-trivial-mechanized
lake build               # 15 jobs, sorry-free
```

To explore interactively, open `FexprTrivial/EqM.lean` in your editor
and place the cursor at the bottom — `EqM_not_convergenceSound` is the
headline. Hover on the named lemmas it uses to see their types; jump
to definition with the usual Lean 4 IDE bindings.

Top-level reexport: `FexprTrivial.lean` imports every module, so
`import FexprTrivial` from a downstream project pulls in the whole
artifact.

## 3. File-by-file tour

A good reading order, following the dependency graph from leaves to
the headline:

```
Term ── Subst ── Coding ── Reduction
                    │           │
                    ├── LemmaOne ── Discriminator ── WandValue
                    │           │       │
                    │           ├──── Determinism
                    │           │
                    └────── Theorem1Concrete
                                            │
                                            └── EqM  ←  the headline

(Alpha and Beta are not on the critical path to the headline.)
```

### Calculus foundations

- **`Term.lean`** — Inductive `Term` with five constructors (`var`,
  `lam`, `app`, `fexpr`, `eval`); free variables (`fv`) and the
  `closed` predicate. Named variables, intentionally — α-distinct
  terms must be representable as syntactically distinct, since
  Wand's discriminator observes syntax.

- **`Alpha.lean`** — Environment-based α-equivalence (`AlphaEqIn env M N`)
  with refl/sym/trans. Used only to discuss what the headline
  *would* say in an α-respecting form; the mechanized headline uses
  syntactic equality, leaving α-respect as future work.

- **`Subst.lean`** — `substClosed` (naive substitution, sound when the
  substituted term is closed). All our reductions stay closed, so
  this suffices.

- **`Coding.lean`** — The Mogensen–Scott encoding `⌜·⌝`:

      ⌜x⌝     = λabcde. a x
      ⌜M N⌝   = λabcde. b ⌜M⌝ ⌜N⌝
      ⌜λx.M⌝  = λabcde. c (λx. ⌜M⌝)
      ⌜fexpr M⌝ = λabcde. d ⌜M⌝
      ⌜eval M⌝  = λabcde. e ⌜M⌝

  Reserved names `__a__ … __e__` (`codeA`–`codeE`). Free-variable
  inclusion `mem_fv_encode` is established here.

### Operational semantics

- **`Reduction.lean`** — `Step` (CBV β + reify + reflect + structural
  congruence), `StepStar`, `Converges`, `IsValue`, plus inversion
  lemmas (`step_eval_inv`, `step_app_inv`, `stepStar_value_eq` etc.)
  that the determinism proof uses.

- **`Beta.lean`** — `BetaStep` and `BetaEq` (the βᵥ fragment without
  the reflective rules). Not on the critical path to the headline;
  kept for talking about β-equivalence as a relation in its own right.

### Wand's argument

#### `LemmaOne.lean` — Wand Lemma 1 (~350 LOC)

Three facts about the encoding:

- **1.2 (free-variable preservation)**: `y ∈ ⌜M⌝.fv ↔ y ∈ M.fv ∧ y ∉ codeReserved`.
  The closure form `closed_encode_iff_safe` follows.

- **1.3 (structural injectivity)**: `⌜M⌝ = ⌜N⌝ → M = N`
  (`Term.encode_injective`). The proof is a 5×5 case analysis:
  distinct head constructors of `Term` produce different encoding
  markers (codeA vs codeB vs …), and equal markers force equal
  sub-encodings, which yield equal sub-terms by induction. This is
  the lemma that lets "distinct closed terms" become "distinguishable"
  later: distinct M, N have distinct codes.

- **`encode_ne_of_ne`** is the contrapositive corollary used downstream.

#### `Discriminator.lean` — `idBody` + cascade (~60 LOC)

Defines `idBody := λc. c` and proves the two-step reduction

    (fexpr idBody) M  →¹  idBody ⌜M⌝  →¹  ⌜M⌝

via `reify_idBody` + `beta_idBody`. The composite `fexpr_idBody_stepStar`
says: applied to closed `M`, the reflective context evaluates to the
operand's code. This is the simplest possible discriminator and the
one that the abstract collapse uses.

#### `WandValue.lean` — value-level distinguishability (~60 LOC)

`wand_distinguishes_distinct_terms`: for any closed `M ≠ N`, the
context `(fexpr idBody) ·` reduces them to syntactically distinct
values. Combines `fexpr_idBody_stepStar` with `Term.encode_ne_of_ne`.
This is the cleanest "general" result; it's value-level, not
convergence-level (both terms still converge, just to different values).

#### `Theorem1Concrete.lean` — the convergence cascade (~530 LOC)

Defines a richer fexpr body `divBody` and traces its reduction on a
specific β-equivalent pair:

    termLHS  =  (λx.x)(λy.y)        -- β-redex
    termRHS  =  (λy.y)              -- β-reduct

with `Step termLHS termRHS` by `termLHS_step_termRHS`. The cascades:

- `termRHS_cascade_to_idA` — `(fexpr divBody) termRHS  →*  idA`,
  packaging the 8-step CBV reduction through the encoding's `codeC`
  marker into `constId`'s body and out to the value `idA`. Hence
  `fexprDiv_termRHS_converges`.

- `termLHS_cascade_to_omega` — `(fexpr divBody) termLHS  →*  Ω`,
  the 9-step reduction through the encoding's `codeB` marker into
  `divLam`'s two-argument abyss, ending at the divergent term `Ω`.

`omega_diverges : ¬ Converges Ω` is also proved here (Ω self-reduces;
`stepStar_omega_unique` says nothing else is reachable; `Ω` is not a
value).

This file is the longest and most repetitive: each step of each
cascade is its own named lemma. It is essentially what Wand's
informal argument looks like when you write down every β-substitution.

#### `Determinism.lean` — what closes the loop (~110 LOC)

Three theorems:

- **`step_deterministic`**: `Step M N₁ → Step M N₂ → N₁ = N₂`. By
  induction on the first `Step`, with `generalizing N₂` so the IH
  is universal over the second reduct. Each case rules out the wrong
  Step rules via `step_value_absurd` / `step_lam_absurd`. The
  `reflect`-vs-`reflect` case uses the inversion lemma `step_eval_inv`
  (rather than direct `cases`, which Lean can't apply when the input
  shape `M.encode` involves an arbitrary term `M`) plus
  `Term.encode_injective`.

- **`stepStar_align`**: if `M →* W` and `M →* V` with `V` a value,
  then `W →* V`. By induction on `M →* W`: the reflexive case uses
  that values don't step (so M = V is impossible if M took a step);
  the step case aligns the two reductions via `step_deterministic`.

- **`not_converges_of_stepStar_diverges`**: if `M →* W` and
  `¬ Converges W`, then `¬ Converges M`. Direct corollary of
  `stepStar_align`.

This file is what lets us upgrade `Theorem1Concrete`'s "reaches Ω"
to the canonical "doesn't converge."

#### `EqM.lean` — the equational theory + headline (~170 LOC)

Defines `EqM` as the inductive closure under `Step` + `refl` / `sym`
/ `trans` + the five congruence rules. Notable members:

- **`EqM_relates_β_pair : EqM termLHS termRHS`** — a single β-step
  lift, the building block for the headline.

- **`ConvergenceSound R := ∀ M N, R M N → (Converges M ↔ Converges N)`**
  — Wand's notion of soundness.

- **`EqM_not_convergenceSound : ¬ ConvergenceSound EqM`** — the
  headline. The proof is six lines: lift the β-pair via `appR` to the
  two reflective contexts; one converges by `fexprDiv_termRHS_converges`;
  the other doesn't by `not_converges_of_stepStar_diverges` applied
  to `termLHS_cascade_to_omega` and `omega_diverges`. Convergence
  soundness would force them to agree — they don't.

- **`wand_unsoundness`** — corollary: any `R` containing `EqM` is
  also not convergence-sound.

The file also retains an "abstract collapse" pitched at the (much
stronger) `ValueSound` notion: `wand_collapse_abstract` /
`wand_collapse_syntactic`. These are useful as a general statement
("any value-sound, compatible relation can only equate equal closed
terms") but are not the form that matches Wand's actual paper —
`ValueSound` is too strict to be Wand's notion. See the file's
header comment for why.

## 4. Tracing the argument

Read the headline first, then walk *upward* through its dependencies:

1. `EqM_not_convergenceSound` (`EqM.lean`) — 6-line proof.
2. The pieces it uses:
   - `EqM_relates_β_pair` and `appR` congruence.
   - `fexprDiv_termRHS_converges` (`Theorem1Concrete.lean`).
   - `termLHS_cascade_to_omega` (`Theorem1Concrete.lean`).
   - `not_converges_of_stepStar_diverges` (`Determinism.lean`).
   - `omega_diverges` (`Theorem1Concrete.lean`).
3. The cascades themselves are big but mechanical: each is a chain
   of `Step.appL` / `Step.appR` / `Step.beta` applications under the
   encoding's `codeA`/`codeB`/`codeC`/`codeD`/`codeE` binders.
4. Determinism is the substantive new ingredient: ~110 LOC of
   careful case analysis on `Step`.

## 5. Reading the key proofs

### `Term.encode_injective` (`LemmaOne.lean`)

Pattern: induct on `M`; for each constructor, case-split on `N`. Most
sub-cases produce a constructor mismatch on the encoding marker and
discharge via `decide` (the reserved names are pairwise distinct
`Name`s, so `codeA ≠ codeB` is decidable). The matching cases recurse
on sub-terms via the IH.

The use of `Term.app.injEq` / `Term.lam.injEq` / `Term.var.injEq`
(the auto-generated injectivity simp lemmas) is the cleaner
alternative to manual `injection` chains — it lets a single `simp only`
turn a wrapped equation into a tuple of sub-equations.

### `step_deterministic` (`Determinism.lean`)

Worth understanding the `induction h₁ generalizing N₂` idiom: without
`generalizing`, the IH would have a *fixed* `N₂` from the outer
context, which doesn't let us instantiate it at the recursive step's
own `N₂`. With `generalizing`, each case's IH is `∀ N₂, Step Mop N₂
→ Mop' = N₂` — exactly what we need to align with `cases h₂`.

The `reflect` case is the only one that can't use direct `cases`:
the constructor's input shape is `Step (.eval M.encode) M`, and
`cases h₂` asks Lean to unify `M.encode` with another `M'.encode`,
which it can't do for arbitrary terms. `step_eval_inv` packages this
as a disjunction with the equation as a hypothesis, sidestepping the
issue.

### The cascades (`Theorem1Concrete.lean`)

Each cascade step is named. Read `termRHS_cascade_to_idA` to see the
overall structure: `apply StepStar.step _ _ _ <step_lemma>` repeated.
The individual step lemmas (e.g., `termRHS_step_codeA`,
`termRHS_step_codeB`, …) each do one `Step.beta`-with-substitution.
The substitutions either leave the body unchanged (when the body is
closed and doesn't reference the bound variable) or replace one free
occurrence of a `codeX` marker with the corresponding selector.

The `Step.appL` lifts (e.g., the `(Step.appL _ _ _ termRHS_step_codeA)`
inside `cascade_step_codeA`) propagate a step inside the deeply nested
applications `((((c idA) divLam) constId) idA) idA` — there are five
function applications stacked, so up to 4 layers of `appL` lifting
are needed before reaching the active β-redex.

### `EqM_not_convergenceSound` (`EqM.lean`)

The proof is short enough to read in full:

```lean
theorem EqM_not_convergenceSound : ¬ ConvergenceSound EqM := by
  intro hSound
  have hEq : EqM (.app (.fexpr divBody) termRHS) (.app (.fexpr divBody) termLHS) :=
    .appR _ _ _ (.sym _ _ EqM_relates_β_pair)
  have hConv_LHS : Converges (.app (.fexpr divBody) termRHS) :=
    fexprDiv_termRHS_converges
  have hNotConv_RHS : ¬ Converges (.app (.fexpr divBody) termLHS) :=
    not_converges_of_stepStar_diverges termLHS_cascade_to_omega omega_diverges
  exact hNotConv_RHS ((hSound hEq).mp hConv_LHS)
```

Every line corresponds to one English-language step of Wand's
argument: lift the β-relation through the reflective context, recall
that one side converges and the other doesn't, derive the
contradiction.

## 6. Open work

Two pieces of Wand's full theorem aren't here:

- **General convergence-distinguishing context**: the headline uses a
  *specific* β-equivalent pair `(termLHS, termRHS)`. Generalizing to
  "for any closed M ≠ N, there is a context distinguishing them on
  convergence" needs a recursive in-calculus comparator — an `eq?`
  built within the calculus that reduces to a Church-true on a
  matching code and diverges otherwise. `divBody` only handles
  distinct head-constructor pairs.

- **α-respect**: we use syntactic equality. Wand's actual statement
  says `EqM = α-equivalence` on closed terms — needs either a
  De Bruijn encoding (codes become α-canonical) or
  encoding-respect-of-α lemmas extending `Alpha.lean`.

Either extension is a self-contained mini-project. Anyone wanting to
push the artifact further should start from `EqM_not_convergenceSound`
and work outward.
