# Tutorial: navigating the fexpr-trivial mechanization

This tutorial walks a reader through the artifact: what it proves, in
what order to read the files, and where to look for each piece of the
argument. Basic familiarity with CBV λ-calculus and Lean 4 syntax is
assumed; no Mathlib is used.

## 1. The claim, in plain English

The setting is the CBV λ-calculus extended with two reflective
operators:

- **`fexpr V`**: a value that, when applied to operand `M`, captures
  `M`'s *syntax* as a code (a Mogensen–Scott encoding `⌜M⌝`) and
  passes that code to `V`. The reduction rule is

      (fexpr V) M  →  V ⌜M⌝.

- **`eval ⌜M⌝`**: the inverse, decoding a code back to its source:

      eval ⌜M⌝  →  M.

These rules let a context **observe the syntactic shape of its
operand**. The natural equational theory `EqM` of this calculus
closes under β + the two reflective rules + full structural
congruence (`appL`, `appR`, `lamIn`, `fexprIn`, `evalIn`).

**Wand's claim**: `EqM` is *not contextually sound*. There is a
context that distinguishes a β-equivalent pair on convergence.

We mechanize this directly: define `EqM`, then exhibit a concrete
`EqM`-related pair `(M, N)` with `Converges M` and `¬ Converges N`.

## 2. How to build & explore

```sh
cd fexpr-trivial-mechanized
lake build               # 11 jobs, sorry-free
```

Open `FexprTrivial/EqM.lean` and place the cursor at the bottom —
`EqM_not_convergenceSound` is the headline. It's a 6-line proof.
Hover on the named lemmas it uses and jump to definition.

## 3. File-by-file tour

The dependency order, from leaves to the headline:

```
Term ── Subst ── Coding ── Reduction
                    │
                    ├── LemmaOne ──┐
                    │              ├── Determinism ──┐
                    │              │                 │
                    └── Theorem1Concrete ────────────┴── EqM  ←  headline
```

### Calculus foundations

- **`Term.lean`** (~130 LOC) — Inductive `Term` with five constructors
  (`var`, `lam`, `app`, `fexpr`, `eval`); free variables (`fv`) and
  the `closed` predicate. Named variables, intentionally — α-distinct
  terms must be representable as syntactically distinct, since the
  discriminator observes syntax.

- **`Subst.lean`** (~245 LOC) — `substClosed` (naive substitution,
  sound when the substituted term is closed). All our reductions stay
  closed, so this suffices.

- **`Coding.lean`** (~135 LOC) — The Mogensen–Scott encoding `⌜·⌝`:

      ⌜x⌝       = λabcde. a x
      ⌜M N⌝     = λabcde. b ⌜M⌝ ⌜N⌝
      ⌜λx.M⌝    = λabcde. c (λx. ⌜M⌝)
      ⌜fexpr M⌝ = λabcde. d ⌜M⌝
      ⌜eval M⌝  = λabcde. e ⌜M⌝

  with reserved names `__a__ … __e__` (`codeA`–`codeE`). Free-variable
  inclusion `mem_fv_encode` and `closed_encode` are established here.

### Operational semantics

- **`Reduction.lean`** (~290 LOC) — `Step` (CBV β + reify + reflect
  + structural congruence), `StepStar`, `Converges`, `IsValue`, plus
  inversion lemmas (`step_eval_inv`, `step_app_inv`,
  `stepStar_value_eq` etc.) used by the determinism proof.

### The argument

- **`LemmaOne.lean`** (~180 LOC) — `Term.encode_injective`:
  `⌜M⌝ = ⌜N⌝ → M = N`. A 5×5 case analysis: distinct head constructors
  produce distinct encoding markers (codeA vs codeB vs …), and equal
  markers force equal sub-encodings, which yield equal sub-terms by
  induction. The `step_deterministic` proof uses this in its reflect
  case to align the two reducts.

- **`Theorem1Concrete.lean`** (~530 LOC) — Defines `divBody` (a fexpr
  body that branches on the encoding's marker) and traces its
  reduction on a specific β-equivalent pair:

      termLHS  =  (λx.x)(λy.y)        -- β-redex
      termRHS  =  λy.y                -- β-reduct

  with `Step termLHS termRHS` by `termLHS_step_termRHS`. The cascades:

  - `termRHS_cascade_to_idA` — `(fexpr divBody) termRHS  →*  idA`
    (a value), routed through the encoding's `codeC` marker.
  - `termLHS_cascade_to_omega` — `(fexpr divBody) termLHS  →*  Ω`,
    routed through `codeB` into `divLam`'s two-argument abyss.

  `omega_diverges` is also proved here. This file is repetitive by
  design: each β-substitution step is its own named lemma.

- **`Determinism.lean`** (~125 LOC) — Three theorems:

  - `step_deterministic`: `Step M N₁ → Step M N₂ → N₁ = N₂`. Case
    analysis on the two `Step`s, with `step_value_absurd` /
    `step_lam_absurd` / `Term.encode_injective` ruling out impossible
    combinations.
  - `stepStar_align`: if `M →* W` and `M →* V` (V a value), then
    `W →* V`. The two paths share a common prefix; values can't step.
  - `not_converges_of_stepStar_diverges`: corollary — `M →* W`
    plus `¬ Converges W` gives `¬ Converges M`.

  This is what upgrades "the unique reduction reaches Ω" to
  "doesn't converge."

- **`EqM.lean`** (~85 LOC) — The headline file:

  - `EqM`: inductive closure under `Step` + refl/sym/trans + the five
    congruence rules.
  - `EqM_relates_β_pair : EqM termLHS termRHS` — single `Step.beta`.
  - `ConvergenceSound R := ∀ M N, R M N → (Converges M ↔ Converges N)`
    — Wand's notion of soundness.
  - `EqM_not_convergenceSound`: the headline. 6-line proof: lift the
    β-pair via `appR` to the two reflective contexts; one converges
    by `fexprDiv_termRHS_converges`; the other doesn't, by
    `not_converges_of_stepStar_diverges` applied to
    `termLHS_cascade_to_omega` and `omega_diverges`.
  - `wand_unsoundness`: any `R` containing `EqM` is also not
    convergence-sound.

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
4. Determinism is the substantive technical ingredient: ~125 LOC of
   careful case analysis on `Step`.

## 5. Reading the key proofs

### `Term.encode_injective` (`LemmaOne.lean`)

Pattern: induct on `M`; for each constructor, case-split on `N`. Most
sub-cases produce a constructor mismatch on the encoding marker and
discharge via `decide` (the reserved names are pairwise distinct
`Name`s). The matching cases recurse on sub-terms via the IH.

The auto-generated `Term.app.injEq` / `Term.lam.injEq` / `Term.var.injEq`
simp lemmas turn a wrapped equation into a tuple of sub-equations in
one `simp only`.

### `step_deterministic` (`Determinism.lean`)

Worth understanding the `induction h₁ generalizing N₂` idiom: without
`generalizing`, the IH would have a *fixed* `N₂` from the outer
context and couldn't be instantiated at the recursive step's own
`N₂`. With `generalizing`, each case's IH is `∀ N₂, Step Mop N₂ →
Mop' = N₂` — exactly what we need to align with `cases h₂`.

The `reflect` case is the only one that can't use direct `cases`:
its constructor input shape is `Step (.eval M.encode) M`, and
`cases h₂` asks Lean to unify `M.encode` with another `M'.encode`,
which it can't do for arbitrary terms. `step_eval_inv` packages this
as a disjunction with the equation as a hypothesis, sidestepping the
issue; `Term.encode_injective` then closes it.

### The cascades (`Theorem1Concrete.lean`)

Each cascade step is a named lemma. Read `termRHS_cascade_to_idA` for
the overall structure: `apply StepStar.step _ _ _ <step_lemma>`
repeated. Individual step lemmas (`termRHS_step_codeA`,
`termRHS_step_codeB`, …) each do one `Step.beta` substitution. The
substitutions either leave the body unchanged (closed body) or
replace one free occurrence of a `codeX` marker with the corresponding
selector.

The `Step.appL` lifts (e.g., the `(Step.appL _ _ _ termRHS_step_codeA)`
inside `cascade_step_codeA`) propagate a step inside the deeply
nested applications `((((c idA) divLam) constId) idA) idA` — five
function applications stacked, so up to 4 layers of `appL` lifting
are needed before reaching the active β-redex.

### `EqM_not_convergenceSound` (`EqM.lean`)

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

Each line corresponds to one English-language step of Wand's
argument: lift the β-relation through the reflective context, recall
that one side converges and the other doesn't, derive the
contradiction.

## 6. Scope

This mechanizes the negative result for **one specific β-equivalent
pair**. Generalizing to "for any closed M ≠ N, exhibit a context
distinguishing them on convergence" requires a recursive in-calculus
discriminator — an `eq?` built within the calculus that reduces to a
Church-true on a matching code and diverges otherwise. `divBody` only
handles distinct head-constructor pairs.
