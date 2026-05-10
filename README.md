# fexpr-trivial-mechanized

A Lean 4 mechanization of Wand 1998, *The Theory of Fexprs is Trivial*
(Lisp and Symbolic Computation 10(3): 189–199).

## Status

Sorry-free; `lake build` is green at 15 jobs on Lean v4.29.1.

## Headline

In any reflective λ-calculus with `fexpr` and `eval`, the natural
equational theory `EqM` — closed under β + reify + reflect rewrites
plus full structural congruence — is **not contextually sound**. A
single reflective context distinguishes a β-equivalent pair on
convergence:

> `EqM ((fexpr divBody) termRHS) ((fexpr divBody) termLHS)`
>   ∧ `Converges ((fexpr divBody) termRHS)`
>   ∧ `¬ Converges ((fexpr divBody) termLHS)`

This is the canonical form of Wand's negative result. It implies
that no equational theory closed under `EqM` can be convergence-sound.

We mechanize:

1. **Wand Lemma 1** — basic facts about the Mogensen–Scott encoding
   `⌜·⌝`: closure preservation, free-variable preservation, and
   structural injectivity (`Term.encode_injective` in `LemmaOne.lean`).

2. **Value-level distinguishability (general)** — for any
   syntactically-distinct closed `M, N`, the un-gated reflective
   context `(fexpr idBody) ·` reduces them to distinct values
   (`wand_distinguishes_distinct_terms` in `WandValue.lean`).

3. **Step-determinism + alignment** — the small-step CBV reduction
   relation is fully deterministic; from this, "M reduces to a
   divergent term W" implies "M doesn't converge"
   (`step_deterministic`, `not_converges_of_stepStar_diverges` in
   `Determinism.lean`).

4. **Concrete convergence-distinguishing cascade** — for the
   β-equivalent pair `termLHS = (λx.x)(λy.y) ≡β termRHS = λy.y`, the
   reflective context `(fexpr divBody) ·` reduces `termRHS` to the
   value `idA` and reduces `termLHS` to `Ω` (witness `omega_diverges`)
   in `Theorem1Concrete.lean`.

5. **Convergence-unsoundness of `EqM`** — combining the cascade with
   step-determinism gives `Converges` on one side and `¬ Converges`
   on the other for an `EqM`-related pair, refuting
   `ConvergenceSound EqM`. This rules out any equational theory
   containing `EqM` from being convergence-sound
   (`EqM_not_convergenceSound`, `wand_unsoundness` in `EqM.lean`).

6. **Abstract collapse** — for the (much stronger) `ValueSound` notion,
   any compatible value-sound `R` cannot equate distinct closed terms
   (`wand_collapse_abstract`, `wand_collapse_syntactic` in `EqM.lean`).
   This is a different headline pitched at a stricter soundness
   notion than Wand's; the convergence-soundness refutation above is
   the one matching the paper's actual claim.

## Layout

```
FexprTrivial.lean                 -- top-level reexport
FexprTrivial/
  Term.lean                       -- term syntax, fv, closed
  Alpha.lean                      -- α-equivalence (env-based)
  Subst.lean                      -- substClosed
  Coding.lean                     -- Mogensen–Scott encoding ⌜·⌝
  Reduction.lean                  -- Step, StepStar, Converges, IsValue
  Beta.lean                       -- BetaStep, BetaEq, full congruence
  LemmaOne.lean                   -- Wand Lemma 1.2 + 1.3 (encode_injective)
  Determinism.lean                -- step_deterministic + alignment
  Discriminator.lean              -- idBody + reduction cascade
  WandValue.lean                  -- value-level Theorem 1 (general)
  Theorem1Concrete.lean           -- convergence-level cascade for one β-pair
  EqM.lean                        -- Eq_M + ¬ ConvergenceSound (headline)
```

Self-contained Lake project, Lean v4.29.1, no Mathlib.

## Build

```
lake build
```

## What is *not* mechanized

1. **α-respect of the encoding.** We use syntactic equality throughout.
   Lifting "syntactically distinct" to "not α-equivalent" requires
   either a De Bruijn-flavored encoding (so codes become α-canonical)
   or substitution/encoding-respect lemmas extending `Alpha.lean`.

2. **General convergence-level Theorem 1.** The convergence-asymmetry
   witness uses the specific β-pair `termLHS / termRHS`. Generalizing
   it to "for any α-distinct closed M, N, exhibit a distinguishing
   context" is the recursive in-calculus discriminator `eq?` work,
   left as future work.
