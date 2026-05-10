# fexpr-trivial-mechanized

A Lean 4 mechanization of Wand 1998, *The Theory of Fexprs is Trivial*
(Lisp and Symbolic Computation 10(3): 189–199).

## Status

Sorry-free; `lake build` is green at 11 jobs on Lean v4.29.1. Around
1730 LOC, no Mathlib.

## Headline

In the call-by-value λ-calculus extended with `fexpr` and `eval`, the
natural equational theory `EqM` — closed under β + reify + reflect +
full structural congruence — is **not contextually sound**. A single
reflective context distinguishes a β-equivalent pair on convergence:

```
EqM ((fexpr divBody) termRHS) ((fexpr divBody) termLHS)
   ∧ Converges ((fexpr divBody) termRHS)
   ∧ ¬ Converges ((fexpr divBody) termLHS)
```

with `termLHS = (λx.x)(λy.y) ≡β λy.y = termRHS`. See
`EqM_not_convergenceSound` in `FexprTrivial/EqM.lean`.

Corollary: any equational theory containing `EqM` is also not
convergence-sound (`wand_unsoundness`).

## Layout

```
FexprTrivial.lean                 -- top-level reexport
FexprTrivial/
  Term.lean                       -- term syntax, fv, closed
  Subst.lean                      -- substClosed
  Coding.lean                     -- Mogensen–Scott encoding ⌜·⌝
  Reduction.lean                  -- Step, StepStar, Converges, IsValue
  LemmaOne.lean                   -- encode_injective (Wand Lemma 1.3)
  Determinism.lean                -- step_deterministic + alignment
  Theorem1Concrete.lean           -- divBody cascade for one β-pair
  EqM.lean                        -- EqM + ¬ ConvergenceSound (headline)
```

## Build

```
lake build
```

## Scope

This artifact mechanizes Wand's negative result for **one specific
β-equivalent pair**. Generalizing to "for any closed M ≠ N, exhibit
a distinguishing context" requires a recursive in-calculus
discriminator (an `eq?` built within the calculus that converges on
a target code and diverges otherwise). That extension is not
mechanized here.
