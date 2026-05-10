/-
  Wand's equational theory `EqM` and the mechanized form of Wand's
  negative result.

  `EqM` is the natural equational theory of the reflective λ-calculus:
  the inductive closure under `Step` (which already covers β + reify
  + reflect) plus the equivalence rules and full structural congruence
  (`appL`, `appR`, `lamIn`, `fexprIn`, `evalIn`).

  Wand's claim: `EqM` is **not contextually sound**. We mechanize the
  convergence form: there exist closed `M, N` with `EqM M N` such that
  `Converges M ∧ ¬ Converges N`. The witness pair is `(.app (.fexpr divBody)
  termRHS, .app (.fexpr divBody) termLHS)`, where `(termLHS, termRHS)`
  is a β-redex / reduct pair from `Theorem1Concrete.lean`. The
  reflective context routes the two terms to `idA` (a value) and `Ω`
  (a divergent term) respectively.

  Sorry-free.
-/
import FexprTrivial.Term
import FexprTrivial.Subst
import FexprTrivial.Coding
import FexprTrivial.Reduction
import FexprTrivial.Determinism
import FexprTrivial.Theorem1Concrete
namespace FexprTrivial

/-! ### `EqM`: the smallest reflective-rewrite-respecting equivalence

  Closure of `Step` under reflexive/symmetric/transitive equivalence
  plus full structural congruence. This is the "natural" equational
  theory of the reflective λ-calculus — exactly the relation Wand
  argues is unsound.
-/

inductive EqM : Term → Term → Prop where
  | step    (M N : Term) : Step M N → EqM M N
  | refl    (M : Term)   : EqM M M
  | sym     (M N : Term) : EqM M N → EqM N M
  | trans   (M N P : Term) : EqM M N → EqM N P → EqM M P
  | appL    (M M' N : Term) : EqM M M' → EqM (.app M N) (.app M' N)
  | appR    (M N N' : Term) : EqM N N' → EqM (.app M N) (.app M N')
  | lamIn   (x : Name) (M M' : Term) : EqM M M' → EqM (.lam x M) (.lam x M')
  | fexprIn (M M' : Term) : EqM M M' → EqM (.fexpr M) (.fexpr M')
  | evalIn  (M M' : Term) : EqM M M' → EqM (.eval M) (.eval M')

/-- `EqM` relates the β-redex `(λx.x)(λy.y)` and its reduct `λy.y`. -/
theorem EqM_relates_β_pair : EqM termLHS termRHS :=
  .step _ _ termLHS_step_termRHS

/-- An equational theory `R` is *convergence-sound* iff `R`-related
    terms have the same convergence behavior. This is the soundness
    notion Wand's Theorem 1 targets. -/
def ConvergenceSound (R : Term → Term → Prop) : Prop :=
  ∀ {M N : Term}, R M N → (Converges M ↔ Converges N)

/-- **`EqM` is not convergence-sound.** The β-pair lifts via `appR`
    to an `EqM` relation between the two reflective contexts; one
    converges to `idA`, the other reaches the divergent `Ω` along its
    unique reduction path (`Step`-determinism upgrades that to
    `¬ Converges`). Convergence-soundness would force them to agree. -/
theorem EqM_not_convergenceSound : ¬ ConvergenceSound EqM := by
  intro hSound
  have hEq : EqM (.app (.fexpr divBody) termRHS) (.app (.fexpr divBody) termLHS) :=
    .appR _ _ _ (.sym _ _ EqM_relates_β_pair)
  have hConv_LHS : Converges (.app (.fexpr divBody) termRHS) :=
    fexprDiv_termRHS_converges
  have hNotConv_RHS : ¬ Converges (.app (.fexpr divBody) termLHS) :=
    not_converges_of_stepStar_diverges termLHS_cascade_to_omega omega_diverges
  exact hNotConv_RHS ((hSound hEq).mp hConv_LHS)

/-- **Wand's punchline.** No equational theory containing `EqM`
    (β + reify + reflect + full congruence) can be convergence-sound. -/
theorem wand_unsoundness :
    ∀ {R : Term → Term → Prop},
      (∀ {M N : Term}, EqM M N → R M N) →
      ¬ ConvergenceSound R := by
  intro R hContains hSound
  apply EqM_not_convergenceSound
  intro M N hEqM
  exact hSound (hContains hEqM)

end FexprTrivial
