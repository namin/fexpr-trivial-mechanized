/-
  Discriminators for Wand's Theorem 1.

  Wand's argument hinges on a single fexpr-based context that turns its
  operand into a code (via `Step.reify`). The simplest such context is
  `(fexpr idBody) ·` where `idBody := λc. c`: applied to `M`, it
  reduces to `M.encode` itself, exposing the syntactic structure.

  Sorry-free.
-/
import FexprTrivial.Term
import FexprTrivial.Subst
import FexprTrivial.Coding
import FexprTrivial.Reduction
namespace FexprTrivial

/-! ### `idBody` — the simplest un-gated reflective body -/

/-- `idBody := λc. c`. The fexpr body that returns its operand-code. -/
def idBody : Term := .lam "c" (.var "c")

theorem idBody_closed : idBody.closed := rfl
theorem idBody_value : IsValue idBody := .lam _ _

/-! ### One-step lemmas for the `idBody` reduction cascade -/

/-- Step 1 of the cascade: reify on `(fexpr idBody) M`. -/
theorem reify_idBody (M : Term) :
    Step (.app (.fexpr idBody) M) (.app idBody M.encode) :=
  Step.reify idBody M idBody_value

/-- Step 2 of the cascade: β on `(λc. c) M.encode →β M.encode`. -/
theorem beta_idBody (M : Term) (hMcl : M.closed) :
    Step (.app idBody M.encode) M.encode := by
  have hVval : IsValue M.encode := isValue_encode M
  have hVcl : M.encode.closed := Term.closed_encode hMcl
  have h := Step.beta "c" (.var "c") M.encode hVval hVcl
  have heq : (Term.var "c").substClosed "c" M.encode = M.encode := by
    show (if "c" = "c" then M.encode else .var "c") = M.encode
    rw [if_pos rfl]
  rw [heq] at h
  exact h

/-- The two-step reduction `(fexpr idBody) M →* ⌜M⌝` for closed `M`. -/
theorem fexpr_idBody_stepStar (M : Term) (hMcl : M.closed) :
    StepStar (.app (.fexpr idBody) M) M.encode :=
  .step _ _ _ (reify_idBody M)
    (.step _ _ _ (beta_idBody M hMcl) (.refl _))

/-- The discriminating context's value-image: `(fexpr idBody) M` evaluates
    to a value (specifically `⌜M⌝`) for any closed `M`. -/
theorem converges_fexpr_idBody (M : Term) (hMcl : M.closed) :
    Converges (.app (.fexpr idBody) M) :=
  ⟨M.encode, isValue_encode M, fexpr_idBody_stepStar M hMcl⟩

end FexprTrivial
