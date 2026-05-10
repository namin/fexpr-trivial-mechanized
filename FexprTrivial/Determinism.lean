/-
  Step-determinism for the small-step CBV reflective calculus.

  The reduction relation `Step` is fully deterministic: from any term
  there is at most one Step-reduct. This holds without a closedness
  hypothesis because the value-side and closedness conditions are
  baked into the rule applicability (`beta` requires `IsValue V` and
  `V.closed`; `reflect` requires `M.closed`; `reify` requires the
  operator's inner to be a value).

  From determinism we derive:
    - `stepStar_align`: if `M →* W` and `M →* V` (V a value), then
      `W →* V`. The two reduction paths share a common prefix; values
      can't step, so the V-path is the longer one.
    - `not_converges_of_stepStar_diverges`: if `M →* W` and `W` does
      not converge, neither does `M`.

  Together these upgrade asymmetric reduction outcomes (one path to a
  value, another path to a divergent term) into the canonical form of
  unsoundness: `Converges` on one side, `¬ Converges` on the other.

  Sorry-free.
-/
import FexprTrivial.Term
import FexprTrivial.Subst
import FexprTrivial.Coding
import FexprTrivial.Reduction
import FexprTrivial.LemmaOne
namespace FexprTrivial

/-- **Step is deterministic.** Given `Step M N₁` and `Step M N₂`,
    the reducts coincide. The proof is a careful case analysis on the
    two `Step`s, ruling out impossible combinations via:

      * `step_value_absurd` (values don't step),
      * `step_lam_absurd` (λ-abstractions don't step),
      * `step_eval_inv` + `Term.encode_injective` (the `reflect` rule's
        input shape pins down the source term up to encoding equality,
        hence syntactic equality by Lemma 1.3),
      * Lean's automatic constructor-mismatch handling (the rule
        applicability shapes are mutually exclusive at the term level).
-/
theorem step_deterministic : ∀ {M N₁ N₂ : Term},
    Step M N₁ → Step M N₂ → N₁ = N₂ := by
  intro M N₁ N₂ h₁
  induction h₁ generalizing N₂ with
  | beta x body V hVval hVcl =>
      intro h₂
      cases h₂ with
      | beta _ _ _ _ _ => rfl
      | appL _ _ _ hStep => exact (step_lam_absurd hStep).elim
      | appR _ _ _ _ hStep => exact (step_value_absurd hVval hStep).elim
  | reify V M hVval =>
      intro h₂
      cases h₂ with
      | reify _ _ _ => rfl
      | appL _ _ _ hStep =>
          cases hStep with
          | fexprIn _ _ hInner => exact (step_value_absurd hVval hInner).elim
  | reflect M hMcl =>
      intro h₂
      -- Use the inversion lemma to avoid Lean's "failed to solve equation" issue.
      rcases step_eval_inv h₂ with ⟨K, hMeq, _, hN₂eq⟩ | ⟨_, _, hStep⟩
      · -- reflect case: M.encode = K.encode → M = K → N₂ = K = M
        have : M = K := Term.encode_injective hMeq
        rw [hN₂eq, this]
      · -- evalIn case: Step M.encode ... but M.encode is a value
        exact (step_value_absurd (isValue_encode M) hStep).elim
  | appL Mop Mop' Nop hStep_op ih =>
      intro h₂
      cases h₂ with
      | beta _ _ _ _ _ => exact (step_lam_absurd hStep_op).elim
      | reify _ _ hVval =>
          exact (step_value_absurd (.fexpr _ hVval) hStep_op).elim
      | appL _ Mop_2' _ hStep_op_2 =>
          rw [ih hStep_op_2]
      | appR _ _ _ _ _ => exact (step_lam_absurd hStep_op).elim
  | appR x body Nop Nop' hStep_op ih =>
      intro h₂
      cases h₂ with
      | beta _ _ _ hVval _ => exact (step_value_absurd hVval hStep_op).elim
      | appL _ _ _ hStep => exact (step_lam_absurd hStep).elim
      | appR _ _ _ _ hStep_op_2 => rw [ih hStep_op_2]
  | fexprIn Mop Mop' hStep_op ih =>
      intro h₂
      cases h₂ with
      | fexprIn _ _ hStep_op_2 => rw [ih hStep_op_2]
  | evalIn Mop Mop' hStep_op ih =>
      intro h₂
      rcases step_eval_inv h₂ with ⟨K, hMop_eq, _, _⟩ | ⟨M_2', hN₂_eq, hStep_2⟩
      · -- reflect case: Mop = K.encode (value), but hStep_op steps Mop. Contradiction.
        rw [hMop_eq] at hStep_op
        exact (step_value_absurd (isValue_encode K) hStep_op).elim
      · -- evalIn vs evalIn: align via IH
        rw [hN₂_eq, ih hStep_2]

/-- **Reduction alignment via determinism.** If `M →* W` and `M →* V`
    with `V` a value, then `W →* V`. Proof: induct on `M →* W` and use
    `step_deterministic` at each step to align with the M-to-V path.
    The reflexive case uses that values don't step. -/
theorem stepStar_align :
    ∀ {M W V : Term}, IsValue V → StepStar M W → StepStar M V → StepStar W V := by
  intro M W V hV hMW
  induction hMW with
  | refl _ => intro h; exact h
  | step _ M' _ s rest ih =>
      intro hMV
      cases hMV with
      | refl _ =>
          -- M = V (a value), but `s : Step M M'` says M steps. Contradiction.
          exact (step_value_absurd hV s).elim
      | step _ N' _ s' rest_V =>
          have hNeq : M' = N' := step_deterministic s s'
          rw [← hNeq] at rest_V
          exact ih rest_V

/-- **Convergence to a known divergent term forces non-convergence.**
    If `M →* W` and `W` doesn't converge, then `M` doesn't converge.

    Combined with the `divBody` cascade: from
    `(.app (.fexpr divBody) termLHS) →* Ω` and `¬ Converges Ω`, we
    derive `¬ Converges ((.app (.fexpr divBody) termLHS))`. -/
theorem not_converges_of_stepStar_diverges :
    ∀ {M W : Term}, StepStar M W → ¬ Converges W → ¬ Converges M := by
  intro M W hMW hWdiv ⟨V, hVval, hMV⟩
  exact hWdiv ⟨V, hVval, stepStar_align hVval hMW hMV⟩

end FexprTrivial
