/-
  βᵥ-equivalence: pure call-by-value β-reduction (no reify, no reflect).

  This is the equivalence we want to *recover* as contextual equivalence
  in the gated calculus. Defined on all `Term`s — terms with `fexpr` or
  `eval` in them are simply stuck under `BetaStep` (no head rule applies),
  which is fine.

  βᵥ-equivalence is the symmetric-transitive-reflexive closure of
  βᵥ-reduction with full congruence. (Reduction itself is value-restricted
  at the redex but congruent everywhere — the standard "βᵥ" of Plotkin 1975.)
-/
import FexprTrivial.Term
import FexprTrivial.Subst
import FexprTrivial.Reduction
namespace FexprTrivial

/-- One step of βᵥ-reduction. Same redex as `Step.beta`; full congruence.

    `BetaStep.beta` requires `V.closed` to keep the naive `substClosed`
    sound under congruence (in particular under `lamIn`, which can place
    a redex underneath a binder where capture would otherwise be
    possible). This restricts BetaEq to the closed-redex sub-relation
    of full βᵥ — sufficient for the closed-only headline. -/
inductive BetaStep : Term → Term → Prop where
  | beta    (x : Name) (M V : Term) : IsValue V → V.closed →
      BetaStep (.app (.lam x M) V) (M.substClosed x V)
  | appL    (M M' N : Term) : BetaStep M M' → BetaStep (.app M N) (.app M' N)
  | appR    (M N N' : Term) : BetaStep N N' → BetaStep (.app M N) (.app M N')
  | lamIn   (x : Name) (M M' : Term) : BetaStep M M' →
      BetaStep (.lam x M) (.lam x M')
  | fexprIn (M M' : Term) : BetaStep M M' → BetaStep (.fexpr M) (.fexpr M')
  | evalIn  (M M' : Term) : BetaStep M M' → BetaStep (.eval M) (.eval M')

/-- βᵥ-equivalence: equivalence-closure of `BetaStep`. -/
inductive BetaEq : Term → Term → Prop where
  | refl  (M : Term) : BetaEq M M
  | sym   (M N : Term) : BetaEq M N → BetaEq N M
  | trans (M N P : Term) : BetaEq M N → BetaEq N P → BetaEq M P
  | step  (M N : Term) : BetaStep M N → BetaEq M N

@[inherit_doc] notation:50 M " ≡β " N => BetaEq M N

theorem BetaEq.of_step {M N : Term} (h : BetaStep M N) : M ≡β N :=
  .step _ _ h

/-! ### `BetaStepRestricted`: the structural-recursion-friendly subset

  The full `BetaStep` has six constructors; for the recovery theorem
  via applicative bisimilarity, three of them (`appL`, `appR`,
  `evalIn`) require congruence-of-bisim machinery (Howe's method) we
  haven't proven, and one (`lamIn`) requires well-founded recursion
  with substitutivity-of-bisim that hits the same obstacle. Restricting
  to `beta` and `fexprIn` gives a relation whose `BetaStepRestricted →
  AppBisim` lift is structurally recursive and sorry-free.

  `BetaStepRestricted` covers the head β-redex case and rewrites
  *inside* fexpr bodies (recursively). It does *not* cover lambda-
  internal rewrites (`lamIn`), application-context rewrites (`appL`,
  `appR`), or eval-context rewrites (`evalIn`). The headline
  `beta_recovery_restricted` is stated over this restricted relation. -/

inductive BetaStepRestricted : Term → Term → Prop where
  | beta    (x : Name) (M V : Term) : IsValue V → V.closed →
      BetaStepRestricted (.app (.lam x M) V) (M.substClosed x V)
  | fexprIn (M M' : Term) : BetaStepRestricted M M' →
      BetaStepRestricted (.fexpr M) (.fexpr M')

/-- Embedding into the full `BetaStep`. -/
theorem BetaStepRestricted.toBetaStep {M N : Term}
    (h : BetaStepRestricted M N) : BetaStep M N := by
  induction h with
  | beta x M V hVval hVcl => exact .beta x M V hVval hVcl
  | fexprIn _ _ _ ih => exact .fexprIn _ _ ih

/-! ### Closure preservation for βᵥ-reduction -/

/-- Forward direction: a β-step does not introduce new free variables. -/
theorem betaStep_fv_subset {M N : Term} (h : BetaStep M N) :
    ∀ y, y ∈ N.fv → y ∈ M.fv := by
  induction h with
  | beta x M V _ hVcl =>
      intro y hy
      rcases Term.mem_fv_substClosed hy with ⟨hyM, hyx⟩ | hyV
      · simp only [Term.fv_app, List.mem_append,
                   Term.fv_lam, List.mem_filter, decide_not, Bool.not_eq_eq_eq_not,
                   Bool.not_true, decide_eq_false_iff_not]
        left; exact ⟨hyM, hyx⟩
      · unfold Term.closed at hVcl
        rw [hVcl] at hyV; cases hyV
  | appL M M' N _ ih =>
      intro y hy
      simp only [Term.fv_app, List.mem_append] at hy ⊢
      rcases hy with h1 | h2
      · exact Or.inl (ih y h1)
      · exact Or.inr h2
  | appR M N N' _ ih =>
      intro y hy
      simp only [Term.fv_app, List.mem_append] at hy ⊢
      rcases hy with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (ih y h2)
  | lamIn x M M' _ ih =>
      intro y hy
      rw [Term.mem_fv_lam_iff] at hy ⊢
      exact ⟨ih y hy.1, hy.2⟩
  | fexprIn M M' _ ih =>
      intro y hy
      simp only [Term.fv_fexpr] at hy ⊢
      exact ih y hy
  | evalIn M M' _ ih =>
      intro y hy
      simp only [Term.fv_eval] at hy ⊢
      exact ih y hy

/-- Reverse direction: a β-step does not eliminate free variables either
    (under our `V.closed` discipline). -/
theorem betaStep_fv_subset_rev {M N : Term} (h : BetaStep M N) :
    ∀ y, y ∈ M.fv → y ∈ N.fv := by
  induction h with
  | beta x M V _ hVcl =>
      intro y hy
      simp only [Term.fv_app, Term.fv_lam, List.mem_append, List.mem_filter,
                 decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
                 decide_eq_false_iff_not] at hy
      rcases hy with ⟨hyM, hyx⟩ | hyV
      · exact Term.mem_fv_substClosed_rev hVcl hyM hyx
      · unfold Term.closed at hVcl
        rw [hVcl] at hyV; cases hyV
  | appL M M' N _ ih =>
      intro y hy
      simp only [Term.fv_app, List.mem_append] at hy ⊢
      rcases hy with h1 | h2
      · exact Or.inl (ih y h1)
      · exact Or.inr h2
  | appR M N N' _ ih =>
      intro y hy
      simp only [Term.fv_app, List.mem_append] at hy ⊢
      rcases hy with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (ih y h2)
  | lamIn x M M' _ ih =>
      intro y hy
      rw [Term.mem_fv_lam_iff] at hy ⊢
      exact ⟨ih y hy.1, hy.2⟩
  | fexprIn M M' _ ih =>
      intro y hy
      simp only [Term.fv_fexpr] at hy ⊢
      exact ih y hy
  | evalIn M M' _ ih =>
      intro y hy
      simp only [Term.fv_eval] at hy ⊢
      exact ih y hy

theorem betaStep_preserves_closed {M N : Term} :
    BetaStep M N → M.closed → N.closed := by
  intro h hcl
  unfold Term.closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y hy
  have := betaStep_fv_subset h y hy
  unfold Term.closed at hcl; rw [hcl] at this; cases this

theorem betaStep_reflects_closed {M N : Term} :
    BetaStep M N → N.closed → M.closed := by
  intro h hcl
  unfold Term.closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y hy
  have := betaStep_fv_subset_rev h y hy
  unfold Term.closed at hcl; rw [hcl] at this; cases this

/-- Closure invariance under βᵥ-equivalence. -/
theorem betaEq_closed_iff {M N : Term} : BetaEq M N → (M.closed ↔ N.closed) := by
  intro h
  induction h with
  | refl _ => exact Iff.rfl
  | sym _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  | step _ _ hStep =>
      exact ⟨betaStep_preserves_closed hStep, betaStep_reflects_closed hStep⟩

/-! ### Useful syntactic lemmas about `BetaStep` -/

/-- Variables don't admit β-steps (no constructor produces `.var` on the LHS). -/
theorem betaStep_var_absurd {x : Name} {N : Term} (h : BetaStep (.var x) N) : False := by
  cases h

/-- β-step preserves `IsValue`: a value reduces only to a value. -/
theorem betaStep_preserves_isValue {M N : Term}
    (hMVal : IsValue M) (hStep : BetaStep M N) : IsValue N := by
  induction hMVal generalizing N with
  | lam _ _ =>
      cases hStep with
      | lamIn _ _ _ _ => exact .lam _ _
  | fexpr _ _ ih =>
      cases hStep with
      | fexprIn _ _ h_inner => exact .fexpr _ (ih h_inner)

/-- **Substitution is a `BetaStep`-congruence under closed values.**
    The β-redex case uses `substClosed_commute` to commute the redex-body's
    inner substitution with the outer substitution. The other cases are
    structural recursion. -/
theorem substClosed_respects_betaStep {b b' : Term} {x : Name} {V : Term}
    (hVcl : V.closed) (hStep : BetaStep b b') :
    BetaStep (b.substClosed x V) (b'.substClosed x V) := by
  induction hStep with
  | beta y body W hWVal hWcl =>
      -- b = .app (.lam y body) W → b' = body.substClosed y W
      have hWcl' : (W.substClosed x V).closed := by
        unfold Term.closed
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro z hz
        rcases Term.mem_fv_substClosed hz with ⟨hzW, _⟩ | hzV
        · unfold Term.closed at hWcl; rw [hWcl] at hzW; cases hzW
        · unfold Term.closed at hVcl; rw [hVcl] at hzV; cases hzV
      have hWval' : IsValue (W.substClosed x V) := substClosed_isValue hWVal
      by_cases h : y = x
      · subst h
        -- LHS subst: .app (.lam y body) (W.substClosed y V)
        -- RHS subst: (body.substClosed y W).substClosed y V = body.substClosed y W
        --   (since y is no longer free after body.substClosed y W)
        rw [Term.substClosed_app, Term.substClosed_lam_self]
        rw [show (body.substClosed y W).substClosed y V = body.substClosed y W from by
              apply Term.substClosed_not_free
              intro hyM
              rcases Term.mem_fv_substClosed hyM with ⟨_, hne⟩ | hyV
              · exact hne rfl
              · unfold Term.closed at hWcl; rw [hWcl] at hyV; cases hyV]
        rw [show body.substClosed y W = body.substClosed y (W.substClosed y V) from by
              rw [Term.substClosed_of_closed W hWcl y V]]
        exact .beta y body (W.substClosed y V) hWval' hWcl'
      · rw [Term.substClosed_app, Term.substClosed_lam_other h]
        rw [show (body.substClosed y W).substClosed x V
              = (body.substClosed x V).substClosed y W from by
              rw [Term.substClosed_commute (fun heq => h heq.symm) hVcl hWcl]
              -- substClosed_commute gives (body.subst x V).subst y W = (body.subst y W).subst x V
              -- We want (body.subst y W).subst x V = (body.subst x V).subst y W (the symm)
              ]
        rw [show W.substClosed x V = W from Term.substClosed_of_closed W hWcl x V]
        exact .beta y (body.substClosed x V) W hWVal hWcl
  | appL M M' N _ ih =>
      rw [Term.substClosed_app, Term.substClosed_app]
      exact .appL _ _ _ ih
  | appR M N N' _ ih =>
      rw [Term.substClosed_app, Term.substClosed_app]
      exact .appR _ _ _ ih
  | lamIn y M M' _ ih =>
      by_cases h : y = x
      · rw [h, Term.substClosed_lam_self, Term.substClosed_lam_self]
        rw [← h]
        exact .lamIn _ _ _ ‹BetaStep M M'›
      · rw [Term.substClosed_lam_other h, Term.substClosed_lam_other h]
        exact .lamIn _ _ _ ih
  | fexprIn M M' _ ih =>
      rw [Term.substClosed_fexpr, Term.substClosed_fexpr]
      exact .fexprIn _ _ ih
  | evalIn M M' _ ih =>
      rw [Term.substClosed_eval, Term.substClosed_eval]
      exact .evalIn _ _ ih

/-- **βᵥ-equivalence is preserved by closed substitution.** Direct lift
    of `substClosed_respects_betaStep` over the equivalence-closure
    constructors of `BetaEq`. -/
theorem substClosed_respects_betaEq {b b' : Term} {x : Name} {V : Term}
    (hVcl : V.closed) (h : BetaEq b b') :
    BetaEq (b.substClosed x V) (b'.substClosed x V) := by
  induction h with
  | refl _ => exact .refl _
  | sym _ _ _ ih => exact .sym _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | step _ _ hStep => exact .step _ _ (substClosed_respects_betaStep hVcl hStep)

/-! ### `BetaEq` congruence lifts

  `BetaStep` has all the structural-congruence constructors (lamIn,
  appL, appR, fexprIn, evalIn). These lift to `BetaEq` by induction on
  the equivalence-closure. Useful for building up `BetaEq` chains
  through term contexts without going through the full single-hole
  `Context` machinery. -/

theorem BetaEq.lamIn (x : Name) {M N : Term} (h : BetaEq M N) :
    BetaEq (.lam x M) (.lam x N) := by
  induction h with
  | refl _ => exact .refl _
  | sym _ _ _ ih => exact .sym _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | step _ _ hStep => exact .step _ _ (.lamIn _ _ _ hStep)

theorem BetaEq.appL (N : Term) {M M' : Term} (h : BetaEq M M') :
    BetaEq (.app M N) (.app M' N) := by
  induction h with
  | refl _ => exact .refl _
  | sym _ _ _ ih => exact .sym _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | step _ _ hStep => exact .step _ _ (.appL _ _ _ hStep)

theorem BetaEq.appR (M : Term) {N N' : Term} (h : BetaEq N N') :
    BetaEq (.app M N) (.app M N') := by
  induction h with
  | refl _ => exact .refl _
  | sym _ _ _ ih => exact .sym _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | step _ _ hStep => exact .step _ _ (.appR _ _ _ hStep)

theorem BetaEq.fexprIn {M N : Term} (h : BetaEq M N) :
    BetaEq (.fexpr M) (.fexpr N) := by
  induction h with
  | refl _ => exact .refl _
  | sym _ _ _ ih => exact .sym _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | step _ _ hStep => exact .step _ _ (.fexprIn _ _ hStep)

theorem BetaEq.evalIn {M N : Term} (h : BetaEq M N) :
    BetaEq (.eval M) (.eval N) := by
  induction h with
  | refl _ => exact .refl _
  | sym _ _ _ ih => exact .sym _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | step _ _ hStep => exact .step _ _ (.evalIn _ _ hStep)

theorem BetaEq.app {M M' N N' : Term}
    (hM : BetaEq M M') (hN : BetaEq N N') : BetaEq (.app M N) (.app M' N') :=
  .trans _ _ _ (.appL N hM) (.appR M' hN)

/-! ### Value-side substitution congruence

  `body[V/x]` and `body[V'/x]` are βᵥ-equivalent when `V` and `V'` are
  βᵥ-related (and both closed). Proven by induction on `body`: each
  occurrence of `x` in `body` becomes a copy of `V` (resp. `V'`), and
  the relating `BetaEq` lifts through the surrounding context.

  The companion to `substClosed_respects_betaStep` (which moves an
  inner BetaStep across a substitution); this one moves an outer
  BetaStep on the substituted value across all occurrences. Note the
  conclusion is `BetaEq`, not `BetaStep`, because `body` may contain
  zero or many occurrences of `x` (and multi-occurrence requires a
  chain of β-steps).
-/
theorem val_substClosed_respects_betaEq {V V' : Term}
    (_hVcl : V.closed) (_hV'cl : V'.closed) (h : BetaEq V V') :
    ∀ (body : Term) (x : Name),
      BetaEq (body.substClosed x V) (body.substClosed x V') := by
  intro body x
  induction body with
  | var z =>
      by_cases hzx : z = x
      · subst hzx; rw [Term.substClosed_var_self, Term.substClosed_var_self]; exact h
      · rw [Term.substClosed_var_other hzx, Term.substClosed_var_other hzx]
        exact .refl _
  | lam z body' ih =>
      by_cases hzx : z = x
      · subst hzx; rw [Term.substClosed_lam_self, Term.substClosed_lam_self]
        exact .refl _
      · rw [Term.substClosed_lam_other hzx, Term.substClosed_lam_other hzx]
        exact BetaEq.lamIn _ ih
  | app L R ihL ihR =>
      rw [Term.substClosed_app, Term.substClosed_app]
      exact BetaEq.app ihL ihR
  | fexpr body' ih =>
      rw [Term.substClosed_fexpr, Term.substClosed_fexpr]
      exact BetaEq.fexprIn ih
  | eval body' ih =>
      rw [Term.substClosed_eval, Term.substClosed_eval]
      exact BetaEq.evalIn ih

/-- The single-step special case: when the outer relation is a `BetaStep`. -/
theorem val_substClosed_respects_betaStep {V V' : Term}
    (hVcl : V.closed) (hV'cl : V'.closed) (h : BetaStep V V') :
    ∀ (body : Term) (x : Name),
      BetaEq (body.substClosed x V) (body.substClosed x V') :=
  val_substClosed_respects_betaEq hVcl hV'cl (BetaEq.step _ _ h)

end FexprTrivial
