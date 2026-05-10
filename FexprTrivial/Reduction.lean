/-
  Wand's small-step reduction (CBV β + reification + reflection).

  Wand presents reduction in Felleisen-context form `R[I] → R[I']`. We
  translate to structural congruence rules — equivalent for closed terms
  and easier to reason about inductively.

  The three head rules:
    β-value : (λx.M) V         → M[V/x]     when V is a value
    reify   : (fexpr V) M      → V ⌜M⌝       when V is a value
    reflect : eval ⌜M⌝         → M

  For session 2 we only require `substClosed` substitution (sound when V
  is closed; preserved by closed-program CBV reduction).
-/
import FexprTrivial.Term
import FexprTrivial.Subst
import FexprTrivial.Coding
namespace FexprTrivial

/-- Values: λ-abstractions and `fexpr`-wrapped values (Wand §2). -/
inductive IsValue : Term → Prop where
  | lam   (x : Name) (M : Term) : IsValue (.lam x M)
  | fexpr (V : Term) : IsValue V → IsValue (.fexpr V)

/-- Wand's three reduction rules + congruence.

    `Step.beta` requires `V.closed` so that the naive `substClosed` is
    sound (no capture of `V`'s free variables by binders in `M`). For
    closed top-level programs CBV reduction satisfies this invariant
    automatically — see `step_preserves_closed`. -/
inductive Step : Term → Term → Prop where
  | beta    (x : Name) (M V : Term) : IsValue V → V.closed →
      Step (.app (.lam x M) V) (M.substClosed x V)
  | reify   (V M : Term) : IsValue V →
      Step (.app (.fexpr V) M) (.app V M.encode)
  | reflect (M : Term) (hMcl : M.closed) :
      Step (.eval M.encode) M
  | appL    (M M' N : Term) : Step M M' → Step (.app M N) (.app M' N)
  | appR    (x : Name) (body N N' : Term) : Step N N' →
      Step (.app (.lam x body) N) (.app (.lam x body) N')
  | fexprIn (M M' : Term) : Step M M' → Step (.fexpr M) (.fexpr M')
  | evalIn  (M M' : Term) : Step M M' → Step (.eval M) (.eval M')

/-- Reflexive-transitive closure of `Step`. -/
inductive StepStar : Term → Term → Prop where
  | refl (M : Term) : StepStar M M
  | step (M M' N : Term) : Step M M' → StepStar M' N → StepStar M N

theorem StepStar.trans : ∀ {M N P : Term},
    StepStar M N → StepStar N P → StepStar M P
  | _, _, _, .refl _, h => h
  | _, _, _, .step _ _ _ s rest, h => .step _ _ _ s (rest.trans h)

theorem StepStar.single {M N : Term} (h : Step M N) : StepStar M N :=
  .step _ _ _ h (.refl _)

/-! ### Length-indexed reduction sequences

  `StepStarLen n M N` says `M` reduces to `N` in exactly `n` `Step`s.
  Foundation for any step-indexed argument: bounds the length of M's
  reduction so a recursion can decrease an index. -/

inductive StepStarLen : Nat → Term → Term → Prop where
  | refl (M : Term) : StepStarLen 0 M M
  | step (M M' N : Term) (n : Nat) : Step M M' → StepStarLen n M' N →
      StepStarLen (n + 1) M N

theorem StepStarLen.toStar : ∀ {n : Nat} {M N : Term},
    StepStarLen n M N → StepStar M N
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step _ _ _ _ s rest => .step _ _ _ s rest.toStar

theorem StepStar.toLen : ∀ {M N : Term}, StepStar M N → ∃ n, StepStarLen n M N
  | _, _, .refl _ => ⟨0, .refl _⟩
  | _, _, .step _ _ _ s rest =>
      let ⟨n, h⟩ := rest.toLen
      ⟨n + 1, .step _ _ _ _ s h⟩

theorem StepStarLen.trans : ∀ {n m : Nat} {M N P : Term},
    StepStarLen n M N → StepStarLen m N P → StepStarLen (n + m) M P
  | 0, m, _, _, _, .refl _, h => by
      show StepStarLen (0 + m) _ _
      rw [Nat.zero_add]; exact h
  | _, m, _, _, _, .step _ _ _ n s rest, h => by
      have ih := rest.trans h
      show StepStarLen (n + 1 + m) _ _
      rw [Nat.add_right_comm]
      exact .step _ _ _ _ s ih

theorem StepStarLen.single {M N : Term} (h : Step M N) : StepStarLen 1 M N :=
  .step _ _ _ 0 h (.refl _)

/-- A term *converges* if it reduces to a value. -/
def Converges (M : Term) : Prop := ∃ V, IsValue V ∧ StepStar M V

theorem Converges.refl {V : Term} (h : IsValue V) : Converges V :=
  ⟨V, h, .refl _⟩

theorem Converges.of_step {M N : Term} (h : Step M N) (hN : Converges N) :
    Converges M := by
  obtain ⟨V, hV, hstar⟩ := hN
  exact ⟨V, hV, .step _ _ _ h hstar⟩

/-- Wand Lemma 1.1: every code `⌜M⌝` is a value (a λ-abstraction). -/
theorem isValue_encode (M : Term) : IsValue M.encode := by
  cases M <;> · unfold Term.encode Term.wrapAbcde; exact IsValue.lam _ _

/-- Substituting any term into a value preserves value-hood: the outer
    constructor (.lam or .fexpr) is unchanged by substitution. -/
theorem substClosed_isValue {V : Term} {x : Name} {W : Term}
    (hVal : IsValue V) : IsValue (V.substClosed x W) := by
  induction hVal with
  | lam y body =>
      show IsValue ((Term.lam y body).substClosed x W)
      by_cases h : y = x
      · rw [h, Term.substClosed_lam_self]; exact .lam _ _
      · rw [Term.substClosed_lam_other h]; exact .lam _ _
  | fexpr V' _ ih =>
      show IsValue ((Term.fexpr V').substClosed x W)
      rw [Term.substClosed_fexpr]
      exact .fexpr _ ih

/-- Closure preservation for one reduction step. -/
theorem step_preserves_closed {M N : Term} :
    Step M N → M.closed → N.closed := by
  intro h hcl
  induction h with
  | beta x M V _ hVcl =>
      rw [Term.closed_app_iff] at hcl
      apply Term.closed_substClosed
      · exact (Term.closed_lam_iff.mp hcl.1)
      · exact hVcl
  | reify V M _ =>
      rw [Term.closed_app_iff, Term.closed_fexpr_iff] at hcl
      rw [Term.closed_app_iff]
      exact ⟨hcl.1, Term.closed_encode hcl.2⟩
  | reflect _ hMcl => exact hMcl
  | appL M M' N _ ih =>
      rw [Term.closed_app_iff] at hcl
      rw [Term.closed_app_iff]
      exact ⟨ih hcl.1, hcl.2⟩
  | appR _ _ _ _ _ ih =>
      rw [Term.closed_app_iff] at hcl
      rw [Term.closed_app_iff]
      exact ⟨hcl.1, ih hcl.2⟩
  | fexprIn M M' _ ih =>
      rw [Term.closed_fexpr_iff] at hcl
      rw [Term.closed_fexpr_iff]
      exact ih hcl
  | evalIn M M' _ ih =>
      rw [Term.closed_eval_iff] at hcl
      rw [Term.closed_eval_iff]
      exact ih hcl

/-- Closure preservation propagates over the reflexive-transitive closure. -/
theorem stepStar_preserves_closed {M N : Term} :
    StepStar M N → M.closed → N.closed := by
  intro h hcl
  induction h with
  | refl _ => exact hcl
  | step M M' N hStep _ ih => exact ih (step_preserves_closed hStep hcl)

/-! ### Step inversion lemmas

  Foundation for any "what could have stepped here" reasoning. Variables
  and λ-abstractions never step; values never step (by induction on
  `IsValue`). For composite shapes, inversion gives the disjunction of
  applicable rules.
-/

theorem step_var_absurd {x : Name} {P : Term} (h : Step (.var x) P) : False := by
  cases h

theorem step_lam_absurd {x : Name} {M P : Term} (h : Step (.lam x M) P) : False := by
  cases h

/-- Values never step. -/
theorem step_value_absurd {V P : Term} (hV : IsValue V) (h : Step V P) : False := by
  induction hV generalizing P with
  | lam _ _ => exact step_lam_absurd h
  | fexpr _ _ ih =>
      cases h with
      | fexprIn _ _ hStep => exact ih hStep

/-- StepStar of a value is reflexive: `V →* P` and `IsValue V` forces `V = P`. -/
theorem stepStar_value_eq {V P : Term} (hV : IsValue V) (h : StepStar V P) : V = P := by
  cases h with
  | refl _ => rfl
  | step _ M' _ hStep _ => exact absurd hStep (fun hs => step_value_absurd hV hs)

/-- StepStar lifts through `.fexpr` (congruence). -/
theorem stepStar_fexprIn : ∀ {M N : Term},
    StepStar M N → StepStar (.fexpr M) (.fexpr N)
  | _, _, .refl _ => .refl _
  | _, _, .step _ Mid _ hStep hRest =>
      .step _ _ _ (.fexprIn _ _ hStep) (stepStar_fexprIn hRest)

/-- StepStar lifts through `.eval` (congruence). -/
theorem stepStar_evalIn : ∀ {M N : Term},
    StepStar M N → StepStar (.eval M) (.eval N)
  | _, _, .refl _ => .refl _
  | _, _, .step _ Mid _ hStep hRest =>
      .step _ _ _ (.evalIn _ _ hStep) (stepStar_evalIn hRest)

/-- StepStar lifts through `.app`'s left position. -/
theorem stepStar_appL (N : Term) : ∀ {M M' : Term},
    StepStar M M' → StepStar (.app M N) (.app M' N)
  | _, _, .refl _ => .refl _
  | _, _, .step _ Mid _ hStep hRest =>
      .step _ _ _ (.appL _ _ _ hStep) (stepStar_appL N hRest)

/-- StepStar lifts through `.app`'s right position when the operator is `.lam`. -/
theorem stepStar_appR (x : Name) (body : Term) : ∀ {N N' : Term},
    StepStar N N' → StepStar (.app (.lam x body) N) (.app (.lam x body) N')
  | _, _, .refl _ => .refl _
  | _, _, .step _ Mid _ hStep hRest =>
      .step _ _ _ (.appR _ _ _ _ hStep) (stepStar_appR x body hRest)


/-- Inversion for `Step (.fexpr M) P` — only `fexprIn` can produce this. -/
theorem step_fexpr_inv {M P : Term} (h : Step (.fexpr M) P) :
    ∃ M', P = .fexpr M' ∧ Step M M' := by
  cases h with
  | fexprIn _ M' hStep => exact ⟨M', rfl, hStep⟩

/-- Inversion for `Step (.eval M) P` — either `reflect` (M is a code) or `evalIn`. -/
theorem step_eval_inv {M P : Term} (h : Step (.eval M) P) :
    (∃ N, M = N.encode ∧ N.closed ∧ P = N) ∨
    (∃ M', P = .eval M' ∧ Step M M') := by
  cases h with
  | reflect _ hMcl => exact Or.inl ⟨P, rfl, hMcl, rfl⟩
  | evalIn _ M' hStep => exact Or.inr ⟨M', rfl, hStep⟩

/-- Inversion for `Step (.app A B) P` — one of β-value, reify, appL, appR. -/
theorem step_app_inv {A B P : Term} (h : Step (.app A B) P) :
    (∃ x Mb, A = .lam x Mb ∧ IsValue B ∧ B.closed ∧ P = Mb.substClosed x B) ∨
    (∃ V, A = .fexpr V ∧ IsValue V ∧ P = .app V B.encode) ∨
    (∃ A', Step A A' ∧ P = .app A' B) ∨
    (∃ B', IsValue A ∧ Step B B' ∧ P = .app A B') := by
  cases h with
  | beta x Mb _ hV hVcl   => exact Or.inl ⟨x, Mb, rfl, hV, hVcl, rfl⟩
  | reify V _ hV          => exact Or.inr (Or.inl ⟨V, rfl, hV, rfl⟩)
  | appL _ A' _ hStep     => exact Or.inr (Or.inr (Or.inl ⟨A', hStep, rfl⟩))
  | appR _ _ _ N' hStep   => exact Or.inr (Or.inr (Or.inr ⟨N', .lam _ _, hStep, rfl⟩))

/-- Inversion: a `.fexpr` reduction to a value pins down the value's shape.
    Proven via length-indexed StepStarLen to give Lean a clear measure. -/
theorem stepStar_fexpr_value_inv_len : ∀ {n : Nat} {M W : Term},
    StepStarLen n (.fexpr M) W → IsValue W →
      ∃ V, IsValue V ∧ W = .fexpr V ∧ StepStar M V
  | 0, M, _, .refl _, hW => by
      cases hW with | fexpr V hV => exact ⟨M, hV, rfl, .refl _⟩
  | n+1, M, W, .step _ Mid _ _ hStep hRest, hW => by
      obtain ⟨M', hMid_eq, hStep_M⟩ := step_fexpr_inv hStep
      subst hMid_eq
      obtain ⟨V, hVval, hWeq, hStarMV⟩ := stepStar_fexpr_value_inv_len hRest hW
      exact ⟨V, hVval, hWeq, .step _ _ _ hStep_M hStarMV⟩

theorem stepStar_fexpr_value_inv {M W : Term}
    (h : StepStar (.fexpr M) W) (hW : IsValue W) :
    ∃ V, IsValue V ∧ W = .fexpr V ∧ StepStar M V :=
  let ⟨_, hLen⟩ := h.toLen
  stepStar_fexpr_value_inv_len hLen hW

/-- Inversion: a `.eval M` reduction to a value forces a reflect-step
    structure: M reduces to some `K.encode` (closed K), then reflect
    fires, then K reduces to the final value. -/
theorem stepStar_eval_value_inv_len : ∀ {n : Nat} {M W : Term},
    StepStarLen n (.eval M) W → IsValue W →
      ∃ K, K.closed ∧ StepStar M K.encode ∧ StepStar K W
  | 0, M, _, .refl _, hW => by cases hW
  | n+1, M, W, .step _ Mid _ _ hStep hRest, hW => by
      rcases step_eval_inv hStep with ⟨K, hMeq, hKcl, hMid_eq⟩ | ⟨M', hMid_eq, hStep_M⟩
      · -- reflect: M = K.encode, Mid = K.
        refine ⟨K, hKcl, ?_, ?_⟩
        · rw [hMeq]; exact .refl _
        · rw [hMid_eq] at hRest
          exact hRest.toStar
      · -- evalIn: Mid = .eval M', Step M M'.
        subst hMid_eq
        obtain ⟨K, hKcl, hStarMK, hStarKW⟩ := stepStar_eval_value_inv_len hRest hW
        exact ⟨K, hKcl, .step _ _ _ hStep_M hStarMK, hStarKW⟩

theorem stepStar_eval_value_inv {M W : Term}
    (h : StepStar (.eval M) W) (hW : IsValue W) :
    ∃ K, K.closed ∧ StepStar M K.encode ∧ StepStar K W :=
  let ⟨_, hLen⟩ := h.toLen
  stepStar_eval_value_inv_len hLen hW

end FexprTrivial
