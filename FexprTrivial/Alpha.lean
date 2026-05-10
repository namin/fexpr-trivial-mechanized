/-
  α-equivalence on named terms via an environment of bound-variable
  pairs. Avoids defining α via substitution and is symmetric in M, N.

  `AlphaEqIn env M N`: under binder pairs `env`, M and N are α-equivalent.
-/
import FexprTrivial.Term
namespace FexprTrivial

/--
  Two free names are "consistent" with respect to an environment of
  binder pairs: walking outward, the topmost binder mentioning either
  name pairs them together.
-/
def consistent : List (Name × Name) → Name → Name → Prop
  | [],            x, y => x = y
  | (a, b) :: env, x, y =>
      if x = a then y = b
      else if y = b then False
      else consistent env x y

theorem consistent_diag (env : List (Name × Name))
    (hd : ∀ p ∈ env, p.1 = p.2) (x : Name) : consistent env x x := by
  induction env with
  | nil => rfl
  | cons p env ih =>
      have hab : p.1 = p.2 := hd p (List.mem_cons_self ..)
      obtain ⟨a, b⟩ := p
      simp at hab
      subst hab
      simp only [consistent]
      by_cases hxa : x = a
      · rw [if_pos hxa]; exact hxa
      · rw [if_neg hxa, if_neg hxa]
        apply ih
        intro q hq
        exact hd q (List.mem_cons_of_mem _ hq)

theorem consistent_swap (env : List (Name × Name)) (x y : Name) :
    consistent env x y → consistent (env.map (fun p => (p.2, p.1))) y x := by
  intro h
  induction env with
  | nil => exact h.symm
  | cons p env ih =>
      obtain ⟨a, b⟩ := p
      simp only [consistent] at h
      simp only [List.map, consistent]
      by_cases hxa : x = a
      · rw [if_pos hxa] at h
        subst hxa
        subst h
        rw [if_pos rfl]
      · rw [if_neg hxa] at h
        by_cases hyb : y = b
        · rw [if_pos hyb] at h
          exact h.elim
        · rw [if_neg hyb] at h
          rw [if_neg hyb, if_neg hxa]
          exact ih h

inductive AlphaEqIn : List (Name × Name) → Term → Term → Prop where
  | var (env : List (Name × Name)) (x y : Name) :
      consistent env x y → AlphaEqIn env (.var x) (.var y)
  | lam (env : List (Name × Name)) (x y : Name) (M N : Term) :
      AlphaEqIn ((x, y) :: env) M N →
      AlphaEqIn env (.lam x M) (.lam y N)
  | app (env : List (Name × Name)) (M₁ M₂ N₁ N₂ : Term) :
      AlphaEqIn env M₁ M₂ → AlphaEqIn env N₁ N₂ →
      AlphaEqIn env (.app M₁ N₁) (.app M₂ N₂)
  | fexpr (env : List (Name × Name)) (M N : Term) :
      AlphaEqIn env M N → AlphaEqIn env (.fexpr M) (.fexpr N)
  | eval (env : List (Name × Name)) (M N : Term) :
      AlphaEqIn env M N → AlphaEqIn env (.eval M) (.eval N)

/-- Top-level α-equivalence (empty environment). -/
def AlphaEq (M N : Term) : Prop := AlphaEqIn [] M N

theorem alpha_refl_in (env : List (Name × Name))
    (hd : ∀ p ∈ env, p.1 = p.2) (M : Term) : AlphaEqIn env M M := by
  induction M generalizing env with
  | var x => exact .var env x x (consistent_diag env hd x)
  | lam x M ih =>
      apply AlphaEqIn.lam
      apply ih
      intro p hp
      cases hp with
      | head => rfl
      | tail _ hp' => exact hd p hp'
  | app M N ihM ihN => exact .app env _ _ _ _ (ihM env hd) (ihN env hd)
  | fexpr M ih => exact .fexpr env _ _ (ih env hd)
  | eval M ih  => exact .eval env _ _ (ih env hd)

theorem alpha_refl (M : Term) : AlphaEq M M := by
  apply alpha_refl_in
  intros p hp
  cases hp

theorem alpha_sym_in (env : List (Name × Name)) (M N : Term) :
    AlphaEqIn env M N →
    AlphaEqIn (env.map (fun p => (p.2, p.1))) N M := by
  intro h
  induction h with
  | var env x y hc => exact .var _ _ _ (consistent_swap env x y hc)
  | lam env x y M N _ ih =>
      apply AlphaEqIn.lam
      have heq : (((x, y) :: env).map (fun p => (p.2, p.1)))
               = (y, x) :: env.map (fun p => (p.2, p.1)) := by simp [List.map]
      rw [heq] at ih
      exact ih
  | app env M₁ M₂ N₁ N₂ _ _ ihM ihN => exact .app _ _ _ _ _ ihM ihN
  | fexpr env M N _ ih => exact .fexpr _ _ _ ih
  | eval env M N _ ih  => exact .eval _ _ _ ih

theorem alpha_sym (M N : Term) : AlphaEq M N → AlphaEq N M := by
  intro h
  have := alpha_sym_in [] M N h
  simpa [List.map] using this

/-- Positional composition: pair the first projection of `env₁` with the
    second projection of `env₂` at each position. -/
def envCompose : List (Name × Name) → List (Name × Name) → List (Name × Name)
  | [], _ => []
  | _ :: _, [] => []
  | (a, _) :: env₁, (_, c) :: env₂ => (a, c) :: envCompose env₁ env₂

/-- Two envs are *compatible* when they have the same length and the
    second component of each pair in `env₁` equals the first component
    of the corresponding pair in `env₂` — exactly the situation that
    arises when two α-equivalences are composed at a common middle term. -/
inductive envsCompatible : List (Name × Name) → List (Name × Name) → Prop where
  | nil : envsCompatible [] []
  | cons (a b c : Name) (env₁ env₂ : List (Name × Name)) :
      envsCompatible env₁ env₂ →
      envsCompatible ((a, b) :: env₁) ((b, c) :: env₂)

theorem consistent_trans :
    ∀ {env₁ env₂ : List (Name × Name)} {x y z : Name},
      envsCompatible env₁ env₂ →
      consistent env₁ x y → consistent env₂ y z →
      consistent (envCompose env₁ env₂) x z := by
  intro env₁ env₂ x y z hcompat h₁ h₂
  induction hcompat generalizing x y z with
  | nil =>
      simp only [consistent] at h₁ h₂
      subst h₁
      simp only [envCompose, consistent]
      exact h₂
  | cons a b c env₁ env₂ _ ih =>
      simp only [consistent] at h₁ h₂
      simp only [envCompose, consistent]
      by_cases hxa : x = a
      · rw [if_pos hxa] at h₁
        subst hxa
        subst h₁
        rw [if_pos rfl] at h₂
        subst h₂
        rw [if_pos rfl]
      · rw [if_neg hxa] at h₁
        by_cases hyb : y = b
        · rw [if_pos hyb] at h₁
          exact h₁.elim
        · rw [if_neg hyb] at h₁
          rw [if_neg hyb] at h₂
          by_cases hzc : z = c
          · rw [if_pos hzc] at h₂
            exact h₂.elim
          · rw [if_neg hzc] at h₂
            rw [if_neg hxa, if_neg hzc]
            exact ih h₁ h₂

theorem alpha_trans_in :
    ∀ {env₁ env₂ : List (Name × Name)} {M N P : Term},
      envsCompatible env₁ env₂ →
      AlphaEqIn env₁ M N → AlphaEqIn env₂ N P →
      AlphaEqIn (envCompose env₁ env₂) M P := by
  intro env₁ env₂ M N P hcompat h₁ h₂
  induction h₁ generalizing env₂ P with
  | var _ x y hc =>
      cases h₂ with
      | var _ _ z hc' => exact .var _ _ _ (consistent_trans hcompat hc hc')
  | lam env xL xR Mb Nb _ ih =>
      cases h₂ with
      | lam _ _ xP _ Pb hPin =>
          apply AlphaEqIn.lam
          have hcompat' :
              envsCompatible ((xL, xR) :: env) ((xR, xP) :: env₂) :=
            envsCompatible.cons xL xR xP env env₂ hcompat
          exact ih hcompat' hPin
  | app env M₁ M₂ N₁ N₂ _ _ ihM ihN =>
      cases h₂ with
      | app _ _ Mp _ Np hM hN =>
          exact .app _ _ _ _ _ (ihM hcompat hM) (ihN hcompat hN)
  | fexpr env M N _ ih =>
      cases h₂ with
      | fexpr _ _ Np h => exact .fexpr _ _ _ (ih hcompat h)
  | eval env M N _ ih =>
      cases h₂ with
      | eval _ _ Np h => exact .eval _ _ _ (ih hcompat h)

theorem alpha_trans (M N P : Term) :
    AlphaEq M N → AlphaEq N P → AlphaEq M P := by
  intro h₁ h₂
  have := alpha_trans_in envsCompatible.nil h₁ h₂
  simpa [envCompose] using this

end FexprTrivial
