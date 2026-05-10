/-
  Substitution.

  For session 1 we provide only `substClosed` — naive substitution
  `M[V/x]` that is sound when `V` is closed (no free variables of `V`
  can be captured by binders in `M`). This suffices for CBV reduction
  starting from a closed program.

  Capture-avoiding substitution and `freshFor` are deferred until a
  downstream proof actually demands them.
-/
import FexprTrivial.Term
namespace FexprTrivial

namespace Term

/--
  Naive substitution. **Caller must ensure `V` is closed**, otherwise
  free variables of `V` may be captured by binders in `M`.
-/
def substClosed : Term → Name → Term → Term
  | .var z,   x, V => if z = x then V else .var z
  | .lam z M, x, V =>
      if z = x then .lam z M
      else .lam z (M.substClosed x V)
  | .app M N, x, V => .app (M.substClosed x V) (N.substClosed x V)
  | .fexpr M, x, V => .fexpr (M.substClosed x V)
  | .eval M,  x, V => .eval (M.substClosed x V)

/-! ### Equation lemmas for `substClosed` — pre-computed if-cases -/

@[simp] theorem substClosed_var_self (x : Name) (V : Term) :
    (Term.var x).substClosed x V = V := by
  unfold substClosed; rw [if_pos rfl]

@[simp] theorem substClosed_var_other {z x : Name} (h : z ≠ x) (V : Term) :
    (Term.var z).substClosed x V = .var z := by
  unfold substClosed; rw [if_neg h]

@[simp] theorem substClosed_lam_self (x : Name) (M V : Term) :
    (Term.lam x M).substClosed x V = .lam x M := by
  unfold substClosed; rw [if_pos rfl]

@[simp] theorem substClosed_lam_other {z x : Name} (h : z ≠ x) (M V : Term) :
    (Term.lam z M).substClosed x V = .lam z (M.substClosed x V) := by
  show (if z = x then _ else _) = _
  rw [if_neg h]

@[simp] theorem substClosed_app (M N : Term) (x : Name) (V : Term) :
    (Term.app M N).substClosed x V = .app (M.substClosed x V) (N.substClosed x V) := rfl

@[simp] theorem substClosed_fexpr (M : Term) (x : Name) (V : Term) :
    (Term.fexpr M).substClosed x V = .fexpr (M.substClosed x V) := rfl

@[simp] theorem substClosed_eval (M : Term) (x : Name) (V : Term) :
    (Term.eval M).substClosed x V = .eval (M.substClosed x V) := rfl

/-- Substituting a variable `x` not free in `M` is the identity. -/
theorem substClosed_not_free (M : Term) (x : Name) (V : Term)
    (h : x ∉ M.fv) : M.substClosed x V = M := by
  induction M with
  | var z =>
      simp at h
      simp only [substClosed]
      split
      · rename_i hzx; exact absurd hzx.symm h
      · rfl
  | lam z M ih =>
      simp only [substClosed]
      split
      · rfl
      · rename_i hzx
        congr 1
        apply ih
        intro hxM
        apply h
        rw [mem_fv_lam_iff]
        exact ⟨hxM, fun hxz => hzx hxz.symm⟩
  | app M N ihM ihN =>
      simp at h
      simp only [substClosed, ihM h.1, ihN h.2]
  | fexpr M ih =>
      simp at h
      simp only [substClosed, ih h]
  | eval M ih =>
      simp at h
      simp only [substClosed, ih h]

/-- Closed terms are unchanged by any substitution. -/
theorem substClosed_of_closed (M : Term) (h : M.closed) (x : Name) (V : Term) :
    M.substClosed x V = M := by
  apply substClosed_not_free
  rw [closed] at h
  rw [h]
  intro hx; cases hx

/--
  Free-variable accounting for `substClosed`. Anything free in the
  result either came from `M` (and isn't `x`) or came from `V`.
-/
theorem mem_fv_substClosed {M : Term} {x : Name} {V : Term} {y : Name} :
    y ∈ (M.substClosed x V).fv →
      (y ∈ M.fv ∧ y ≠ x) ∨ y ∈ V.fv := by
  induction M with
  | var z =>
      simp only [substClosed]
      by_cases hzx : z = x
      · rw [if_pos hzx]
        intro hy; exact Or.inr hy
      · rw [if_neg hzx]
        intro hy
        simp only [fv_var, List.mem_singleton] at hy
        subst hy
        exact Or.inl ⟨by simp [fv_var], hzx⟩
  | lam z M ih =>
      simp only [substClosed]
      by_cases hzx : z = x
      · rw [if_pos hzx]
        subst hzx
        intro hy
        rw [mem_fv_lam_iff] at hy
        obtain ⟨hyM, hyx⟩ := hy
        refine Or.inl ⟨?_, hyx⟩
        rw [mem_fv_lam_iff]; exact ⟨hyM, hyx⟩
      · rw [if_neg hzx]
        intro hy
        rw [mem_fv_lam_iff] at hy
        obtain ⟨hyM_subst, hyz⟩ := hy
        rcases ih hyM_subst with ⟨hyM, hyx⟩ | hyV
        · refine Or.inl ⟨?_, hyx⟩
          rw [mem_fv_lam_iff]; exact ⟨hyM, hyz⟩
        · exact Or.inr hyV
  | app M N ihM ihN =>
      simp only [substClosed, fv_app, List.mem_append]
      intro hy
      rcases hy with hyM | hyN
      · rcases ihM hyM with ⟨hyM', hyx⟩ | hyV
        · exact Or.inl ⟨Or.inl hyM', hyx⟩
        · exact Or.inr hyV
      · rcases ihN hyN with ⟨hyN', hyx⟩ | hyV
        · exact Or.inl ⟨Or.inr hyN', hyx⟩
        · exact Or.inr hyV
  | fexpr M ih =>
      simp only [substClosed, fv_fexpr]
      intro hy; exact ih hy
  | eval M ih =>
      simp only [substClosed, fv_eval]
      intro hy; exact ih hy

/--
  Closure preservation for substitution: if every free variable of `M`
  is `x`, and `V` is closed, then `M[V/x]` is closed.
-/
theorem closed_substClosed {M : Term} {x : Name} {V : Term}
    (hM : ∀ y ∈ M.fv, y = x) (hV : V.closed) :
    (M.substClosed x V).closed := by
  unfold closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y hy
  rcases mem_fv_substClosed hy with ⟨hyM, hyx⟩ | hyV
  · exact hyx (hM y hyM)
  · unfold closed at hV
    rw [hV] at hyV
    cases hyV

/--
  Reverse direction of `mem_fv_substClosed` when `V` is closed:
  every non-`x` free variable of `M` survives the substitution.
-/
theorem mem_fv_substClosed_rev {M : Term} {x : Name} {V : Term} {y : Name}
    (_hVcl : V.closed) (hyM : y ∈ M.fv) (hyx : y ≠ x) :
    y ∈ (M.substClosed x V).fv := by
  induction M with
  | var z =>
      simp [fv_var] at hyM
      subst hyM
      simp only [substClosed]
      rw [if_neg hyx]
      simp [fv_var]
  | lam z M ih =>
      rw [mem_fv_lam_iff] at hyM
      obtain ⟨hyM', hyz⟩ := hyM
      simp only [substClosed]
      by_cases hzx : z = x
      · rw [if_pos hzx]
        rw [mem_fv_lam_iff]; exact ⟨hyM', hyz⟩
      · rw [if_neg hzx]
        rw [mem_fv_lam_iff]
        exact ⟨ih hyM', hyz⟩
  | app M N ihM ihN =>
      simp only [substClosed, fv_app, List.mem_append] at hyM ⊢
      rcases hyM with hyM' | hyN'
      · exact Or.inl (ihM hyM')
      · exact Or.inr (ihN hyN')
  | fexpr M ih =>
      simp only [substClosed, fv_fexpr] at hyM ⊢
      exact ih hyM
  | eval M ih =>
      simp only [substClosed, fv_eval] at hyM ⊢
      exact ih hyM

/-- Two substitutions of closed terms commute when they target different
    variables. The standard substitution composition lemma, specialised
    to closed substitutees so the freshness side-conditions are vacuous. -/
theorem substClosed_commute {b V W : Term} {x y : Name}
    (hxy : x ≠ y) (hVcl : V.closed) (hWcl : W.closed) :
    (b.substClosed x V).substClosed y W = (b.substClosed y W).substClosed x V := by
  induction b with
  | var z =>
    by_cases hzx : z = x
    · rw [hzx]
      have hxy' : ¬ x = y := hxy
      rw [substClosed_var_self x V, substClosed_var_other hxy' W,
          substClosed_var_self x V]
      exact substClosed_of_closed V hVcl y W
    · by_cases hzy : z = y
      · rw [hzy]
        have hyx : ¬ y = x := fun h => hxy h.symm
        rw [substClosed_var_other hyx V, substClosed_var_self y W]
        exact (substClosed_of_closed W hWcl x V).symm
      · rw [substClosed_var_other hzx V, substClosed_var_other hzy W,
            substClosed_var_other hzx V]
  | lam z body ih =>
    by_cases hzx : z = x
    · rw [hzx]
      have hxy' : ¬ x = y := hxy
      rw [substClosed_lam_self x body V, substClosed_lam_other hxy' body W,
          substClosed_lam_self x (body.substClosed y W) V]
    · by_cases hzy : z = y
      · rw [hzy]
        have hyx : ¬ y = x := fun h => hxy h.symm
        rw [substClosed_lam_other hyx body V, substClosed_lam_self y body W,
            substClosed_lam_self y (body.substClosed x V) W,
            substClosed_lam_other hyx body V]
      · rw [substClosed_lam_other hzx body V, substClosed_lam_other hzy body W,
            substClosed_lam_other hzy (body.substClosed x V) W,
            substClosed_lam_other hzx (body.substClosed y W) V, ih]
  | app M N ihM ihN =>
    rw [substClosed_app, substClosed_app, substClosed_app, substClosed_app, ihM, ihN]
  | fexpr M ih =>
    rw [substClosed_fexpr, substClosed_fexpr, substClosed_fexpr, substClosed_fexpr, ih]
  | eval M ih =>
    rw [substClosed_eval, substClosed_eval, substClosed_eval, substClosed_eval, ih]

end Term
end FexprTrivial
