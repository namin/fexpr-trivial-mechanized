/-
  Wand's calculus terms: M, N ::= x | λx.M | M N | (fexpr M) | (eval M)

  Named variables (de Bruijn would erase the very thing we are studying:
  α-distinct terms must be syntactically distinct in the representation,
  because Wand's distinguishing context observes the syntactic structure
  of its operand).
-/
namespace FexprTrivial

abbrev Name := String

inductive Term where
  | var   : Name → Term
  | lam   : Name → Term → Term
  | app   : Term → Term → Term
  | fexpr : Term → Term
  | eval  : Term → Term
  deriving Repr, DecidableEq, Inhabited

namespace Term

/-- Free variables, as a list (may have duplicates; treat as multiset of memberships). -/
def fv : Term → List Name
  | .var x   => [x]
  | .lam x M => M.fv.filter (· ≠ x)
  | .app M N => M.fv ++ N.fv
  | .fexpr M => M.fv
  | .eval M  => M.fv

/-- A term is closed when it has no free variables. -/
def closed (M : Term) : Prop := M.fv = []

/-- Structural size, used as a well-founded measure for substitution. -/
def size : Term → Nat
  | .var _   => 1
  | .lam _ M => 1 + M.size
  | .app M N => 1 + M.size + N.size
  | .fexpr M => 1 + M.size
  | .eval M  => 1 + M.size

theorem size_pos (M : Term) : 0 < M.size := by
  cases M <;> simp [size] <;> omega

/--
  Naive (non-capture-avoiding) renaming: replace free `x` by free `y`.
  Safe only when `y` does not occur bound anywhere in the term — we use
  it via fresh `y` in the substitution definition.
-/
def rename : Term → Name → Name → Term
  | .var z,   x, y => if z = x then .var y else .var z
  | .lam z M, x, y =>
      if z = x then .lam z M
      else .lam z (M.rename x y)
  | .app M N, x, y => .app (M.rename x y) (N.rename x y)
  | .fexpr M, x, y => .fexpr (M.rename x y)
  | .eval M,  x, y => .eval (M.rename x y)

theorem rename_size (M : Term) (x y : Name) : (M.rename x y).size = M.size := by
  induction M with
  | var z =>
      simp [rename, size]
      split <;> simp [size]
  | lam z M ih =>
      simp [rename]
      split <;> simp [size, ih]
  | app M N ihM ihN => simp [rename, size, ihM, ihN]
  | fexpr M ih      => simp [rename, size, ih]
  | eval M ih       => simp [rename, size, ih]

@[simp] theorem fv_var (x : Name) : (Term.var x).fv = [x] := rfl
@[simp] theorem fv_lam (x : Name) (M : Term) : (Term.lam x M).fv = M.fv.filter (· ≠ x) := rfl
@[simp] theorem fv_app (M N : Term) : (Term.app M N).fv = M.fv ++ N.fv := rfl
@[simp] theorem fv_fexpr (M : Term) : (Term.fexpr M).fv = M.fv := rfl
@[simp] theorem fv_eval (M : Term) : (Term.eval M).fv = M.fv := rfl

theorem mem_fv_lam_iff {x z : Name} {M : Term} :
    x ∈ (Term.lam z M).fv ↔ x ∈ M.fv ∧ x ≠ z := by
  simp [List.mem_filter]

theorem closed_app_iff {M N : Term} :
    (Term.app M N).closed ↔ M.closed ∧ N.closed := by
  unfold closed
  simp [fv_app]

theorem closed_fexpr_iff {M : Term} :
    (Term.fexpr M).closed ↔ M.closed := by
  unfold closed; simp [fv_fexpr]

theorem closed_eval_iff {M : Term} :
    (Term.eval M).closed ↔ M.closed := by
  unfold closed; simp [fv_eval]

/-- A `λx.M` is closed iff every free variable of `M` is `x`. -/
theorem closed_lam_iff {x : Name} {M : Term} :
    (Term.lam x M).closed ↔ ∀ y ∈ M.fv, y = x := by
  unfold closed
  simp [fv_lam, List.filter_eq_nil_iff]

/-- If `x` is not free in `M`, renaming is the identity. -/
theorem rename_fresh (M : Term) (x y : Name) (h : x ∉ M.fv) :
    M.rename x y = M := by
  induction M with
  | var z =>
      simp at h
      simp only [rename]
      split
      · rename_i hzx; exact absurd hzx.symm h
      · rfl
  | lam z M ih =>
      simp only [rename]
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
      simp only [rename, ihM h.1, ihN h.2]
  | fexpr M ih =>
      simp at h
      simp only [rename, ih h]
  | eval M ih =>
      simp at h
      simp only [rename, ih h]

end Term
end FexprTrivial
