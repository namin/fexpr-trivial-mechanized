/-
  The Mogensen–Scott encoding `⌜·⌝` from Wand §2:

      ⌜x⌝         ≡ λabcde. a x
      ⌜MN⌝        ≡ λabcde. b ⌜M⌝ ⌜N⌝
      ⌜λx.M⌝      ≡ λabcde. c (λx. ⌜M⌝)
      ⌜(fexpr M)⌝ ≡ λabcde. d ⌜M⌝
      ⌜(eval M)⌝  ≡ λabcde. e ⌜M⌝

  Wand notes that `a, b, c, d, e` should be fresh per case. We pick
  globally-fixed reserved names (`__a__` etc.) and rely on the convention
  that user `Name`s do not collide with the reserved set. Lemmas that
  need the freshness condition will carry it as a hypothesis.

  For session 1 we just define the encoding. The Wand Lemma 1 facts
  (closure, fv preservation, α-iff-β-of-codes) come in session 2 once
  we have the machinery to state them cleanly.
-/
import FexprTrivial.Term
namespace FexprTrivial

namespace Term

def codeA : Name := "__a__"
def codeB : Name := "__b__"
def codeC : Name := "__c__"
def codeD : Name := "__d__"
def codeE : Name := "__e__"

/-- Wrap a body in `λabcde. body`. -/
def wrapAbcde (body : Term) : Term :=
  .lam codeA (.lam codeB (.lam codeC (.lam codeD (.lam codeE body))))

/-- The Mogensen–Scott encoding `⌜M⌝`. -/
def encode : Term → Term
  | .var x   => wrapAbcde (.app (.var codeA) (.var x))
  | .app M N => wrapAbcde (.app (.app (.var codeB) M.encode) N.encode)
  | .lam x M => wrapAbcde (.app (.var codeC) (.lam x M.encode))
  | .fexpr M => wrapAbcde (.app (.var codeD) M.encode)
  | .eval M  => wrapAbcde (.app (.var codeE) M.encode)

/-- The set of reserved names used by the encoding. -/
def codeReserved : List Name := [codeA, codeB, codeC, codeD, codeE]

/-- A name is "user-safe" iff it is not one of the reserved encoder binders. -/
def safeName (x : Name) : Prop := x ∉ codeReserved

/-- The reserved names are pairwise distinct. -/
theorem codeReserved_nodup : codeReserved.Nodup := by
  unfold codeReserved codeA codeB codeC codeD codeE
  decide

/-- Free variables of `wrapAbcde body` are exactly free variables of `body`
    that are not in the reserved set. -/
theorem mem_fv_wrapAbcde {body : Term} {y : Name} :
    y ∈ (wrapAbcde body).fv ↔
      y ∈ body.fv ∧ y ≠ codeA ∧ y ≠ codeB ∧ y ≠ codeC ∧ y ≠ codeD ∧ y ≠ codeE := by
  unfold wrapAbcde
  simp only [mem_fv_lam_iff]
  constructor
  · intro ⟨⟨⟨⟨⟨h, hE⟩, hD⟩, hC⟩, hB⟩, hA⟩
    exact ⟨h, hA, hB, hC, hD, hE⟩
  · intro ⟨h, hA, hB, hC, hD, hE⟩
    exact ⟨⟨⟨⟨⟨h, hE⟩, hD⟩, hC⟩, hB⟩, hA⟩

/--
  The free-variable inclusion for `encode`: every free variable of
  `⌜M⌝` is also a free variable of `M`. The wrapping `λabcde` filters
  out exactly the reserved names introduced by the encoding, so no
  encoding-internal binders leak.
-/
theorem mem_fv_encode {M : Term} {y : Name} :
    y ∈ (M.encode).fv → y ∈ M.fv := by
  induction M with
  | var x =>
      intro hy
      simp only [encode] at hy
      rw [mem_fv_wrapAbcde] at hy
      obtain ⟨hbody, hnA, _, _, _, _⟩ := hy
      simp [fv_app, fv_var] at hbody
      rcases hbody with hyA | hyx
      · exact absurd hyA hnA
      · simp [fv_var]; exact hyx
  | lam x M' ih =>
      intro hy
      simp only [encode] at hy
      rw [mem_fv_wrapAbcde] at hy
      obtain ⟨hbody, _, _, hnC, _, _⟩ := hy
      simp [fv_app, fv_var] at hbody
      rcases hbody with hyC | ⟨hyM', hyx⟩
      · exact absurd hyC hnC
      · rw [mem_fv_lam_iff]; exact ⟨ih hyM', hyx⟩
  | app M N ihM ihN =>
      intro hy
      simp only [encode] at hy
      rw [mem_fv_wrapAbcde] at hy
      obtain ⟨hbody, _, hnB, _, _, _⟩ := hy
      simp [fv_app, fv_var] at hbody
      rcases hbody with hyB | hyM | hyN
      · exact absurd hyB hnB
      · rw [fv_app]; exact List.mem_append.mpr (Or.inl (ihM hyM))
      · rw [fv_app]; exact List.mem_append.mpr (Or.inr (ihN hyN))
  | fexpr M' ih =>
      intro hy
      simp only [encode] at hy
      rw [mem_fv_wrapAbcde] at hy
      obtain ⟨hbody, _, _, _, hnD, _⟩ := hy
      simp [fv_app, fv_var] at hbody
      rcases hbody with hyD | hyM'
      · exact absurd hyD hnD
      · rw [fv_fexpr]; exact ih hyM'
  | eval M' ih =>
      intro hy
      simp only [encode] at hy
      rw [mem_fv_wrapAbcde] at hy
      obtain ⟨hbody, _, _, _, _, hnE⟩ := hy
      simp [fv_app, fv_var] at hbody
      rcases hbody with hyE | hyM'
      · exact absurd hyE hnE
      · rw [fv_eval]; exact ih hyM'

/-- Wand Lemma 1.2 (closed half): codes of closed terms are closed. -/
theorem closed_encode {M : Term} (h : M.closed) : (M.encode).closed := by
  unfold closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y hy
  have hyM := mem_fv_encode hy
  unfold closed at h
  rw [h] at hyM
  cases hyM

end Term
end FexprTrivial
