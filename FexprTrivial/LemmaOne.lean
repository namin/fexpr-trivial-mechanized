/-
  Encoding injectivity (Wand 1998, Lemma 1.3).

  The Mogensen–Scott encoding is structurally injective:
  `⌜M⌝ = ⌜N⌝ → M = N`. The reflect-rule case of `step_deterministic`
  uses this to align the two reducts when both fire `Step.reflect`.

  Sorry-free.
-/
import FexprTrivial.Term
import FexprTrivial.Coding
namespace FexprTrivial

namespace Term

/-- Structural injectivity for `wrapAbcde`. -/
theorem wrapAbcde_injective {b₁ b₂ : Term} (h : wrapAbcde b₁ = wrapAbcde b₂) :
    b₁ = b₂ := by
  unfold wrapAbcde at h
  simp only [Term.lam.injEq, true_and] at h
  exact h

/-- **Wand Lemma 1.3.** `⌜M⌝ = ⌜N⌝ → M = N`. The proof is a 5×5 case
    analysis: distinct head constructors of `Term` produce different
    encoding markers (codeA, …, codeE), and equal markers force equal
    sub-encodings, which yield equal sub-terms by induction. -/
theorem encode_injective : ∀ {M N : Term}, M.encode = N.encode → M = N := by
  intro M
  induction M with
  | var x =>
      intro N hEnc
      cases N with
      | var y =>
          simp only [encode, Term.app.injEq, Term.var.injEq, true_and] at hEnc
          have := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq, true_and] at this
          rw [this]
      | lam y N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | app N₁ N₂ =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
      | fexpr N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | eval N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
  | lam x M' ih =>
      intro N hEnc
      cases N with
      | var y =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | lam y N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.lam.injEq, true_and] at hbody
          obtain ⟨hxy, hMN⟩ := hbody
          rw [hxy, ih hMN]
      | app N₁ N₂ =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
      | fexpr N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | eval N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
  | app M₁ M₂ ihM ihN =>
      intro N hEnc
      cases N with
      | var y =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
      | lam y N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
      | app N₁ N₂ =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq, true_and] at hbody
          obtain ⟨hM₁, hM₂⟩ := hbody
          rw [ihM hM₁, ihN hM₂]
      | fexpr N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
      | eval N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
  | fexpr M' ih =>
      intro N hEnc
      cases N with
      | var y =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | lam y N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | app N₁ N₂ =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
      | fexpr N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq, true_and] at hbody
          rw [ih hbody]
      | eval N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
  | eval M' ih =>
      intro N hEnc
      cases N with
      | var y =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | lam y N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | app N₁ N₂ =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq] at hbody
          obtain ⟨hL, _⟩ := hbody
          cases hL
      | fexpr N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq] at hbody
          exact absurd hbody.1 (by decide)
      | eval N' =>
          simp only [encode] at hEnc
          have hbody := wrapAbcde_injective hEnc
          simp only [Term.app.injEq, Term.var.injEq, true_and] at hbody
          rw [ih hbody]

end Term
end FexprTrivial
