/-
  Wand 1998 — value-level distinguishability.

  The first half of the path to Theorem 1: a single un-gated reflective
  context distinguishes any two syntactically-distinct closed terms by
  reducing them to syntactically-distinct values (their codes).

  This is the constructive core of Wand's argument: reflection lets a
  context observe its operand's syntactic structure. Combined with
  Lemma 1.3 (encode injectivity), it says "no equational theory that
  preserves reduction outcomes can equate distinct closed terms."

  Sorry-free.
-/
import FexprTrivial.Term
import FexprTrivial.Coding
import FexprTrivial.Reduction
import FexprTrivial.LemmaOne
import FexprTrivial.Discriminator
namespace FexprTrivial

/-- **Wand's collapse, value-level form.** For any closed `M, N` whose
    Mogensen–Scott encodings are syntactically distinct, the un-gated
    reflective context `C[·] := (fexpr idBody) ·` distinguishes them:
    `C[M] →* ⌜M⌝` and `C[N] →* ⌜N⌝`, with `⌜M⌝ ≠ ⌜N⌝`.

    No assumption of β-equivalence: the lemma simply says the reflective
    context discriminates by encoding. Wand's full negative result
    follows by combining this with `Term.encode_injective` (so M ≠ N
    suffices for distinct encodings). -/
theorem wand_collapse_value (M N : Term)
    (hMcl : M.closed) (hNcl : N.closed)
    (hEncodeNeq : M.encode ≠ N.encode) :
    ∃ V_M V_N : Term,
      IsValue V_M ∧ IsValue V_N ∧
      V_M ≠ V_N ∧
      StepStar (.app (.fexpr idBody) M) V_M ∧
      StepStar (.app (.fexpr idBody) N) V_N :=
  ⟨M.encode, N.encode,
    isValue_encode M, isValue_encode N,
    hEncodeNeq,
    fexpr_idBody_stepStar M hMcl, fexpr_idBody_stepStar N hNcl⟩

/-- **Value-level distinguishability headline.** For any *syntactically
    distinct* closed `M, N`, the un-gated reflective context distinguishes
    them by reducing to distinct values. -/
theorem wand_distinguishes_distinct_terms (M N : Term)
    (hMcl : M.closed) (hNcl : N.closed) (hNeq : M ≠ N) :
    ∃ V_M V_N : Term,
      IsValue V_M ∧ IsValue V_N ∧
      V_M ≠ V_N ∧
      StepStar (.app (.fexpr idBody) M) V_M ∧
      StepStar (.app (.fexpr idBody) N) V_N :=
  wand_collapse_value M N hMcl hNcl (Term.encode_ne_of_ne hNeq)

end FexprTrivial
