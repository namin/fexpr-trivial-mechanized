/-
  Wand's equational theory `Eq_M` — and Wand's negative observation
  about it.

  Wand 1998 considers the equational theory closed under β + reify +
  reflect + full structural congruence (we call it `EqM` here). The
  paper's headline result is that **this theory is unsound** under
  contextual observation: it equates terms that a reflective context
  can pry apart on convergence.

  This file mechanizes:

    - `wand_collapse_abstract` / `wand_collapse_syntactic`: any
      *value-sound* relation closed under composition with
      `(fexpr idBody) ·` cannot equate two closed terms with distinct
      Mogensen–Scott codes (or, contrapositively, two distinct closed
      terms by Lemma 1.3).

    - `EqM_relates_β_pair`: `EqM` relates a specific β-equivalent
      pair `termLHS = (λx.x)(λy.y)` and `termRHS = λy.y`. This is
      one β-step plus the equivalence-closure rules, no reflection
      required to derive the relation.

    - `EqM_unsound_under_reflection`: composing that EqM relation
      with the reflective context `(fexpr divBody) ·` (via the `appR`
      congruence) gives two terms whose reduction outcomes are
      provably asymmetric: one converges to `idA`, the other reaches
      the divergent term `Ω` along a concrete reduction path.

  Together: EqM equates β-equivalent terms (by definition of being
  closed under β + congruence), but the reflective context makes that
  pair operationally asymmetric — so EqM is not contextually sound.
  This is exactly Wand's claim that the natural equational theory of
  the reflective λ-calculus is unsound.

  Sorry-free.

  ## A note on `ValueSound`

  Earlier drafts attempted to refute `ValueSound EqM` (defined as: if
  `EqM M N` and both reduce to values, the values are syntactically
  equal). That refutation goes through trivially via `EqM.lamIn`
  applied to a β-step inside a binder — but it doesn't really capture
  Wand's observation, because `ValueSound` is too strong: it fails
  for any equational theory containing β + lamIn, in *any* calculus
  (reflective or not). The refutation in this file uses convergence
  asymmetry through the reflective context, which is the genuinely
  reflective negative result Wand identifies.
-/
import FexprTrivial.Term
import FexprTrivial.Subst
import FexprTrivial.Coding
import FexprTrivial.Reduction
import FexprTrivial.LemmaOne
import FexprTrivial.Determinism
import FexprTrivial.Discriminator
import FexprTrivial.WandValue
import FexprTrivial.Theorem1Concrete
namespace FexprTrivial

/-! ### `EqM`: the smallest reflective-rewrite-respecting equivalence

  The closure of `Step` under reflexive/symmetric/transitive equivalence
  plus full structural congruence. Since `Step` already includes β,
  reify, and reflect, the equivalence closure is exactly Wand's
  syntactically-defined equational theory. The full congruence
  constructors (`appL`, `appR`, `lamIn`, `fexprIn`, `evalIn`) ensure
  `EqM` is a *compatible* relation — closed under arbitrary contexts.
-/

inductive EqM : Term → Term → Prop where
  | step    (M N : Term) : Step M N → EqM M N
  | refl    (M : Term)   : EqM M M
  | sym     (M N : Term) : EqM M N → EqM N M
  | trans   (M N P : Term) : EqM M N → EqM N P → EqM M P
  | appL    (M M' N : Term) : EqM M M' → EqM (.app M N) (.app M' N)
  | appR    (M N N' : Term) : EqM N N' → EqM (.app M N) (.app M N')
  | lamIn   (x : Name) (M M' : Term) : EqM M M' → EqM (.lam x M) (.lam x M')
  | fexprIn (M M' : Term) : EqM M M' → EqM (.fexpr M) (.fexpr M')
  | evalIn  (M M' : Term) : EqM M M' → EqM (.eval M) (.eval M')

namespace EqM

/-- `StepStar` collapses to `EqM`. -/
theorem of_stepStar : ∀ {M N : Term}, StepStar M N → EqM M N
  | _, _, .refl _ => .refl _
  | _, _, .step _ _ _ s rest => .trans _ _ _ (.step _ _ s) (of_stepStar rest)

/-- App-congruence: lift `EqM` on both sides simultaneously. -/
theorem app_cong {M M' N N' : Term} (hM : EqM M M') (hN : EqM N N') :
    EqM (.app M N) (.app M' N') :=
  .trans _ _ _ (.appL _ _ _ hM) (.appR _ _ _ hN)

end EqM

/-! ### Properties of equational theories that drive the collapse

  Two predicates over relations: `ValueSound` (a strong, perhaps
  *too*-strong, soundness notion) and `CompatFexprId` (closure under
  the reflective context). Wand's collapse is a statement about any
  relation satisfying both.
-/

/-- An equational theory `R` is *value-sound* iff whenever `R M N` and
    both `M` and `N` reduce to values, those values are syntactically
    equal. Used in the abstract collapse below. -/
def ValueSound (R : Term → Term → Prop) : Prop :=
  ∀ {M N V_M V_N : Term},
    R M N →
    StepStar M V_M → IsValue V_M →
    StepStar N V_N → IsValue V_N →
    V_M = V_N

/-- Closure under composition with `(fexpr idBody) ·`. Any `R` closed
    under right-application of a fixed term satisfies this; in
    particular, every `R` containing the congruence rule `appR` does. -/
def CompatFexprId (R : Term → Term → Prop) : Prop :=
  ∀ {M N : Term}, R M N → R (.app (.fexpr idBody) M) (.app (.fexpr idBody) N)

/-- `EqM` itself is closed under `(fexpr idBody) ·` by its `appR`
    congruence rule. -/
theorem EqM.compat_fexprId : CompatFexprId EqM :=
  fun h => .appR _ _ _ h

/-! ### Abstract collapse: any value-sound, compatible R is trivial -/

/-- **Wand's collapse, abstract form.** Any value-sound equational
    theory `R` that is closed under composition with `(fexpr idBody) ·`
    cannot equate two closed terms whose Mogensen–Scott codes differ.

    The proof is short: `R` lifts the relation through the reflective
    context to `(fexpr idBody) M` vs `(fexpr idBody) N`. Both reduce
    to the operands' codes (`fexpr_idBody_stepStar` from
    `Discriminator.lean`). Value-soundness forces the codes to be
    equal — contradicting the distinct-codes hypothesis. -/
theorem wand_collapse_abstract
    {R : Term → Term → Prop}
    (hSound : ValueSound R)
    (hCompat : CompatFexprId R)
    {M N : Term} (hMcl : M.closed) (hNcl : N.closed)
    (hEncodeNeq : M.encode ≠ N.encode) :
    ¬ R M N := by
  intro hRMN
  have hR_under : R (.app (.fexpr idBody) M) (.app (.fexpr idBody) N) :=
    hCompat hRMN
  have hMto : StepStar (.app (.fexpr idBody) M) M.encode :=
    fexpr_idBody_stepStar M hMcl
  have hNto : StepStar (.app (.fexpr idBody) N) N.encode :=
    fexpr_idBody_stepStar N hNcl
  have hEncEq : M.encode = N.encode :=
    hSound hR_under hMto (isValue_encode M) hNto (isValue_encode N)
  exact hEncodeNeq hEncEq

/-- **Wand's collapse, syntactic form.** Same as above, with the
    `M.encode ≠ N.encode` hypothesis discharged via Lemma 1.3
    (`encode_injective`): syntactically-distinct closed terms have
    distinct codes, so a value-sound `R` cannot equate them. -/
theorem wand_collapse_syntactic
    {R : Term → Term → Prop}
    (hSound : ValueSound R)
    (hCompat : CompatFexprId R)
    {M N : Term} (hMcl : M.closed) (hNcl : N.closed)
    (hNeq : M ≠ N) :
    ¬ R M N :=
  wand_collapse_abstract hSound hCompat hMcl hNcl (Term.encode_ne_of_ne hNeq)

/-! ### EqM relates β-equivalent pairs

  `EqM` is closed under β by its `step` constructor. This is a
  trivial fact — recorded for the next theorem. -/

/-- `EqM` relates the β-redex `(λx.x)(λy.y)` and its reduct `λy.y`
    via a single β-step. -/
theorem EqM_relates_β_pair : EqM termLHS termRHS :=
  .step _ _ termLHS_step_termRHS

/-! ### Convergence-soundness as Wand's notion of soundness

  Wand's actual soundness notion is *contextual* / *convergence*
  equivalence: `R M N` should preserve the observation `Converges`.
  We refute this for `EqM`. -/

/-- An equational theory `R` is *convergence-sound* iff `R`-related
    terms have the same convergence behavior. This is the property
    Wand's Theorem 1 actually targets — distinct from the stricter
    `ValueSound` of the abstract collapse above. -/
def ConvergenceSound (R : Term → Term → Prop) : Prop :=
  ∀ {M N : Term}, R M N → (Converges M ↔ Converges N)

/-! ### The headline negative result: `EqM` is not convergence-sound -/

/-- **`EqM` is not convergence-sound.** The β-equivalent pair
    `termLHS ≡β termRHS` lifts via `appR` to an `EqM` relation
    between `(fexpr divBody) termRHS` and `(fexpr divBody) termLHS`.
    The first converges to `idA` (Theorem1Concrete's
    `fexprDiv_termRHS_converges`); the second has its unique
    reduction path passing through `Ω` (`termLHS_cascade_to_omega`)
    and `Ω` doesn't converge (`omega_diverges`). With Step-
    determinism (`Determinism.lean`'s `not_converges_of_stepStar_diverges`),
    we conclude `¬ Converges` on the second.

    This is **Wand's negative result in canonical form**: a context
    in which the equational theory `EqM` (β + reify + reflect + full
    congruence) equates terms whose convergence behaviors differ.
    Hence no equational theory of this shape is contextually sound
    in the reflective calculus — exactly the unsoundness Wand 1998
    establishes. -/
theorem EqM_not_convergenceSound : ¬ ConvergenceSound EqM := by
  intro hSound
  -- The relation between the two reflective contexts.
  have hEq : EqM (.app (.fexpr divBody) termRHS) (.app (.fexpr divBody) termLHS) :=
    .appR _ _ _ (.sym _ _ EqM_relates_β_pair)
  have hConv_LHS : Converges (.app (.fexpr divBody) termRHS) :=
    fexprDiv_termRHS_converges
  have hNotConv_RHS : ¬ Converges (.app (.fexpr divBody) termLHS) :=
    not_converges_of_stepStar_diverges termLHS_cascade_to_omega omega_diverges
  -- ConvergenceSound forces them to match — contradiction.
  exact hNotConv_RHS ((hSound hEq).mp hConv_LHS)

/-- **Wand 1998 — the punchline, Wand's notion.** No equational theory
    closed under `EqM` (i.e. β + reify + reflect + full congruence)
    can be convergence-sound. -/
theorem wand_unsoundness :
    ∀ {R : Term → Term → Prop},
      (∀ {M N : Term}, EqM M N → R M N) →
      ¬ ConvergenceSound R := by
  intro R hContains hSound
  apply EqM_not_convergenceSound
  intro M N hEqM
  exact hSound (hContains hEqM)

end FexprTrivial
