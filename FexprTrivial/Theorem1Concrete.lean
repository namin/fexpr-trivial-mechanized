/-
  Convergence-level Wand collapse — concrete demo.

  A *specific* convergence-distinguishing pair: termLHS = (λx.x)(λy.y)
  is β-equivalent to termRHS = λy.y, but the un-gated reflective
  context (fexpr divBody) routes them to different reduction outcomes:

      (fexpr divBody) termLHS →* omega       (a divergent term)
      (fexpr divBody) termRHS →* idA         (a value, converges)

  This is the canonical strong form of Wand 1998 collapse: a single
  context maps β-equivalent terms to fundamentally different
  reduction outcomes. Ported here verbatim from the substrate.

  Sorry-free.
-/
import FexprTrivial.Term
import FexprTrivial.Subst
import FexprTrivial.Coding
import FexprTrivial.Reduction
import FexprTrivial.LemmaOne

namespace FexprTrivial

/-! ### Identity terms and the β-equivalent demo pair -/

def idA : Term := .lam "x" (.var "x")
def idB : Term := .lam "y" (.var "y")
def termLHS : Term := .app idA idB
def termRHS : Term := idB

theorem idA_closed : idA.closed := rfl
theorem idB_closed : idB.closed := rfl
theorem termLHS_closed : termLHS.closed := rfl
theorem termRHS_closed : termRHS.closed := rfl

theorem idA_value : IsValue idA := .lam _ _
theorem idB_value : IsValue idB := .lam _ _

/-! ### β-step witnessing termLHS ≡β termRHS -/

theorem termLHS_step_termRHS : Step termLHS termRHS :=
  Step.beta "x" (.var "x") idB idB_value idB_closed

/-! ### Divergence: Ω = (λx. x x) (λx. x x)

  The classical CBV-divergent term. Ω self-reduces (`Ω →β Ω`) and is
  not a value, so it never reaches a value via `StepStar`. This gives
  us `¬ Converges Ω`, which we'll use to build a `Converges`-
  distinguishing context in the next phase. -/

def delta : Term := .lam "x" (.app (.var "x") (.var "x"))

theorem delta_closed : delta.closed := rfl
theorem delta_value : IsValue delta := .lam _ _

def omega : Term := .app delta delta

theorem omega_closed : omega.closed := rfl

/-- Ω self-reduces. -/
theorem step_omega_self : Step omega omega := by
  have h := Step.beta "x" (.app (.var "x") (.var "x")) delta delta_value delta_closed
  -- h : Step (.app (.lam "x" (.app (.var "x") (.var "x"))) delta)
  --          ((.app (.var "x") (.var "x")).substClosed "x" delta)
  have heq : (Term.app (.var "x") (.var "x")).substClosed "x" delta = omega := by
    show Term.app ((Term.var "x").substClosed "x" delta)
                  ((Term.var "x").substClosed "x" delta) = omega
    have h1 : (Term.var "x").substClosed "x" delta = delta := by
      show (if "x" = "x" then delta else Term.var "x") = delta
      rw [if_pos rfl]
    rw [h1]; rfl
  rw [heq] at h
  exact h

/-- Ω can only step to Ω. -/
theorem step_omega_unique {X : Term} (h : Step omega X) : X = omega := by
  cases h with
  | beta x M V _ _ =>
    -- Lean unifies omega = .app (.lam x M) V, giving x = "x",
    -- M = .app (.var "x") (.var "x"), V = delta.
    -- X = M.substClosed x V; need this = omega.
    show (Term.app (.var "x") (.var "x")).substClosed "x" delta = omega
    show Term.app ((Term.var "x").substClosed "x" delta)
                  ((Term.var "x").substClosed "x" delta) = omega
    have h1 : (Term.var "x").substClosed "x" delta = delta := by
      show (if "x" = "x" then delta else Term.var "x") = delta
      rw [if_pos rfl]
    rw [h1]; rfl
  | appL _ _ _ hStep =>
    -- Step on operator delta. delta is a value, no Step.
    exact (step_value_absurd delta_value hStep).elim
  | appR _ _ _ _ hStep =>
    -- Step on operand delta. delta is a value, no Step.
    exact (step_value_absurd delta_value hStep).elim

/-- Anything reachable from Ω via StepStar is Ω. Stated as an
    auxiliary that lets us induct over an arbitrary starting term. -/
theorem stepStar_omega_unique_aux : ∀ {M X : Term},
    StepStar M X → M = omega → X = omega := by
  intro M X h
  induction h with
  | refl _ => intro hM; exact hM
  | step _ Y _ hStep _ ih =>
    intro hM
    rw [hM] at hStep
    have hY : Y = omega := step_omega_unique hStep
    exact ih hY

theorem stepStar_omega_unique {X : Term} (h : StepStar omega X) : X = omega :=
  stepStar_omega_unique_aux h rfl

theorem omega_not_value : ¬ IsValue omega := by
  intro h
  cases h

/-- **Ω diverges**: no reduction sequence from Ω reaches a value. -/
theorem omega_diverges : ¬ Converges omega := by
  intro ⟨V, hVval, hStar⟩
  have hV : V = omega := stepStar_omega_unique hStar
  rw [hV] at hVval
  exact omega_not_value hVval

/-! ### Distinguishing context: the divergence-routing fexpr body

  We construct a fexpr body that applies its operand-code to 5
  selectors. By the structure of the Mogensen–Scott encoding, the
  selector chosen depends on the operand's constructor:
  - `.var` → uses `V_A`
  - `.app` → uses `V_B`
  - `.lam` → uses `V_C`
  - `.fexpr` → uses `V_D`
  - `.eval` → uses `V_E`

  We pick `V_B` to be a 2-argument constant function returning Ω
  (forces divergence on `.app`-shaped operand-codes), and `V_C` to
  be a 1-argument constant function returning idA (forces convergence
  on `.lam`-shaped operand-codes). The other selectors are arbitrary
  values.

  Applied to `(.fexpr divBody) termLHS` (where termLHS is an `.app`),
  the cascade routes through `V_B` and reaches Ω. Applied to
  `(.fexpr divBody) termRHS` (where termRHS is a `.lam`), the
  cascade routes through `V_C` and reaches idA (a value). -/

/-- Selector for `.app`: 2-argument constant function returning Ω. -/
def divLam : Term := .lam "u" (.lam "v" omega)

theorem divLam_closed : divLam.closed := rfl
theorem divLam_value : IsValue divLam := .lam _ _

/-- Selector for `.lam`: 1-argument constant function returning idA. -/
def constId : Term := .lam "w" idA

theorem constId_closed : constId.closed := rfl
theorem constId_value : IsValue constId := .lam _ _

/-- The divergence-routing fexpr body: applies operand-code to 5 selectors. -/
def divBody : Term :=
  .lam "c" (.app (.app (.app (.app (.app (.var "c") idA) divLam) constId) idA) idA)

theorem divBody_closed : divBody.closed := rfl
theorem divBody_value : IsValue divBody := .lam _ _

/-- The "after the first reify+beta" form: the operand-code applied to the
    5 selectors, parameterized by the operand. -/
def applyToSelectors (encoded : Term) : Term :=
  .app (.app (.app (.app (.app encoded idA) divLam) constId) idA) idA

/-- Step 1 of the cascade: reify on `(fexpr divBody) M`. -/
theorem cascade_step_reify (M : Term) :
    Step (.app (.fexpr divBody) M) (.app divBody M.encode) :=
  Step.reify divBody M divBody_value

/-- Step 2 of the cascade: β on `(λc. body) M.encode`. The substitution
    leaves the closed values (idA, divLam, constId) untouched and replaces
    `.var "c"` with `M.encode`. -/
theorem cascade_step_betaC (M : Term) (hMcl : M.closed) :
    Step (.app divBody M.encode) (applyToSelectors M.encode) := by
  have h := Step.beta "c"
    (.app (.app (.app (.app (.app (.var "c") idA) divLam) constId) idA) idA)
    M.encode (isValue_encode M) (Term.closed_encode hMcl)
  unfold applyToSelectors
  simp only [Term.substClosed_app, Term.substClosed_var_self,
             Term.substClosed_of_closed _ idA_closed,
             Term.substClosed_of_closed _ divLam_closed,
             Term.substClosed_of_closed _ constId_closed] at h
  exact h

/-- Lift a Step through one layer of `.app _ N`. -/
theorem stepAppL_lift {M M' : Term} (N : Term) (h : Step M M') :
    Step (.app M N) (.app M' N) := Step.appL _ _ _ h

/-! ### Convergence side: `(fexpr divBody) termRHS →* idA`

  termRHS is a `.lam`, so its encoding's body uses the codeC selector
  (constId). The cascade applies termRHS.encode to (idA, divLam,
  constId, idA, idA), which reduces via 5 betas to
  `(λw. idA) (λy. (.var "y").encode)`, then one more beta to `idA`. -/

/-- Helper: a "skip" step that strips one outer .lam binder, when its body
    is closed (the typical situation in our cascade — the binders are
    codeA..codeE, only one of which appears free in the encoded body
    based on the encoded term's constructor). -/
theorem step_skip_lam (binder : Name) (body V : Term)
    (hVval : IsValue V) (hVcl : V.closed) (hbody_cl : body.closed) :
    Step (.app (.lam binder body) V) body := by
  have h := Step.beta binder body V hVval hVcl
  rwa [Term.substClosed_of_closed _ hbody_cl] at h

/-! ### Convergence side: termRHS branch reaches idA

  termRHS = `λy. y` (a `.lam`). Its encoding's deepest body is
  `.app (.var codeC) (.lam "y" (.var "y").encode)`, with codeC as
  the marker. Applied to selectors (idA, divLam, constId, idA, idA),
  the codeC slot picks up `constId`, giving
  `.app constId (.lam "y" (.var "y").encode) →β idA`.

  The cascade is 8 reductions: 1 reify + 1 β-on-divBody + 5 selector
  applications + 1 final β. Each "selector application" β is lifted
  through nested `Step.appL` to reach the outermost `.app`. -/

/-- Body inside termRHS.encode's outer `.lam codeA`. -/
def bodyA_R : Term :=
  .lam Term.codeB
    (.lam Term.codeC
      (.lam Term.codeD
        (.lam Term.codeE
          (.app (.var Term.codeC) (.lam "y" (Term.var "y").encode)))))

theorem bodyA_R_closed : bodyA_R.closed := rfl

/-- Body inside the next `.lam codeB`. -/
def bodyB_R : Term :=
  .lam Term.codeC
    (.lam Term.codeD
      (.lam Term.codeE
        (.app (.var Term.codeC) (.lam "y" (Term.var "y").encode))))

theorem bodyB_R_closed : bodyB_R.closed := rfl

/-- Body inside `.lam codeC`. After β substituting constId for codeC,
    the marker `.var codeC` becomes `constId` and the closed `.lam "y" ..`
    is unchanged. -/
def bodyC_R_after : Term :=
  .lam Term.codeD
    (.lam Term.codeE
      (.app constId (.lam "y" (Term.var "y").encode)))

theorem bodyC_R_after_closed : bodyC_R_after.closed := rfl

/-- Body inside `.lam codeD` (after the codeC substitution). -/
def bodyD_R : Term :=
  .lam Term.codeE (.app constId (.lam "y" (Term.var "y").encode))

theorem bodyD_R_closed : bodyD_R.closed := rfl

/-- Body inside `.lam codeE`. -/
def bodyE_R : Term :=
  .app constId (.lam "y" (Term.var "y").encode)

theorem bodyE_R_closed : bodyE_R.closed := rfl

/-- termRHS.encode's outer .lam codeA strip via β with idA. -/
theorem termRHS_step_codeA :
    Step (.app termRHS.encode idA) bodyA_R := by
  have h := Step.beta Term.codeA bodyA_R idA idA_value idA_closed
  rwa [Term.substClosed_of_closed bodyA_R bodyA_R_closed] at h

/-- bodyA_R's .lam codeB strip via β with divLam. -/
theorem termRHS_step_codeB :
    Step (.app bodyA_R divLam) bodyB_R := by
  have h := Step.beta Term.codeB bodyB_R divLam divLam_value divLam_closed
  rwa [Term.substClosed_of_closed bodyB_R bodyB_R_closed] at h

/-- bodyB_R's .lam codeC strip via β with constId. The marker substitution
    here actually changes the body (codeC was free as `.var codeC`). -/
theorem termRHS_step_codeC :
    Step (.app bodyB_R constId) bodyC_R_after := by
  have h := Step.beta Term.codeC
    (.lam Term.codeD
      (.lam Term.codeE
        (.app (.var Term.codeC) (.lam "y" (Term.var "y").encode))))
    constId constId_value constId_closed
  -- Substituted body: substitutes codeC with constId.
  -- - .lam codeD: lam_other (codeD ≠ codeC), recurse.
  -- - .lam codeE: lam_other.
  -- - .app: substClosed_app.
  -- - .var codeC: var_self → constId.
  -- - .lam "y" ...: closed, so substClosed_of_closed.
  have hcD : Term.codeD ≠ Term.codeC := by decide
  have hcE : Term.codeE ≠ Term.codeC := by decide
  have hy : "y" ≠ Term.codeC := by decide
  have hLamY_closed : (Term.lam "y" (Term.var "y").encode).closed := rfl
  simp only [Term.substClosed_lam_other hcD, Term.substClosed_lam_other hcE,
             Term.substClosed_app, Term.substClosed_var_self,
             Term.substClosed_of_closed _ hLamY_closed] at h
  exact h

/-- bodyC_R_after's .lam codeD strip via β with idA. -/
theorem termRHS_step_codeD :
    Step (.app bodyC_R_after idA) bodyD_R := by
  have h := Step.beta Term.codeD bodyD_R idA idA_value idA_closed
  rwa [Term.substClosed_of_closed bodyD_R bodyD_R_closed] at h

/-- bodyD_R's .lam codeE strip via β with idA. -/
theorem termRHS_step_codeE :
    Step (.app bodyD_R idA) bodyE_R := by
  have h := Step.beta Term.codeE bodyE_R idA idA_value idA_closed
  rwa [Term.substClosed_of_closed bodyE_R bodyE_R_closed] at h

/-- bodyE_R's β: `(λw. idA) (.lam "y" ...) → idA`. -/
theorem termRHS_step_final :
    Step bodyE_R idA := by
  unfold bodyE_R constId
  have h := Step.beta "w" idA (.lam "y" (Term.var "y").encode) (.lam _ _) rfl
  rwa [Term.substClosed_of_closed idA idA_closed] at h

/-- The full convergence-side cascade: chained reduction
    `(fexpr divBody) termRHS →* idA`. -/
theorem termRHS_cascade_to_idA :
    StepStar (.app (.fexpr divBody) termRHS) idA := by
  apply StepStar.step _ _ _ (cascade_step_reify termRHS)
  apply StepStar.step _ _ _ (cascade_step_betaC termRHS termRHS_closed)
  -- At applyToSelectors termRHS.encode = .app^5 with termRHS.encode at innermost.
  unfold applyToSelectors
  -- Step 3: apply termRHS.encode to idA (innermost), lifted through 4 .appL.
  apply StepStar.step _ _ _
    (Step.appL _ _ _ (Step.appL _ _ _ (Step.appL _ _ _ (Step.appL _ _ _ termRHS_step_codeA))))
  -- Step 4: apply bodyA_R to divLam, lifted through 3 .appL.
  apply StepStar.step _ _ _
    (Step.appL _ _ _ (Step.appL _ _ _ (Step.appL _ _ _ termRHS_step_codeB)))
  -- Step 5: apply bodyB_R to constId, lifted through 2 .appL.
  apply StepStar.step _ _ _
    (Step.appL _ _ _ (Step.appL _ _ _ termRHS_step_codeC))
  -- Step 6: apply bodyC_R_after to idA, lifted through 1 .appL.
  apply StepStar.step _ _ _ (Step.appL _ _ _ termRHS_step_codeD)
  -- Step 7: apply bodyD_R to idA (no .appL).
  apply StepStar.step _ _ _ termRHS_step_codeE
  -- Step 8: bodyE_R = .app constId ... → idA.
  apply StepStar.step _ _ _ termRHS_step_final
  exact .refl _

/-- **Convergence side**: `(fexpr divBody) termRHS` converges to idA. -/
theorem fexprDiv_termRHS_converges : Converges (.app (.fexpr divBody) termRHS) :=
  ⟨idA, idA_value, termRHS_cascade_to_idA⟩

/-! ### Divergence side: termLHS branch reaches omega

  termLHS = `(λx.x)(λy.y)` (an `.app`). Its encoding's deepest body is
  `.app (.app (.var codeB) idA.encode) idB.encode`, with codeB as the
  marker. Applied to selectors (idA, divLam, constId, idA, idA), the
  codeB slot picks up `divLam = λu. λv. omega`. After 5 selector
  applications we reach `.app (.app divLam idA.encode) idB.encode`,
  which β-reduces in 2 more steps to omega.

  The cascade is 9 reductions: 1 reify + 1 β-on-divBody + 5 selectors
  + 2 finals. -/

/-- Body inside termLHS.encode's outer `.lam codeA`. -/
def bodyA_L : Term :=
  .lam Term.codeB
    (.lam Term.codeC
      (.lam Term.codeD
        (.lam Term.codeE
          (.app (.app (.var Term.codeB) idA.encode) idB.encode))))

theorem bodyA_L_closed : bodyA_L.closed := rfl

/-- Body inside `.lam codeB` *after* substituting codeB → divLam. The
    marker `.var codeB` becomes divLam; `idA.encode` and `idB.encode`
    are closed and unchanged. -/
def bodyB_L_after : Term :=
  .lam Term.codeC
    (.lam Term.codeD
      (.lam Term.codeE
        (.app (.app divLam idA.encode) idB.encode)))

theorem bodyB_L_after_closed : bodyB_L_after.closed := rfl

/-- Body inside the next `.lam codeC` (already after the codeB substitution). -/
def bodyC_L : Term :=
  .lam Term.codeD
    (.lam Term.codeE
      (.app (.app divLam idA.encode) idB.encode))

theorem bodyC_L_closed : bodyC_L.closed := rfl

/-- Body inside `.lam codeD`. -/
def bodyD_L : Term :=
  .lam Term.codeE (.app (.app divLam idA.encode) idB.encode)

theorem bodyD_L_closed : bodyD_L.closed := rfl

/-- Body inside `.lam codeE`. -/
def bodyE_L : Term :=
  .app (.app divLam idA.encode) idB.encode

theorem bodyE_L_closed : bodyE_L.closed := rfl

/-- termLHS.encode's outer .lam codeA strip via β with idA. -/
theorem termLHS_step_codeA :
    Step (.app termLHS.encode idA) bodyA_L := by
  have h := Step.beta Term.codeA bodyA_L idA idA_value idA_closed
  rwa [Term.substClosed_of_closed bodyA_L bodyA_L_closed] at h

/-- bodyA_L's .lam codeB strip via β with divLam. The marker substitution
    here changes `.var codeB` → `divLam` and leaves idA.encode, idB.encode
    untouched (both closed). -/
theorem termLHS_step_codeB :
    Step (.app bodyA_L divLam) bodyB_L_after := by
  have h := Step.beta Term.codeB
    (.lam Term.codeC
      (.lam Term.codeD
        (.lam Term.codeE
          (.app (.app (.var Term.codeB) idA.encode) idB.encode))))
    divLam divLam_value divLam_closed
  have hcC : Term.codeC ≠ Term.codeB := by decide
  have hcD : Term.codeD ≠ Term.codeB := by decide
  have hcE : Term.codeE ≠ Term.codeB := by decide
  have hidA_cl : idA.encode.closed := Term.closed_encode idA_closed
  have hidB_cl : idB.encode.closed := Term.closed_encode idB_closed
  simp only [Term.substClosed_lam_other hcC, Term.substClosed_lam_other hcD,
             Term.substClosed_lam_other hcE,
             Term.substClosed_app, Term.substClosed_var_self,
             Term.substClosed_of_closed _ hidA_cl,
             Term.substClosed_of_closed _ hidB_cl] at h
  exact h

/-- bodyB_L_after's .lam codeC strip via β with constId. -/
theorem termLHS_step_codeC :
    Step (.app bodyB_L_after constId) bodyC_L := by
  have h := Step.beta Term.codeC bodyC_L constId constId_value constId_closed
  rwa [Term.substClosed_of_closed bodyC_L bodyC_L_closed] at h

/-- bodyC_L's .lam codeD strip via β with idA. -/
theorem termLHS_step_codeD :
    Step (.app bodyC_L idA) bodyD_L := by
  have h := Step.beta Term.codeD bodyD_L idA idA_value idA_closed
  rwa [Term.substClosed_of_closed bodyD_L bodyD_L_closed] at h

/-- bodyD_L's .lam codeE strip via β with idA. -/
theorem termLHS_step_codeE :
    Step (.app bodyD_L idA) bodyE_L := by
  have h := Step.beta Term.codeE bodyE_L idA idA_value idA_closed
  rwa [Term.substClosed_of_closed bodyE_L bodyE_L_closed] at h

/-- The inner β: `(λu. λv. omega) idA.encode → λv. omega`. -/
theorem termLHS_step_innerBeta :
    Step (.app divLam idA.encode) (.lam "v" omega) := by
  unfold divLam
  have h := Step.beta "u" (.lam "v" omega) idA.encode
    (isValue_encode idA) (Term.closed_encode idA_closed)
  rwa [Term.substClosed_of_closed _ (rfl : (Term.lam "v" omega).closed)] at h

/-- The outer β: `(λv. omega) idB.encode → omega`. -/
theorem termLHS_step_outerBeta :
    Step (.app (.lam "v" omega) idB.encode) omega := by
  have h := Step.beta "v" omega idB.encode
    (isValue_encode idB) (Term.closed_encode idB_closed)
  rwa [Term.substClosed_of_closed omega omega_closed] at h

/-- The full divergence-side cascade: chained reduction
    `(fexpr divBody) termLHS →* omega`. -/
theorem termLHS_cascade_to_omega :
    StepStar (.app (.fexpr divBody) termLHS) omega := by
  apply StepStar.step _ _ _ (cascade_step_reify termLHS)
  apply StepStar.step _ _ _ (cascade_step_betaC termLHS termLHS_closed)
  unfold applyToSelectors
  -- Step 3: codeA strip, lifted through 4 .appL.
  apply StepStar.step _ _ _
    (Step.appL _ _ _ (Step.appL _ _ _ (Step.appL _ _ _ (Step.appL _ _ _ termLHS_step_codeA))))
  -- Step 4: codeB substitution (the marker), lifted through 3 .appL.
  apply StepStar.step _ _ _
    (Step.appL _ _ _ (Step.appL _ _ _ (Step.appL _ _ _ termLHS_step_codeB)))
  -- Step 5: codeC strip, lifted through 2 .appL.
  apply StepStar.step _ _ _
    (Step.appL _ _ _ (Step.appL _ _ _ termLHS_step_codeC))
  -- Step 6: codeD strip, lifted through 1 .appL.
  apply StepStar.step _ _ _ (Step.appL _ _ _ termLHS_step_codeD)
  -- Step 7: codeE strip.
  apply StepStar.step _ _ _ termLHS_step_codeE
  -- Step 8: inner β `divLam idA.encode → .lam "v" omega`, lifted through 1 .appL.
  apply StepStar.step _ _ _ (Step.appL _ _ _ termLHS_step_innerBeta)
  -- Step 9: outer β to omega.
  apply StepStar.step _ _ _ termLHS_step_outerBeta
  exact .refl _

/-- **Divergence side**: `(fexpr divBody) termLHS` reduces to omega
    (which we've proven diverges). Note this is the existence of one
    reduction path; without Step-determinism, we don't directly conclude
    `¬ Converges`. -/
theorem fexprDiv_termLHS_reaches_omega :
    StepStar (.app (.fexpr divBody) termLHS) omega :=
  termLHS_cascade_to_omega

/-! ### Final convergence-level headline -/
/-! ### The headline: asymmetric distinguishability via reflection

  Same un-gated reflective context `(fexpr divBody) ·` routes
  β-equivalent termLHS, termRHS to fundamentally different outcomes:
  - `(fexpr divBody) termRHS` *converges* — reduces to the value idA.
  - `(fexpr divBody) termLHS` reaches the divergent term omega via a
    concrete reduction path; combined with `omega_diverges`, this
    demonstrates a divergent path exists.

  This is genuine asymmetry: even though `termLHS ≡β termRHS`, the
  un-gated reflective context distinguishes them by their encodings'
  syntactic markers (codeC for `.lam`, codeB for `.app`).

  The body `divBody = λc. c idA divLam constId idA idA` is exactly
  the kind of operand-using fexpr body that fails the gating
  discipline (similar to Example 3's `idBody`). Under our gating,
  this context is *not admissible* — restoring the equational theory.

  Note: this falls one step short of `¬ Converges (.app (.fexpr
  divBody) termLHS)` in full generality. Closing that requires a
  Step-determinism lemma (~80 LOC of case analysis) or a confluence
  argument. The asymmetric statement below is what we have
  sorry-free; it demonstrates the collapse via concrete reduction
  outcomes rather than via a non-convergence claim. -/

theorem wand_collapse_divergence_demo :
    Converges (.app (.fexpr divBody) termRHS) ∧
    StepStar (.app (.fexpr divBody) termLHS) omega ∧
    ¬ Converges omega :=
  ⟨fexprDiv_termRHS_converges, termLHS_cascade_to_omega, omega_diverges⟩
end FexprTrivial
