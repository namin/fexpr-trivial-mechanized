/-
  Wand 1998, Lemma 1.

  In Wand's paper, Lemma 1 collects basic facts about the Mogensen–Scott
  encoding `⌜·⌝`:

    1.1  every code is a value                       (mechanized in Reduction.lean
                                                      as `isValue_encode`)
    1.2  free variables of `⌜M⌝` equal those of `M`
         restricted to non-reserved names            (this file)
    1.3  the encoding is structurally injective —
         `⌜M⌝ = ⌜N⌝ ↔ M = N`                          (this file)

  These are the syntactic preliminaries Wand uses to argue, in §4,
  that a context can recover the source term from its code: structural
  injectivity is what makes "comparing codes" a meaningful test.

  Sorry-free.
-/
import FexprTrivial.Term
import FexprTrivial.Coding
namespace FexprTrivial

namespace Term

/-! ### Lemma 1.2: free-variable preservation

  The encoding wraps each constructor with `λabcde.`, so the encoded
  term has the reserved names a..e as binders. Free variables of `⌜M⌝`
  that come from `M` survive the wrap (they are not a..e by the
  user-name-safety convention) and are exactly the free variables of
  `M`. The reverse inclusion was the missing direction in the substrate
  (`mem_fv_encode` covers ⊆; this lemma covers ⊇ under safety).
-/

/-- Forward direction (already proved): every free var of `⌜M⌝` is a free var of `M`. -/
theorem fv_encode_subset {M : Term} {y : Name} :
    y ∈ (M.encode).fv → y ∈ M.fv := mem_fv_encode

/-- Reverse direction: if `y` is a free variable of `M` and is not one
    of the reserved encoding-binder names, then `y` is also a free
    variable of `⌜M⌝`. -/
theorem fv_encode_supset {M : Term} {y : Name}
    (hsafe : y ∉ codeReserved) (hyM : y ∈ M.fv) : y ∈ (M.encode).fv := by
  -- Unpack the safety hypothesis once.
  have hexpand : y ∉ ([codeA, codeB, codeC, codeD, codeE] : List Name) := hsafe
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hexpand
  obtain ⟨hyA, hyB, hyC, hyD, hyE⟩ := hexpand
  induction M with
  | var x =>
      rw [fv_var, List.mem_singleton] at hyM
      subst hyM
      simp only [encode]
      rw [mem_fv_wrapAbcde]
      refine ⟨?_, hyA, hyB, hyC, hyD, hyE⟩
      rw [fv_app]; apply List.mem_append.mpr; right
      rw [fv_var]; exact List.mem_singleton.mpr rfl
  | lam x M' ih =>
      rw [mem_fv_lam_iff] at hyM
      obtain ⟨hyM', hyx⟩ := hyM
      simp only [encode]
      rw [mem_fv_wrapAbcde]
      refine ⟨?_, hyA, hyB, hyC, hyD, hyE⟩
      rw [fv_app]; apply List.mem_append.mpr; right
      rw [mem_fv_lam_iff]
      exact ⟨ih hyM', hyx⟩
  | app M N ihM ihN =>
      rw [fv_app] at hyM
      rcases List.mem_append.mp hyM with hyM' | hyN'
      · simp only [encode]
        rw [mem_fv_wrapAbcde]
        refine ⟨?_, hyA, hyB, hyC, hyD, hyE⟩
        rw [fv_app]; apply List.mem_append.mpr; left
        rw [fv_app]; apply List.mem_append.mpr; right
        exact ihM hyM'
      · simp only [encode]
        rw [mem_fv_wrapAbcde]
        refine ⟨?_, hyA, hyB, hyC, hyD, hyE⟩
        rw [fv_app]; apply List.mem_append.mpr; right
        exact ihN hyN'
  | fexpr M' ih =>
      rw [fv_fexpr] at hyM
      simp only [encode]
      rw [mem_fv_wrapAbcde]
      refine ⟨?_, hyA, hyB, hyC, hyD, hyE⟩
      rw [fv_app]; apply List.mem_append.mpr; right
      exact ih hyM
  | eval M' ih =>
      rw [fv_eval] at hyM
      simp only [encode]
      rw [mem_fv_wrapAbcde]
      refine ⟨?_, hyA, hyB, hyC, hyD, hyE⟩
      rw [fv_app]; apply List.mem_append.mpr; right
      exact ih hyM

/-- Wand Lemma 1.2: free variables of `⌜M⌝` are the free variables of
    `M` minus the reserved names. -/
theorem mem_fv_encode_iff {M : Term} {y : Name} :
    y ∈ (M.encode).fv ↔ y ∈ M.fv ∧ y ∉ codeReserved := by
  constructor
  · intro hy
    refine ⟨fv_encode_subset hy, ?_⟩
    intro hres
    -- `⌜M⌝` has the reserved names as binders. Inspect by case on M.
    have hwrap : ∀ (body : Term),
        y ∈ (wrapAbcde body).fv → y ≠ codeA ∧ y ≠ codeB ∧ y ≠ codeC ∧ y ≠ codeD ∧ y ≠ codeE := by
      intro body hbody
      rw [mem_fv_wrapAbcde] at hbody
      exact ⟨hbody.2.1, hbody.2.2.1, hbody.2.2.2.1, hbody.2.2.2.2.1, hbody.2.2.2.2.2⟩
    have hres' : y ∈ ([codeA, codeB, codeC, codeD, codeE] : List Name) := hres
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hres'
    cases M with
    | var x =>
        simp only [encode] at hy
        obtain ⟨hA, hB, hC, hD, hE⟩ := hwrap _ hy
        rcases hres' with rfl | rfl | rfl | rfl | rfl
        · exact hA rfl
        · exact hB rfl
        · exact hC rfl
        · exact hD rfl
        · exact hE rfl
    | lam x M' =>
        simp only [encode] at hy
        obtain ⟨hA, hB, hC, hD, hE⟩ := hwrap _ hy
        rcases hres' with rfl | rfl | rfl | rfl | rfl
        · exact hA rfl
        · exact hB rfl
        · exact hC rfl
        · exact hD rfl
        · exact hE rfl
    | app M' N' =>
        simp only [encode] at hy
        obtain ⟨hA, hB, hC, hD, hE⟩ := hwrap _ hy
        rcases hres' with rfl | rfl | rfl | rfl | rfl
        · exact hA rfl
        · exact hB rfl
        · exact hC rfl
        · exact hD rfl
        · exact hE rfl
    | fexpr M' =>
        simp only [encode] at hy
        obtain ⟨hA, hB, hC, hD, hE⟩ := hwrap _ hy
        rcases hres' with rfl | rfl | rfl | rfl | rfl
        · exact hA rfl
        · exact hB rfl
        · exact hC rfl
        · exact hD rfl
        · exact hE rfl
    | eval M' =>
        simp only [encode] at hy
        obtain ⟨hA, hB, hC, hD, hE⟩ := hwrap _ hy
        rcases hres' with rfl | rfl | rfl | rfl | rfl
        · exact hA rfl
        · exact hB rfl
        · exact hC rfl
        · exact hD rfl
        · exact hE rfl
  · intro ⟨hyM, hsafe⟩
    exact fv_encode_supset hsafe hyM

/-- Wand Lemma 1.2 (closure form, full iff): `⌜M⌝.closed ↔ M.closed`,
    provided every free variable of `M` is non-reserved. The forward
    direction (`closed_encode`) was already in the substrate. -/
theorem closed_encode_iff_safe {M : Term}
    (hsafe : ∀ y ∈ M.fv, y ∉ codeReserved) :
    (M.encode).closed ↔ M.closed := by
  constructor
  · intro hEnc
    unfold closed
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro y hyM
    have hy_nores : y ∉ codeReserved := hsafe y hyM
    have hyEnc : y ∈ (M.encode).fv := fv_encode_supset hy_nores hyM
    unfold closed at hEnc; rw [hEnc] at hyEnc; cases hyEnc
  · exact closed_encode

/-! ### Lemma 1.3: structural injectivity

  The encoding distinguishes terms by their head constructor (via the
  reserved markers `codeA..codeE`) and is injective on each constructor
  by structural recursion on the operands.
-/

/-- Structural injectivity for `wrapAbcde`. -/
theorem wrapAbcde_injective {b₁ b₂ : Term} (h : wrapAbcde b₁ = wrapAbcde b₂) :
    b₁ = b₂ := by
  unfold wrapAbcde at h
  simp only [Term.lam.injEq, true_and] at h
  exact h

/-- Wand Lemma 1.3: structural injectivity of the encoding. -/
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

/-- Contrapositive form, useful for distinguishability arguments:
    syntactically distinct terms have distinct encodings. -/
theorem encode_ne_of_ne {M N : Term} (h : M ≠ N) : M.encode ≠ N.encode :=
  fun heq => h (encode_injective heq)

end Term
end FexprTrivial
