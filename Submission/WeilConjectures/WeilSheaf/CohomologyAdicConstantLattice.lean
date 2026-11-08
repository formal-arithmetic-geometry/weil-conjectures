/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyDualityFrobenius
public import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.ConstantIntLowerStar
public import Submission.WeilConjectures.WeilSheaf.CohomologyAdicConstantExt

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The geometric Frobenius of `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` is the pullback along the Galois Frobenius

Through the identification `Hʳ(Y ⊗ k̄, ℚ̄_ℓ) ≅ Hʳ(Ȳ_proét, ℚ̄_ℓ)` of the cohomology of the constant
Weil sheaf with pro-étale cohomology, the geometric Frobenius is the pullback
`Fr^* : Hʳ(Ȳ, ℚ̄_ℓ) ⟶ Hʳ(Ȳ, ℚ̄_ℓ)` along the geometric Galois Frobenius `Fr : Ȳ ≅ Ȳ`
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback`).
In particular it preserves the image of the integral cohomology `Hʳ(Ȳ, ℤ_ℓ)`, on which it is the
pullback `Fr^*` of integral cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian MonoidalCategory

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius on `Ext(ℤ, ℚ̄_ℓ)` computed with an injective resolution of the constant
pro-étale Weil sheaf is the pullback along the geometric Galois Frobenius. -/
theorem extFrobenius_eq_adicConstantHPullback
    (I : InjectiveResolution (ProEtaleWeilSheaf.adicConstant k₀ l Y)) (r : ℕ)
    (x : Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj (ProEtaleWeilSheaf.adicConstant k₀ l Y))
      r) :
    extFrobenius I r x =
      adicConstantHPullback l (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius r x := by
  rw [extFrobenius_eq_extFrobeniusOfResolution, extFrobeniusOfResolution_eq,
    adicConstantHPullback_apply, Ext.mk₀CompMk₀,
    ← constantIntSheafToLowerStar_eq_constantIntIsoLowerStar_hom]
  rfl

end ProEtaleWeilSheaf

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

set_option maxRecDepth 4000 in
/-- **The geometric Frobenius of `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` is the pullback along the Galois Frobenius.**
`Hʳ(Y ⊗ k̄, ℚ̄_ℓ) ≅ Hʳ(Ȳ_proét, ℚ̄_ℓ)` as `ℚ̄_ℓ`-vector spaces, the geometric Frobenius of the
constant Weil sheaf corresponding to the pullback `Fr^*` along the geometric Galois Frobenius
`Fr : Ȳ ≅ Ȳ` (`AlgebraicGeometry.ProEtale.adicConstantHPullback`). -/
theorem exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback (r : ℕ) :
    ∃ Θ : AdicConstantH l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber r ≃ₗ[PadicAlgCl l]
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).carrier,
      ∀ x, Θ (adicConstantHPullback l (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius r x) =
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).frobenius (Θ x) := by
  obtain ⟨Θ, hΘ⟩ := exists_linearEquiv_adicConstantH_cohomology
    (injectiveResolution (WeilSheaf.adicConstant k₀ l Y).obj) r
  refine ⟨Θ, fun x ↦ ?_⟩
  refine (congrArg Θ (ProEtaleWeilSheaf.extFrobenius_eq_adicConstantHPullback
    (injectiveResolution (WeilSheaf.adicConstant k₀ l Y).obj) r x)).symm.trans ?_
  exact hΘ x

end WeilSheaf

end AlgebraicGeometry
