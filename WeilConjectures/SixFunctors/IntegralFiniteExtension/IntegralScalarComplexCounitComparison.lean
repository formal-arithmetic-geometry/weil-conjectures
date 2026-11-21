/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement

/-! # The cochain counit for the two fixed completed scalar models

## References

* [Stacks, Tag 06YY]
* [Stacks, Tag 07A4]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  completedCoefficientMap completedScalarCounit pbcComplexCounit

-- Normalize the shared scalar witness through the two localization factorizations.
/-- The canonical cochain counit is the counit of the same completed scalar witness. -/
theorem pbcComplexCounit_eq_completedScalarCounit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    pbcComplexCounit (completedCoefficientMap l E L ι X) P =
      completedScalarCounit.{u, u} l E L ι X P := by
  simp only [pbcComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors]
  erw [(pbcDerivedExtend (completedCoefficientMap l E L ι X)).map_id,
    DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id, Category.comp_id]
  with_unfolding_all rfl

/-- Rewrite a prescribed scalar-comparison square using the canonical cochain counit. -/
theorem completedScalarCounit_comparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (t : integralOrdinaryScalar l E L ι X ≅
      completedOrdinaryScalarExtension.{u, u} l E L ι X)
    (e : integralOrdinaryDerivedScalar l E L ι X ≅
      completedDerivedScalarExtension.{u, u} l E L ι X)
    (he : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι X P =
        (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P))
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    e.hom.app (DerivedCategory.Q.obj P) ≫
        pbcComplexCounit (completedCoefficientMap l E L ι X) P =
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P) := by
  rw [pbcComplexCounit_eq_completedScalarCounit]
  exact he P

end WeilConjectures.IntegralFiniteExtension
