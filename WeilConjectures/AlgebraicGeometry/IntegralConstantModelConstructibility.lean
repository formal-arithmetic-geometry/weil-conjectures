/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalModels

/-! # Finite constant models under integral realization

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Definition 6.8.10 and
  Proposition 6.8.11.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
namespace AlgebraicGeometry.ProEtale.IntegralConstantModel

private theorem absolute_iff (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (N : AdicCompletion.Modules l E X) :
    IsConstantModelConstructible (DerivedNakayama.integerRing l E) X N ↔
      Scheme.IsCompletedConstantStratified X (Scheme.pbcIntegralDatum l E).ideal
        ((Scheme.pbcRestrict
          (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom).obj
          ((SheafOfModules.restrictScalars
            (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
            ((integralSectionFunctor l E X).obj N))) :=
  (integralSectionLocalModels l E X N).trans
    (Scheme.completedConstantModelTransport X (Scheme.pbcIntegralDatum l E) _)

/-- The fixed section-action realization identifies finite constant local models.
(Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11.) -/
theorem constructible_iff (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (sfbCondensedIntegers l E).X X)) :
    IsConstantModelConstructible (sfbCondensedIntegers l E).X X M ↔
      Scheme.IsCompletedConstantStratified X (Scheme.pbcIntegralDatum l E).ideal
        ((modulesFunctor l E X).obj M) := by
  exact (constantModel_comap_iff (pointComparison l E).hom.hom X M).symm.trans
    (absolute_iff l E X _)

end AlgebraicGeometry.ProEtale.IntegralConstantModel
