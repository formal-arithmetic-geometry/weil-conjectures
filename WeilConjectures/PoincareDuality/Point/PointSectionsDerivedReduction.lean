/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionIso
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionCone
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionHomology

/-! # Point sections and derived integral reduction -/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Point sections commute naturally with derived reduction in the quotient-module
category. After forgetting quotient scalars the left side is the multiplication cone,
and its cohomology is sections of the reduced cohomology sheaf in every integer degree.
Source: Stacks Tags 093M, 06YS, 06YY, 05RT, 064L and 06Y6. -/
theorem point_sections_derived_reduction (_hl : l ≠ D.p) (n : ℕ) :
    Nonempty (pointReductionTensorSections D l E n ≅ pointReductionSectionsTensor D l E n) ∧
    (∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (C : CochainComplex (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ),
      Nonempty (DerivedCategory.Q.obj C ≅
        (pointIntegralSections l E D.k).mapDerivedCategory.obj N.obj) →
      Nonempty (((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (pointReductionQuotient l E n)).mapDerivedCategory).obj
          ((pointReductionTensorSections D l E n).obj N) ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone
          ((ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) • 𝟙 C)))) ∧
    ∀ r : ℤ, Nonempty
      (pointReductionTensorSections D l E n ⋙ DerivedCategory.homologyFunctor _ r ≅
        (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
          scalarReductionDerivedExtension l E (Spec (.of D.k)) n ⋙
            DerivedCategory.homologyFunctor _ r ⋙
              pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) := by
  refine ⟨point_sections_derived_reduction_iso D l E _hl n, ?_,
    point_sections_derived_reduction_homology D l E _hl n⟩
  intro N C hC
  obtain ⟨e⟩ := hC
  obtain ⟨m⟩ := point_sections_derived_reduction_module_cone D l E _hl n C
  let f := pointReductionModuleTensor l E n
  let q := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (pointReductionQuotient l E n)).mapDerivedCategory
  exact ⟨(q.mapIso (f.mapIso e)).symm ≪≫ m⟩

end WeilConjectures
