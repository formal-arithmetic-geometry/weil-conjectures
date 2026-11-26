/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.SmoothPurity.Point.PointSectionsFinitenessFiniteTorsion
import WeilConjectures.SmoothPurity.Point.PointSectionsFinitenessIntegral

/-!
# Finiteness of sections over the algebraically closed coefficient point

## Implementation details

All assertions are made for every complex representative of the derived object, not only
for bounded or K-flat ones. Sections are evaluated at the final small pro-etale object.
The scalar maps are actual constant-section maps, and rationalization is termwise scalar
extension. The section-exactness dependency makes these formulas independent of the
representative. `ULift` changes only coefficient size, leaving the original rings and their
actions intact.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- Sections of a finite-torsion constructible complex have bounded finite cohomology;
sections of an integral constructible complex are bounded, finitely generated and derived
complete; their termwise rationalization has bounded finite-dimensional cohomology. -/
theorem point_sections_finiteness (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ C : CochainComplex
        (SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology (Spec (.of D.k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
                (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))) ℤ,
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (DerivedCategory.Q.obj
            (((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex
              (.up ℤ)).obj C))) ∧
    (∀ C : CochainComplex (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ℤ,
      sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFgComplete (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
          (DerivedCategory.Q.obj
            (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)) ∧
        DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars (pointIntegralToField l E)).mapHomologicalComplex
              (.up ℤ)).obj
              (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)))) := by
  constructor
  · exact point_sections_finiteness_finiteTorsion D l _hl E n hn
  · exact point_sections_finiteness_integral D l _hl E n hn

end WeilConjectures
