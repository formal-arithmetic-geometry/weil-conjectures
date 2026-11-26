/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.Integral.IntegralHomReductionComparison
/-! # Coherence of the complex reduction counit

We identify the transported reduction counit with the Hom reduction complex comparison and show
that it is natural and invertible at K-flat complexes.

## References

* [Stacks: Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe d u
open CategoryTheory CategoryTheory.Functor Opposite
namespace WeilConjectures.IntegralHom
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
private noncomputable def complexCounit :
    DerivedCategory.Q ⋙ integralDerivedReduction l E X D hl n ⟶
      (integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (integralDerivedReduction l E X D hl n) ≫
    whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (integralDerivedReductionCounit l E X D hl n) ≫
    whiskerRight ((integralReductionChangeOfRings l E X D hl n).mapHomotopyCategoryFactors
      (.up ℤ)).hom DerivedCategory.Qh ≫
    whiskerLeft ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

/-- The reduction counit equals the Hom reduction complex comparison: both presentations use
the same transported derived counit. -/
theorem reductionCounit_eq_complexComparison
    (P : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ) :
    reductionCounit l E X D hl n P = homReductionComplexComparison D l hl E X n P := by
  rfl

/-- Naturality of the transported counit on complexes. -/
theorem reductionCounit_naturality
    {P Q : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ} (f : P ⟶ Q) :
    (integralDerivedReduction l E X D hl n).map (DerivedCategory.Q.map f) ≫
        reductionCounit l E X D hl n Q =
      reductionCounit l E X D hl n P ≫ DerivedCategory.Q.map
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).map f) := by
  exact (complexCounit D l hl E X n).naturality f

/-- The transported counit is invertible at K-flat representatives. -/
theorem reductionCounit_isIso
    (P : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
    (hP : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    IsIso (reductionCounit l E X D hl n P) := by
  have := integralDerivedReduction_counit_isIso l E X D hl n P hP
  unfold reductionCounit
  infer_instance
end WeilConjectures.IntegralHom
