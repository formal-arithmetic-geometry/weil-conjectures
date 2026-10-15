/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Integral derived reduction

Source: Bhatt--Scholze, Section 6.5, Definition 6.5.1 and Lemma 6.5.4;
Stacks Project, Tags 06YS and 06YY (blueprint: def-weil-integral-derived-reduction).

The natural-number index n denotes the positive exponent n+1. The functor is chosen
from the universal derived-change-of-rings pair, not from an arbitrary existence
statement: the universal property determines it up to unique compatible isomorphism.
-/

@[expose] public section

universe d t u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ)

/-- Standard localization for completed coefficient module sheaves.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable instance integralReductionSourceHasDerivedCategory :
    HasDerivedCategory (completedIntegralModuleSheaves l E Y D hl) :=
  HasDerivedCategory.standard _

/-- Standard localization for finite quotient coefficient module sheaves.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable instance integralReductionTargetHasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)) :=
  HasDerivedCategory.standard _

/-- The small pro-etale site fits in the ambient coefficient universe.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable instance integralReductionSiteEssentiallySmall :
    EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
  essentiallySmallSelf _

set_option linter.defProp false in
/-- The recorded derived-change-of-rings theorem applied to the actual limit projection.
It includes the fixed sectionwise tensor action, its derived universal property,
exactness, and its counit isomorphism on every K-flat complex.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralReductionExistence :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheaf l E Y D hl)
    (O' := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjection l E Y D hl n)

/-- Ordinary change of rings along the coefficient projection, with objects and morphisms
fixed by the sectionwise tensor product and sheafification.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralReductionChangeOfRings :
    completedIntegralModuleSheaves l E Y D hl ⥤
      SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) :=
  (integralReductionExistence l E Y D hl n).choose

/-- Additivity of the chosen ordinary tensor functor, supplied by its defining witness.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable instance integralReductionChangeOfRingsAdditive :
    (integralReductionChangeOfRings l E Y D hl n).Additive :=
  (integralReductionExistence l E Y D hl n).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The full derived pair supplied by the general change-of-rings theorem.
Its universal property, exactness and K-flat computation fix the construction.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralReductionDerivedExistence :
    ∃ (LF : completedIntegralDerivedCategory l E Y D hl ⥤
        DerivedCategory
          (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (completedIntegralModuleSheaves l E Y D hl)
            (ComplexShape.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients
            (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
            (R := completedIntegralCommRingSheaf l E Y D hl) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
  (integralReductionExistence l E Y D hl n).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived reduction modulo the (n+1)-st power of the chosen uniformizer, the exact
left derived functor of change of rings along the completed coefficient projection.
Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.4; Stacks, Tag 06YY
(blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralDerivedReduction :
    completedIntegralDerivedCategory l E Y D hl ⥤
      DerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)) :=
  (integralReductionDerivedExistence l E Y D hl n).choose

/-- The universal comparison to termwise change of rings on homotopy complexes.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralDerivedReductionCounit :
    DerivedCategory.Qh ⋙ integralDerivedReduction l E Y D hl n ⟶
      (integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (integralReductionDerivedExistence l E Y D hl n).choose_spec.choose

/-- The universal left-derived-functor structure; it determines the functor uniquely
up to the unique isomorphism respecting this counit.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable instance integralDerivedReductionUniversal :
    (integralDerivedReduction l E Y D hl n).IsLeftDerivedFunctor
      (integralDerivedReductionCounit l E Y D hl n)
      (HomotopyCategory.quasiIso (completedIntegralModuleSheaves l E Y D hl)
        (ComplexShape.up ℤ)) :=
  (integralReductionDerivedExistence l E Y D hl n).choose_spec.choose_spec.1

/-- The completed coefficient projection is surjective as a morphism of sheaves.
Source: Bhatt--Scholze, Section 6.5, setup before Definition 6.5.1
(blueprint: def-weil-integral-derived-reduction).
Proof: a section of the constant quotient sheaf is locally represented by an element
of the quotient ring. Lift that element to the valuation ring using the quotient
surjection. Its reductions at every positive exponent give compatible constant
sections, hence a section of the inverse limit. The projection of this section is
the original quotient section on the chosen cover. This is local surjectivity. -/
theorem integralDerivedReductionProjection_locallySurjective :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCoefficientProjection l E Y D hl n).hom := by
  sorry

/-- The derived reduction is exact: it admits a shift comparison making it a
triangulated functor. Source: Stacks, Tag 06YY
(blueprint: def-weil-integral-derived-reduction).
Proof: unfold the chosen derived functor and use the exactness conjunct of
integralReductionDerivedExistence, which is the recorded derived-change-of-rings
theorem applied to the completed coefficient projection. Its source and target
are the same module categories, with commutativity retained in their ring data. -/
theorem integralDerivedReduction_exact :
    ∃ (_ : (integralDerivedReduction l E Y D hl n).CommShift ℤ),
      (integralDerivedReduction l E Y D hl n).IsTriangulated := by
  sorry

/-- The universal counit computes reduction on every K-flat complex.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction).
Proof: the last conjunct of the defining derived-change-of-rings witness says
that its counit is an isomorphism at the homotopy image of every K-flat complex.
The named reduction and its counit are exactly that witness's two projections;
the completed commutative ring sheaf has the same underlying ring sheaf.
Substituting the given P and its K-flatness gives this assertion. -/
theorem integralDerivedReduction_counit_isIso
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) P) :
    IsIso ((integralDerivedReductionCounit l E Y D hl n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  sorry

/-- The canonical computation on a K-flat representative is the counit isomorphism.
For a resolution P → G, precompose this with the inverse of the image of P → G.
Comparisons between resolutions are composites through this same derived object,
so are canonical and compatible with a third resolution.
Source: Bhatt--Scholze, Section 6.5; Stacks, Tag 06YY
(blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralDerivedReductionKFlatIso
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) P) :
    (integralDerivedReduction l E Y D hl n).obj
        ((DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≅
      (DerivedCategory.Qh).obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
  letI : IsIso ((integralDerivedReductionCounit l E Y D hl n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
    integralDerivedReduction_counit_isIso l E Y D hl n P hP
  asIso ((integralDerivedReductionCounit l E Y D hl n).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))

/-- Computation by any K-flat resolution: invert the image of the augmentation and
then use the counit on its K-flat source. This is the canonical resolution comparison.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralDerivedReductionResolutionIso
    {P G : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (s : P ⟶ G)
    (hs : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) s) :
    (integralDerivedReduction l E Y D hl n).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G)) ≅
      DerivedCategory.Qh.obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
  letI : QuasiIso s := hs.1
  letI : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) s).2 inferInstance
  (asIso ((integralDerivedReduction l E Y D hl n).map
    (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)))).symm ≪≫
      integralDerivedReductionKFlatIso l E Y D hl n P hs.2

end WeilConjectures
