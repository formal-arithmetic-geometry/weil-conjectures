/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientBasicSupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDerivedScalarAdjunctionUnit
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralCoefficientFlat
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.RationalCoefficientExtensionExact

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Derived unit and complex-counit data for the completed scalar map. -/
structure RealizationScalarFunctorCoreDerivedData
    [HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1}]
    [(ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [EssentiallySmall.{u + 1} T.ProEt]
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      rationalCoefficientSheaf l T E) where
  unit : ∀ P : CochainComplex (pbcModules.{u} T
      (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        ((pbcExtend φ).mapHomologicalComplex (.up ℤ) |>.obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P)
  computes : ∀ P : CochainComplex (pbcModules.{u} T
      (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    IsIso (pbcComplexCounit φ P)

omit [AlgebraicGeometry.IsNoetherian T] [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] in
/-- If `φ` is the inclusion of integral into rational coefficients, transported along an
identification `e` of the completed integral coefficients with the continuous integral-valued
functions, then the derived unit is the localized ordinary unit on every complex and the
derived complex counit is invertible.

Source: Stacks Tags 06YY and 0DVC, and Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-weil-pbc-realization-scalar-functor).

Proof: the section maps of `φ` are an isomorphism followed by the inclusion of continuous
integral-valued into continuous field-valued functions. That inclusion is a localization,
so `φ` is sectionwise flat and ordinary scalar extension along `φ` is exact. The unit
formula holds for every complex by K-flat resolution and naturality. Exact extension
preserves the resolving quasi-isomorphism, so the counit is invertible everywhere. -/
theorem nonempty_realizationScalarFunctorCoreDerivedData_of_normalized
    [HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1}]
    [(ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [EssentiallySmall.{u + 1} T.ProEt]
    (e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅ Scheme.integralCoefficientSheaf l T E)
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶ rationalCoefficientSheaf l T E)
    (hφ : integralRationalCoefficientNormalized l E T (e.inv ≫ φ)) :
    Nonempty (RealizationScalarFunctorCoreDerivedData l E T φ) := by
  have : PreservesFiniteLimits (pbcExtend φ) := by
    refine pbcExtend_preservesFiniteLimits_of_flat φ fun U ↦ ?_
    have h : (φ.hom.app U).hom = ((e.inv ≫ φ).hom.app U).hom.comp (e.hom.hom.app U).hom := by
      rw [← CommRingCat.hom_comp, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
        ← Category.assoc, e.hom_inv_id, Category.id_comp]
    rw [h]
    exact (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (e.hom.hom.app U))).comp
        (integralRationalCoefficient_flat l T E hφ U)
  exact ⟨⟨pbcDerivedScalarAdjunction_unit_app φ,
    pbcComplexCounit_isIso_of_preservesFiniteLimits φ⟩⟩

-- The section instances are part of the statement as given, though the proof does not use them.
set_option linter.unusedSectionVars false in
/-- The derived scalar extension construction supplies the two core identities.

Source: Stacks Tags 06YY and 0DVC, via the exact termwise extension and its
universal derived adjunction
(blueprint: lem-weil-pbc-realization-scalar-functor).

Proof: the unit formula holds for every complex by K-flat resolution and naturality
(`pbcDerivedScalarAdjunction_unit_app`). Exactness of scalar extension
(`pbcExtend_rationalCoefficient_preservesFiniteLimits`) preserves the resolving
quasi-isomorphism, so the counit is invertible on every complex. -/
theorem realization_scalar_functor_core_derived_data
    [HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1}]
    [(ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [EssentiallySmall.{u + 1} T.ProEt]
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      rationalCoefficientSheaf l T E) :
    Nonempty (RealizationScalarFunctorCoreDerivedData l E T φ) := by
  have := pbcExtend_rationalCoefficient_preservesFiniteLimits l T E φ
  exact ⟨⟨pbcDerivedScalarAdjunction_unit_app φ,
    pbcComplexCounit_isIso_of_preservesFiniteLimits φ⟩⟩

end WeilConjectures
