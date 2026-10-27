/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.ContinuousConstructibleModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion

/-! # Transport of rational module localization

The completed presentation is compared with the continuous coefficient presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
/-- Exact derived localization and fraction descent in the completed presentation.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-module-localization-transport).

Proof: use the scalar-normalized isomorphism i to transport the completed constant
section action to continuous integral functions. Sheaf localization of this ring is
continuous rational functions, with the actual coefficient inclusion. Transport the
exact extension functor and its universal derived pair along these ring isomorphisms.
Apply rationalContinuousCoefficient_derivedLocalization to the completed ring and its
constant sections, and the canonical localization isomorphism A[1/varpi] = E. The
uniqueness of the counit-compatible derived comparison transports the cohomology
isomorphisms to the prescribed pbcDerivedExtend. Apply its fraction descent to the full
integral triangulated subcategory. Compare the resulting raw shift with the fixed
pbcScalarRationalHasShift using the identity normalization on integral objects; compare
their distinguished triangles by their common integral-image criterion. Transport the
functor through these comparisons. Its object function is unchanged. The tensor-Hom
formula gives the displayed fractions and the canonical constant-section E-linearity.
No constructibility or finite-module model assertion is used in this argument. -/
theorem rationalModuleLocalizationTransport (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (_hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E))) :
    ∃ κ : Linear E (pbcModules X (rationalCoefficientSheaf l X E)),
    letI := κ
    letI : Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
      inferInstance
    let α : pbcAdicCompletion X (pbcIntegralDatum l E) ⟶
        rationalCoefficientSheaf l X E := i.hom ≫ integralRationalCoefficientMap l E X
    (∀ (M N : pbcModules X (rationalCoefficientSheaf l X E))
      (f : M ⟶ N) (a : E) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (a • f).val.app U x =
        (letI := coefficientExtensionNormedField l E
         (show (rationalCoefficientSheaf l X E).obj.obj U from
           ContinuousMap.const _ (ULift.up.{u + 1, u} a))) • f.val.app U x) ∧
    (PreservesFiniteLimits (pbcExtend.{u} α) ∧ PreservesFiniteColimits (pbcExtend.{u} α)) ∧
    (∃ (_ : (pbcDerivedExtend.{u} α).CommShift ℤ), (pbcDerivedExtend.{u} α).IsTriangulated) ∧
    (∀ r : ℤ, Nonempty (pbcDerivedExtend.{u} α ⋙
      DerivedCategory.homologyFunctor (pbcModules X (rationalCoefficientSheaf l X E)) r ≅
      DerivedCategory.homologyFunctor
        (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) r ⋙ pbcExtend.{u} α)) ∧
    ∃ J : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
        DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)),
      ∃ (_ha : J.Additive) (_hl : J.Linear E) (hs : J.CommShift ℤ),
        letI := hs
        J.IsTriangulated ∧
        ∃ hobj : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
            J.obj ((pbcRationalization X (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj K) = (pbcDerivedExtend.{u} α).obj K.obj,
          ∀ (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
            (f : K ⟶ L) (n : ℕ),
            J.map (((pbcRationalCoefficientEquiv l E).symm
              (((pbcUniformizer l E).down.val ^ n)⁻¹)) •
                (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
              eqToHom (hobj K) ≫
                (((pbcUniformizer l E).down.val ^ n)⁻¹ •
                  (pbcDerivedExtend.{u} α).map f.hom) ≫ eqToHom (hobj L).symm := by sorry

end AlgebraicGeometry.Scheme
