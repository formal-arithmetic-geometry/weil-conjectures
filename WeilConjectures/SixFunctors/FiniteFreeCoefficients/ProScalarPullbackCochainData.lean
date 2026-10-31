/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import all WeilConjectures.SixFunctors.NormalizedSiteScalarTensor.NormalizedSiteScalarTensorComposition

/-! # Concrete representatives for pro-etale scalar extension and inverse image

Source: Stacks Tags 06YY and 07A4. Scalar representatives transpose the localized
ordinary scalar unit. Geometric representatives are the derived upper-star counit.
The sheaf scalar/pullback comparison is the conjugate of the objectwise
restriction/direct-image identity.
(blueprint: new-sf-pro-scalar-pullback-cochain-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The finite Verdier scalar representatives are the components of a natural
transformation, invertible on K-flat complexes.
Source: Stacks 06YY and 07A4.
Proof: use the adjoint transpose of the localized ordinary unit. Its naturality
is adjunction naturality. Scalar extension preserves acyclic K-flat complexes,
since after faithful exact restriction it is tensoring with the target ring.
Consequently the derived counit, hence its adjoint-unique representative, is
invertible on K-flat complexes.
(blueprint: new-sf-pro-scalar-pullback-cochain-data). -/
theorem pro_scalar_representative_transformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ∃ r : DerivedCategory.Q ⋙ ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ⟶
        (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology T) φ).mapHomologicalComplex
          (.up ℤ) ⋙ DerivedCategory.Q,
      (∀ K, r.app K = finiteVerdierScalarRepresentative (Scheme.ProEt.topology T) φ K) ∧
      ∀ K, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K → IsIso (r.app K) := by
  refine ⟨WeilConjectures.NormalizedSiteScalarTensor.representative
    (Scheme.ProEt.topology T) φ, ?_, ?_⟩
  · exact WeilConjectures.NormalizedSiteScalarTensor.representative_app
      (Scheme.ProEt.topology T) φ
  · exact WeilConjectures.NormalizedSiteScalarTensor.representative_iso
      (Scheme.ProEt.topology T) φ

/-- The geometric cochain representative transformation is the derived counit,
followed by the homotopy quotient comparison.
Source: Stacks 07A4 (blueprint: new-sf-pro-scalar-pullback-cochain-data). -/
def pro_geometric_representative
    (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (f : Y ⟶ X) :
    DerivedCategory.Q ⋙ Sites.proPull A f ⟶
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit ≫
    Functor.whiskerRight
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh

/-- Exact inverse image has invertible geometric representatives on every complex.
Source: Stacks 07A4.
Proof: both the exact derived counit and the homotopy quotient factors are
isomorphisms; their whiskered composite is an isomorphism componentwise.
(blueprint: new-sf-pro-scalar-pullback-cochain-data). -/
theorem pro_geometric_representative_isIso
    (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    IsIso ((pro_geometric_representative A f).app K) := by
  dsimp only [pro_geometric_representative, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- The actual ordinary scalar/pullback comparison, conjugate to the objectwise
restriction/direct-image identity.
Source: Stacks 07A4 (blueprint: new-sf-pro-scalar-pullback-cochain-data). -/
def pro_scalar_sheaf_pullback_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} B) f ≅
      ProEtale.upperStar (ModuleCat.{u + 1} A) f ⋙
        finiteVerdierOrdinaryExtension (Scheme.ProEt.topology Y) φ :=
  (conjugateIsoEquiv
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology Y) φ))
    ((finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
    (ProEtale.lowerStarCompRestrictScalarsIso φ f).symm

end WeilConjectures.FiniteFreeCoefficients
