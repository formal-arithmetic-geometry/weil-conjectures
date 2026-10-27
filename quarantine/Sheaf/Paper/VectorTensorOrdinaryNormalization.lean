/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.VectorTensorSiteEquations

/-! # Ordinary normalization of coefficient-first vector integration
Source: blueprint vector-bundle purity, ordinary integration and its adjunction transpose.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- The ordinary inverse-projection integration has the prescribed normalized purity
adjunct, with the explicit signed symmetry from coefficient-first to twist-first order.
Source: blueprint sec-smooth-purity/sk-prop-an/thm-amb-vector-bundle-purity.proof.md,
first two paragraphs; normalization of def-pur-vector-purity-normalization.
(blueprint: lem-pur-vector-tensor-ordinary-normalization).

Proof: take the normalized family gamma supplied by vectorBundleNormalized. At K its
normalization says that the compact-support image of gamma followed by the Brown counit
is the inverse ordinary projection followed by the trace tensored with K and the left
unitor. Precompose with the signed symmetry to switch the input to coefficient-first
order. The coefficient-first projection is defined by precisely these two symmetries;
invert this composite. The finite-unit map in the normalization is the identity:
Etale.singleFunctorObjUnitIso_inv and the inverse-hom identity give this for its hom.
Naturality of symmetry moves the trace across it, and its unit
identity turns the left unitor into the right unitor. Since pe.inv is the actual
coefficient-first projection, this is exactly ordinaryTensorIntegrate with pe. Applying
the adjunction Hom bijection gives the displayed component identity. The same calculation
works in rank zero and over the empty base, and requires no flatness over Z/N.
-/
theorem vectorTensorOrdinaryNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S)
    (pe : (Etale.vectorBundlePurityLower A S d F).obj
        (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (Etale.vectorIntegrationSource A N hA S d F))
    (hpe : pe.inv = Etale.vectorBundlePurityProjectionMap A N hA S d F K) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
      (Etale.vectorIntegration_geometry S d F).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
      (Etale.vectorIntegration_geometry S d F).2.1
    ∃ γ : WeilConjectures.PurityFiniteSetting.VectorPurityGamma A N hA S d F,
      WeilConjectures.PurityFiniteSetting.VectorPurityGammaNormalized
        A N hN hA S hS d F γ ∧
      HEq ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ K
        (ordinaryTensorIntegrate A S K (Etale.vectorIntegrationSource A N hA S d F)
          _ pe (Etale.vectorBundleIntegration N hN A hA S hS d F)))
        ((((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.scheme S d F)).hom.app
            ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj K)).app
              (Etale.vectorIntegrationCoefficient A N hA S d F)) ≫ γ.app K) := by sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
