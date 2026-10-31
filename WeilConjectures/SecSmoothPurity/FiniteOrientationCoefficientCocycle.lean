/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteGeneralRingData
import WeilConjectures.SecSmoothPurity.FiniteGeneralRingIntegrationExponent

/-! # Finite coefficient composition and normalized orientations

Source: current general-ring smooth purity, paragraph (3).
(blueprint: lem-sp-finite-orientation-coefficient-cocycle). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem bundle_exponent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (q : S.rootsOfUnitySheaf M ⟶ S.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN S q b) :
    (finiteGeneralRingLevelPower A M N hM hN S b d).hom ≫
        Etale.FiniteRingSectionDeformation.bundleSectionAdjoint N hNpos A hN S hS' d F =
      Etale.FiniteRingSectionDeformation.bundleSectionAdjoint M hMpos A hM S hS d F := by
  let P := Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)
  let U := Etale.ordinaryFinitePullback A (VectorBundleZeroSection.zero S d F)
  let e := finiteGeneralRingLevelPower A M N hM hN S b d
  have htrace := finiteGeneralRingIntegrationExponent A M N hMpos hNpos hdiv
    hM hN S hS hS' d F q b hb
  have hadj : P.map e.hom ≫
      Etale.FiniteRingSectionDeformation.bundleAdjoint N hNpos A hN S hS' d F =
    Etale.FiniteRingSectionDeformation.bundleAdjoint M hMpos A hM S hS d F := by
    unfold Etale.FiniteRingSectionDeformation.bundleAdjoint
    exact ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv_naturality_left
      (P.map e.hom) (Etale.vectorBundleIntegration N hNpos A hN S hS' d F)).symm.trans
      (congrArg ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ _) htrace)
  let c := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d F) (VectorBundleZeroSection.π S d F)
    (VectorBundleZeroSection.zero_spec S d F).1
  have hc := c.inv.naturality e.hom
  change e.hom ≫ c.inv.app _ = c.inv.app _ ≫ U.map (P.map e.hom) at hc
  change e.hom ≫ (c.inv.app _ ≫ U.map _) = c.inv.app _ ≫ U.map _
  rw [← Category.assoc, hc, Category.assoc, ← U.map_comp, hadj]
  rfl

/-- Changing the annihilating exponent preserves the direct Rees normalization.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, paragraph (3).
(blueprint: lem-sp-finite-orientation-coefficient-cocycle).

Proof: use the coefficient homomorphisms Z/M -> Z/N -> A, with N dividing M.
Evaluate the composition compatibility of exceptional coefficient comparisons at
the unit. The normalized scalar isomorphisms of the root lines identify its scalar
associator with the displayed Kummer power comparison: on a primitive root the
power map is reduction of the cyclic generator, so their maps agree on every
scalar/root generator. The direct diagonal orientation agrees with coefficient
extension by the chart calculation of the preceding paragraph of the blueprint.
Thus the coefficient-composition square carries the normalized orientation at M
to the normalized orientation at N. The Rees comparison is identified by its t=1
normalization on both sides. Scalar root comparison is invertible, so cancellation
also gives the converse implication; this does not assert that Z/N is flat over
Z/M. This argument compares coefficient mates, rather than deriving a new
integration-exponent theorem. The same coefficient-composition square applies in
dimension zero, for the zero ring, and on empty schemes.
-/
theorem finiteOrientationCoefficientCocycle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (G : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit (M : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X, ⊤)))
    (q : X.rootsOfUnitySheaf M ⟶ X.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine X M A hM ≅ Scheme.finiteEtaleTateLine X N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN X q b)
    (alpha : Etale.dualizingComplex A f ≅ Etale.FiniteSmoothPurity.line A M hM X d) :
    Etale.FiniteSmoothPurity.OrientationNormalized A M hMpos hM f d G hX alpha ↔
      Etale.FiniteSmoothPurity.OrientationNormalized A N hNpos hN f d G hX'
        (alpha ≪≫ finiteGeneralRingLevelPower A M N hM hN X b d) := by
  let := G
  have he := bundle_exponent A M N hMpos hNpos hdiv hM hN X hX hX' d
    (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) q b hb
  constructor
  · rintro ⟨κ, hκ, sq, heq⟩
    refine ⟨κ, hκ, sq, ?_⟩
    simpa only [Iso.trans_hom, Category.assoc, reassoc_of% he] using heq
  · rintro ⟨κ, hκ, sq, heq⟩
    refine ⟨κ, hκ, sq, ?_⟩
    simpa only [Iso.trans_hom, Category.assoc, reassoc_of% he] using heq

end AlgebraicGeometry.ProEtale
