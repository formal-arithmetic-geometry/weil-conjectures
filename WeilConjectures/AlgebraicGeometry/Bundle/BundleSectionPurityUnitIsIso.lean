/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationMate
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Finite-ring orientations along bundle zero sections

The canonical integration mate constructs the orientation. Its affine normalization
and equality detection on affine frames give existence and uniqueness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The actual coefficient-unit purity mate is invertible, with its inverse projection
specified by the canonical projection arrow.
Source: parent orientation proof Steps 2 and 9; vector-bundle purity Steps 4--9.
(blueprint: lem-trf-bundle-section-purity-unit-isIso).

Proof: finite-coefficient projection formula makes the proper/open projection invertible;
conjugation by the two signed tensor symmetries preserves invertibility. Choose its
canonical inverse isomorphism, whose inverse is exactly that projection map. The
existing vectorIntegrationMate_isIso applies at the coefficient unit. Precomposition
by the inverse pullback-unit/tensor-unitor isomorphism preserves invertibility. -/
theorem bundleSectionPurityUnit_exists_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    ∃ p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M),
      p.inv = vectorBundlePurityProjectionMap A N hA S d M (ordinaryFiniteUnit A S) ∧
      IsIso (bundleSectionPurityUnitMap N hN A hA S hS d M p) := by
  have hp : IsIso (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M)
      (ordinaryFiniteUnit A S) (vectorIntegrationCoefficient A N hA S d M)) := by
    have := isIso_projectionMap_of_finite A (VectorBundleZeroSection.π S d M)
    have hcomponent : IsIso (((projectionMap (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d M)).app
          (vectorIntegrationCoefficient A N hA S d M)).app (ordinaryFiniteUnit A S)) :=
      inferInstance
    unfold compactProjectionMapCoeffFirst
    refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' hcomponent ?_)
    · exact (((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).app
        (ordinaryFiniteUnit A S)).app (vectorIntegrationSource A N hA S d M)).isIso_hom
    · exact Functor.map_isIso _
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.scheme S d M)).app
            (vectorIntegrationCoefficient A N hA S d M)).app
              ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d M)).obj
                (ordinaryFiniteUnit A S))).hom
  have hq : IsIso (vectorBundlePurityProjectionMap A N hA S d M
      (ordinaryFiniteUnit A S)) := hp
  refine ⟨(asIso (vectorBundlePurityProjectionMap A N hA S d M
    (ordinaryFiniteUnit A S))).symm, rfl, ?_⟩
  have hm := vectorIntegrationMate_isIso N hN A hA S hS d M (ordinaryFiniteUnit A S)
  dsimp only [bundleSectionPurityUnitMap, Iso.symm_hom, asIso_inv,
    vectorBundlePurityAdjunction, vectorBundlePurityTwistedPullback]
  exact IsIso.comp_isIso' (Iso.isIso_inv (bundleSectionPurityUnitIso N A hA S d M)) hm

end AlgebraicGeometry.Etale
