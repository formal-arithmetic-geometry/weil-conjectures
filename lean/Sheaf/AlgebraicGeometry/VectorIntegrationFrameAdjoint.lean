/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Targets.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Sheaf.Paper.CoordinateCounitArrows

/-! # Frame normalization before restricting the integration adjunct to a section

Source: orientation-charts Step 4, transpose of integration normalization.
(blueprint: lem-trf-vector-integration-frame-adjoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  rightDerivedLowerShriek rightDerivedUpperShriek rightDerivedUpperShriekAdjunction
  affineLinearCompactComparison affineTraceCounit affineTraceProjection singleFunctorObjUnitIso

/-- Integration normalization transposes to the affine adjunct on every bundle frame.
Source: orientation-charts Step 4; parent finite-ring section deformation proof Step 7.
(blueprint: lem-trf-vector-integration-frame-adjoint).
Proof: let Ex be compact-support exchange for this open Cartesian frame square. It is
invertible by open base change. Normalization says that pullback of integration followed
by constant-unit pullback is Ex followed by the affine coefficient comparison, compact
comparison inverse and ordered trace counit. Cancel Ex. Naturality of the adjunction Hom
equivalences transposes this equality: the transpose of inverse Ex is the exceptional
base-change map. Naturality in the coefficient unit replaces ordinary unit pullback by
the monoidal unit comparison. These agree by the constant-single unit square; the inverse
of singleFunctorObjUnitIso is identity. The remaining transpose is exactly towerAdjoint.
The coefficient square uses the projection compositor indexed by the given square
equality; its equality-transport presentation agrees by compositor coherence.
No section is involved. The same calculation works for rank zero, empty opens and A=0. -/
theorem vectorIntegration_frameAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] (W : S.Opens)
    [IsNoetherian W.toScheme] (e : VectorBundleZeroSection.Trivialization S d M W) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    (ordinaryFinitePullback A (vectorIntegrationChart S d M W e)).map
        ((vectorBundlePurityAdjunction A S d M).homEquiv _ _
          (vectorBundleIntegration N hN A hA S hS d M)) ≫
      dualizingComplexBaseChangeMap A (vectorIntegrationChart_isPullback S d M W e) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (vectorIntegrationChart S d M W e) (VectorBundleZeroSection.π S d M)).inv.app
        (affineLinearBaseCoefficient A N hA S d) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (affineTraceProjection W.toScheme d)
        W.ι (vectorIntegrationChart S d M W e ≫ VectorBundleZeroSection.π S d M)
        (vectorIntegrationChart_isPullback S d M W e).w).hom.app
          (affineLinearBaseCoefficient A N hA S d) ≫
      (ordinaryFinitePullback A (affineTraceProjection W.toScheme d)).map
        (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS d).hom ≫
      (affineLinearCoefficientDescent A N hA t W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d).inv ≫
      CoordinateCounitArrows.towerAdjoint N hN A hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d := by sorry

end AlgebraicGeometry.Etale
