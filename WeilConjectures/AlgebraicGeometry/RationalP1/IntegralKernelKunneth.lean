/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeNormalizedSelfSquareProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison

/-! # The coefficient-independent first kernel Kunneth comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000]
  projectionModuleAbelian
  projectionModuleHasDerived
  projectionModuleCategory
  projectionCoefficientMonObj
  projectionSheafMonoidal
  projectionModuleMonoidal
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
attribute [local instance 20001] CategoryTheory.traceSheafSymmetric
/-- The two Kunneth paths for arbitrary condensed coefficients.
Source: first projective-line triangle (blueprint: lem-integral-kernel-kunneth).
Proof: transport the canonical tensor-compatibility equation to the bundled internal
module tensor data before taking components. Express both normalized projections as
adjunction transposes of the tensorator followed by the appropriate counit. Transpose
both displayed paths through the composite adjunction for q and the first projection.
The mate-counit equations replace the exchanges by the chosen pullback square, and
its tensor compatibility identifies the transposes. Injectivity of the adjunction's
hom equivalence gives equality after conjugating between the two direct-image paths.
The conjugate is precisely firstPathComparison, with the displayed orientation. -/
theorem kernel_native_kunneth
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let B := moduleObjectDerivedPullback Λ (secondProjection Y)
    let e := nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y)
      (firstProjection Y) (secondProjection Y) (square Y)
    let e' := (mateEquiv
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y))
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y))
      (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ (square Y)).inv)).natTrans
    projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫
      R.map ((e.app M ▷ T) ≫
        projectionMateMap Λ (secondProjection Y) (A.obj M) T) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ B.obj T) =
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
      R.map ((M ◁ e'.app T) ≫ projectionMap Λ (firstProjection Y) M (B.obj T)) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
