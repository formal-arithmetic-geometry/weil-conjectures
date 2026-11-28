/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeNormalizedSelfSquareProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.IntegralKernelKunnethTransport

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
/-- The two Künneth paths for the self-square of `ℙ¹_Y → Y` agree, for arbitrary condensed
coefficients: the projection map followed by the exchange of the square equals the projection
mate followed by the opposite exchange. -/
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
      (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ (square Y)).inv))
    projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫
      R.map ((e.app M ▷ T) ≫
        projectionMateMap Λ (secondProjection Y) (A.obj M) T) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ B.obj T) =
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
      R.map ((M ◁ e'.app T) ≫ projectionMap Λ (firstProjection Y) M (B.obj T)) := by
  apply integral_kernel_kunneth_transport Λ Y M T
  exact integral_kernel_kunneth_tensor_square Λ Y

end AlgebraicGeometry.ProEtale.RationalP1
