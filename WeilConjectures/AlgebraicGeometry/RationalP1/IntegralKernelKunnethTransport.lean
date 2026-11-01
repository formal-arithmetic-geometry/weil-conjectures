/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeNormalizedSelfSquareProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.IntegralKernelKunnethTensorSquare
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTracePretrace
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
/-- The adjunction-mate transport from trace tensor coherence to the native kernel
identity. Source: first projective-line triangle (blueprint: lem-integral-kernel-kunneth-transport).
Proof: perform the two transpose calculation, then normalize its projection maps and
identify the conjugate direct-image comparison with `firstPathComparison`. -/
theorem integral_kernel_kunneth_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (hcompat :
      letI : MonoidalCategory (TraceD Λ Y) :=
        (traceNativeComparisonData Λ (ProjectiveLine Y ↘ Y)
          (firstProjection Y) (secondProjection Y)).monoidalC
      letI : MonoidalCategory (TraceD Λ (diagonalSurface Y)) :=
        (traceNativeComparisonData Λ (ProjectiveLine Y ↘ Y)
          (firstProjection Y) (secondProjection Y)).monoidalV
      ∀ K L : TraceD Λ Y,
      (tracePullSquare Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
          (secondProjection Y) (square Y).w).hom.app (K ⊗ L) ≫
        (tracePull Λ (firstProjection Y)).map
          ((traceNativeComparisonData Λ (ProjectiveLine Y ↘ Y)
            (firstProjection Y) (secondProjection Y)).tensorF K L) ≫
        (traceNativeComparisonData Λ (ProjectiveLine Y ↘ Y)
          (firstProjection Y) (secondProjection Y)).tensorOne
            ((tracePull Λ (ProjectiveLine Y ↘ Y)).obj K)
            ((tracePull Λ (ProjectiveLine Y ↘ Y)).obj L) =
      (tracePull Λ (secondProjection Y)).map
          ((traceNativeComparisonData Λ (ProjectiveLine Y ↘ Y)
            (firstProjection Y) (secondProjection Y)).tensorF K L) ≫
        (traceNativeComparisonData Λ (ProjectiveLine Y ↘ Y)
          (firstProjection Y) (secondProjection Y)).tensorTwo
            ((tracePull Λ (ProjectiveLine Y ↘ Y)).obj K)
            ((tracePull Λ (ProjectiveLine Y ↘ Y)).obj L) ≫
        ((tracePullSquare Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
          (secondProjection Y) (square Y).w).hom.app K ⊗ₘ
          (tracePullSquare Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
            (secondProjection Y) (square Y).w).hom.app L)) :
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
      R.map ((e.app M ▷ T) ≫ projectionMateMap Λ (secondProjection Y) (A.obj M) T) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ B.obj T) =
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
      R.map ((M ◁ e'.app T) ≫ projectionMap Λ (firstProjection Y) M (B.obj T)) := by
  have h := native_kunneth Λ Y M T
  have hn := congrArg (fun z ↦ z.app T) (native_opposite_mate_nat Λ Y)
  have he := (native_opposite_mate Λ Y T).symm.trans hn
  dsimp only at h ⊢
  rw [he] at h
  unfold secondPretraceExchangeMap at h
  unfold nativeSelfSquareExchange
  exact h

end AlgebraicGeometry.ProEtale.RationalP1
