/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeNormalizedSelfSquareProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
/-- Component form of the tensor square coherence used by the Kunneth proof.
Source: Stacks 07A4 (blueprint: lem-integral-kernel-kunneth-tensor-square).
Proof: take components of the bundled `trace_square_tensor` coherence. -/
theorem integral_kernel_kunneth_tensor_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
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
            (secondProjection Y) (square Y).w).hom.app L) := by
  sorry
end AlgebraicGeometry.ProEtale.RationalP1
