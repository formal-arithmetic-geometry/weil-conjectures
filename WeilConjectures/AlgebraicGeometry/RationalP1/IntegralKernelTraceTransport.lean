/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.FirstSectionKernelComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeNormalizedSelfSquareProjection

/-! # Trace transport with arbitrary condensed coefficients -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] projectionModuleAbelian projectionModuleHasDerived
  projectionModuleCategory projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleMonoidal
attribute [local instance 20001] CategoryTheory.traceSheafSymmetric
attribute [local instance 30000] internalMonoidal
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.derivedUpperStarLowerStarAdjunction
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
attribute [local irreducible] projectionMap projectionMateMap tensorShiftIso twist

/-- Trace-functional transport conditional on the two Kunneth paths, with no section
insertion or diagonal class. Source: the first projective-line triangle
(blueprint: lem-integral-kernel-trace-transport).
Proof: expand the twisted second projection and apply tensorShiftIso naturality.
Use hk at the shifted line, then naturality of firstPathComparison and the first
projection in its coefficient to insert e. Postcompose with the first functional.
The scalar trace hypothesis changes this to the q functional; the normalized
projection evaluation removes its right coefficient. Cancel the invertible q,
second, exchange and first maps, and reinsert the tensor-shift isomorphisms and the
normalized counit. No integration identity is used in this intermediate step. -/
theorem kernel_first_trace_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (v : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      ((twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M))) ⟶
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)
    (hv : CounitComponentNormalized Λ Y L d
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) v)
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
    (h₁ : IsIso (projectionMap Λ (firstProjection Y) M
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
    (ht : firstTraceExchange Λ Y _ _ e ≫
      firstNativeFunctional Λ Y L d _ d.trace₁ ≫
        (singleUnitIso Λ (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
        (trace Λ Y L d ≫ (singleUnitIso Λ Y).hom) ≫ (secondTraceUnitIso Λ Y).hom)
    (hk : ∀ T : DerivedCategory (Modules Λ (ProjectiveLine Y)),
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
      R.map ((M ◁ e'.app T) ≫ projectionMap Λ (firstProjection Y) M (B.obj T))) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let N := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧
    R.map (U.map (X := A.obj M ⊗ N)
        (tensorShiftIso Λ (diagonalSurface Y) (L (diagonalSurface Y)) (A.obj M)).hom ≫
      @inv _ _ _ _ (twistProjectionMap Λ (secondProjection Y)
        (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e (A.obj M)) hp ≫
      (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map
        (by
          dsimp only [R, U, A]
          unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
          exact @inv _ _ _ _ ((condensedAmbientExchange Λ (square Y)).app M) hb)) ≫ v =
      firstTerminalFunctional Λ Y L d M N d.trace₁ h₁ := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
