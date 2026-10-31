/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSiteTensorTransposeData

/-! # Comparison square for the canonical compact-support projection maps

Source: finite-ring site tensor transport, proof steps 5--9
(blueprint: lem-pur-finite-ring-projection-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- The canonical compact-support comparison intertwines the canonical projection maps.
Source: Stacks 07A4, 0E8I, 0GL1; proof steps 5--9 of finite-ring site transport
(blueprint: lem-pur-finite-ring-projection-square).

Proof: for the proper factor transpose the projection comparison under derived
pullback/direct image. The direct-image comparison is its counit mate. Naturality
and the tensor/pullback comparison reduce both transposes to the counit tensored
with identity; cancel the comparison and its inverse. For the open factor use the
extension/restriction adjunction: after restriction both maps act identically on
pure tensors. On K-flat representatives these equalities hold on every bidegree
summand and descend to the unbounded derived category. Paste the proper and open
squares and use naturality to move the open comparison through proper direct
image. The outer edge is exactly finiteComparisonCompactSupportMap, and the
projection definitions include the same pullback-composition identification.
No projection-formula invertibility is needed for this equality. -/
theorem finiteRingProjectionSquare (B : Type) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} B))))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) Y).mapDerivedCategory.map
        (finiteRingEtalePF (ModuleCat.{u + 1} (ULift.{u + 1} B)) c M K) ≫
      finiteComparisonCompactSupportMap B c.i c.g
        (M ⊗ (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor.obj K) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).map
        (finiteRingTensorPullbackComparison
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory
          (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) Y).mapDerivedCategory
          (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) X)
          (finiteRingSitePullback (ModuleCat.{u + 1} (ULift.{u + 1} B)) f
            (unboundedDirectImagePullbackIso (ULift.{u + 1} B) f)) M K).hom =
    (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) Y
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).obj M) K).hom ≫
      (finiteComparisonCompactSupportMap B c.i c.g M ⊗ₘ
        𝟙 ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          Y).mapDerivedCategory.obj K)) ≫
      finiteRingProPF (ModuleCat.{u + 1} (ULift.{u + 1} B)) c
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory.obj M)
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          Y).mapDerivedCategory.obj K) := by sorry

end AlgebraicGeometry.ProEtale
