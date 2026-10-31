/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarData
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationB

/-! # Identification of the two actual completed pullback comparisons

Source: Bhatt--Scholze, Lemma 6.5.9(4), and the normalized quotient-cone construction.
(blueprint: lem-pod-completed-comparison-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] HasDerivedCategory.standard
  podCompletedDerivedInverseImage integralDerivedPullback

/-- The resolution-normalized exact inverse-image comparison and the actual
completion-unit comparison are the same whole derived morphism, after changing
only the completed coefficient-map presentation.
Source: BS Lemma 6.5.9(4); the quotient-cone calculation of the comparison normalization.
(blueprint: lem-pod-completed-comparison-normalization).

Proof in words: use the canonical quotient reduction calculus on Y. Its actual
unit is the quotient coaugmentation, with zero shifted coordinate. The normalized
ordinary limit reindexing takes every quotient projection to the exact inverse-image
projection and takes the zero shifted coordinate to zero. Its right-derived
resolution square identifies this equality with podLimitReindexing. The specified
pullbackTensorIntegralPullbackModel identifies the resulting strict Roos object
with integralDerivedPullback on every good representative. Consequently
podCompletedToTower on a good representative is the localization of the same
inverse-image Roos augmentation used by inverseImagePullbackComparison. The equality
of completed coefficient maps, checked on all finite projections, gives exactly
completedReindexModel at the source. Naturality of both comparison maps and good
representative isomorphisms transports this equality to every derived object.
This is an equality of the whole cone map, including its shifted coordinate;
no equality is deduced merely from finite reduction projections. -/
theorem podCompletedComparison_normalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y)) :
    podCompletedToTower l E g K =
      (completedReindexModel l E g).hom.app K ≫
        inverseImagePullbackComparisonDerived l E g hX hY K := by sorry

end WeilConjectures.AdicQbarRealization
