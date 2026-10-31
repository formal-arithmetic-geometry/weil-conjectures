/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData

import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionComparison
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstruction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The zero module has the zero finite scalar presentation on the identity cover.
private theorem constantModel_of_isZero (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (spIntegralCondensed l E) X)) (hM : IsZero M) :
    IsConstantModelConstructible (spIntegralCondensed l E) X M := by
  let Λ := spIntegralCondensed l E
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  refine ⟨S, fun a ↦ ?_⟩
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun b ↦ ?_⟩
  let P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ :=
    cokernel (𝟙 (Mod.finiteFree Λ 0))
  refine ⟨P, ⟨0, 0, 𝟙 _, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
  have : pointUpperStar.{u}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : (upperStarFromPoint X).PreservesZeroMorphisms := by
    unfold upperStarFromPoint
    infer_instance
  have : ((upperStarFromPoint X).mapMod Λ).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext; simp⟩
  exact (((CondensedRing.upperStar Λ (S.immersion a)) ⋙
    CondensedRing.upperStar Λ (𝟙 X)).map_isZero hM).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_cokernel_of_epi _))

private theorem zero_isConstructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible (spIntegralCondensed l E) X
      (0 : Integral l E X) := by
  have hz := isZero_zero (Integral l E X)
  refine ⟨?_, fun n ↦ constantModel_of_isZero l E X _
    ((DerivedCategory.homologyFunctor _ n).map_isZero hz)⟩
  apply (DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).mp
  exact ⟨0, 0,
    (DerivedCategory.isGE_iff _ _).2 (fun q _ ↦ Functor.map_isZero _ hz),
    (DerivedCategory.isLE_iff _ _).2 (fun q _ ↦ Functor.map_isZero _ hz)⟩

private theorem zero_input_has_no_unordered_image_bound (s : Presentation l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (hM : IsZero M) (d : ℕ) :
    ¬ (∀ a b : ℤ, DerivedCategory.torAmplitudeIn _ a b M → ∀ n : ℕ,
      Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
        (imageLevel l E s c M n) a (b + 2 * d)) := by
  intro h
  have ht : DerivedCategory.torAmplitudeIn _ (2 * (d : ℤ) + 1) 0 M := by
    intro N
    let F := (curriedTensor (Integral l E X)).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj N)
    have hz := F.map_isZero hM
    exact ⟨(DerivedCategory.isGE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ hz,
      (DerivedCategory.isLE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ hz⟩
  have hn := (h _ _ ht 0).1
  omega

-- This is a counterexample inside the theorem's actual constructible input domain.
private theorem exists_constructible_interval_counterexample (s : Presentation l E)
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f : X ⟶ Y} (c : Compactification f) (d : ℕ) :
    ∃ M : Constructible l E X,
      ¬ (∀ a b : ℤ, DerivedCategory.torAmplitudeIn _ a b M.obj → ∀ n : ℕ,
        Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
          (imageLevel l E s c M.obj n) a (b + 2 * d)) := by
  exact ⟨⟨0, zero_isConstructible l E X⟩,
    zero_input_has_no_unordered_image_bound l E s c 0 (isZero_zero _) d⟩


/-- Normalized compact-support towers, their Tor bounds, and canonical integral reconstruction.
Source: blueprint latest direct-image.proof.md paragraphs (1) and (2).
Proof: reduce M using the normalized reduction theorem. Tower shriek levels and the uniform
bound theorem give finite constructibility and widen each Tor interval by 2d. Each transition
is the finite coefficient direct-image comparison composed with direct image of the input
transition, hence invertible. Complete compactification/limit realization commutes the two
separately derived factors with the scalar-restricted strict inverse limit: the proper factor
is a right adjoint and quasi-compact open extension is exact and preserves products. The
input is complete by the integral-model criterion. Tower reconstruction gives integral
constructibility of the limit. The normalized equivalence identifies its reduction with
the original normalized strict tower. The actual ordinary and derived adjunction
normalizations identify this isomorphism with the constructed proper/open mate, rather than
only its evaluations. Its inverse limit after the completion unit is reconstruction, hence
invertible. Transport constructibility across that isomorphism. The empty-source image and
the zero input are zero, so the assertions hold also in these cases for ordered Tor intervals.
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
-- The ordered-interval hypothesis is essential: the private counterexample above
-- disproves the former clause without a ≤ b, already on the constructible zero input.
theorem image_reconstruction (s : Presentation l E)
    (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q)
    (L : ∀ T : Scheme.{u}, Limit l E s T) :
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    ∀ c : Compactification f,
      Nonempty (CanonicalTowerComparison l E s q hq c) ∧
      ∀ M : Constructible l E X,
        spNormalizedConstructibleTorTowers l E Y (s.towers Y)
          (imageTower l E s c M.obj) ∧
        (∀ a b : ℤ, a ≤ b →
          DerivedCategory.torAmplitudeIn _ a b M.obj → ∀ n : ℕ,
          Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
            (imageLevel l E s c M.obj n) a (b + 2 * d)) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj M.obj) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((lim l E s Y (L Y)).obj
            (imageTower l E s c M.obj)) ∧
        IsIso (reconstruction l E s c (L Y) q hq M)
 := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
