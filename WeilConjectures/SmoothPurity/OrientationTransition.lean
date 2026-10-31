/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SmoothPurity.OrientationTransitionEtale
public import WeilConjectures.SmoothPurity.OrientationTransitionShift

/-!
# The canonical finite orientations are compatible with the reductions

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ`, `T = 𝒪_{E,X}(d)[2d]` and
`W = Rf^! 𝒪_{E,Y}`. Modulo `ℓⁿ` the canonical finite orientation
(`ProEtale.CondensedRing.etaleReductionSmoothOrientationIso`) is a morphism
`θₙ : red_n T ⟶ red_n W` of bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes
(`ProEtale.CondensedRing.integersModPowReductionSmoothOrientation`), the étale reading being fully
faithful.

The main result is that these morphisms are compatible with the reductions
`𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹`: the reduction of `θₙ₊₂` is `θₙ₊₁`
(`ProEtale.CondensedRing.derivedExtendScalarsReduction_integersModPowReductionSmoothOrientation`,
blueprint `det-sp-purity-coefficient-change`). Hence the family `(θₙ)` lifts to an integral
morphism `T ⟶ W` (`ProEtale.exists_derivedReduction_map_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- The **canonical finite orientation modulo `ℓⁿ`** as a morphism
`red_n(𝒪_{E,X}(d)[2d]) ⟶ red_n(Rf^! 𝒪_{E,Y})` of bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes,
whose étale reading is `finiteEtaleReadingSmoothOrientation`: the étale reading is fully
faithful. -/
noncomputable def integersModPowReductionSmoothOrientation (n : ℕ) :
    (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((shiftFunctor _ (2 * d : ℤ)).obj (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)) ⟶
      (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :=
  (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X)).preimage
    (finiteEtaleReadingSmoothOrientation ℓ E f d n)

lemma finiteEtaleReading_map_integersModPowReductionSmoothOrientation (n : ℕ) :
    (finiteEtaleReading ℓ E.1 n X).map (integersModPowReductionSmoothOrientation ℓ E f d n) =
      finiteEtaleReadingSmoothOrientation ℓ E f d n :=
  (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X)).map_preimage _

instance isIso_integersModPowReductionSmoothOrientation (n : ℕ) :
    IsIso (integersModPowReductionSmoothOrientation ℓ E f d n) :=
  have : IsIso ((finiteEtaleReading ℓ E.1 n X).map
      (integersModPowReductionSmoothOrientation ℓ E f d n)) := by
    rw [finiteEtaleReading_map_integersModPowReductionSmoothOrientation]
    infer_instance
  (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X)).isIso_of_isIso_map _

/-- A morphism `φ₀` lifts the canonical finite orientations if and only if its reductions modulo
`ℓⁿ⁺¹` are the morphisms `integersModPowReductionSmoothOrientation`. -/
lemma isIntegralSmoothOrientation_iff
    (φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :
    IsIntegralSmoothOrientation ℓ E f d φ₀ ↔ ∀ n : ℕ,
      (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 (n + 1)).map φ₀ =
        integersModPowReductionSmoothOrientation ℓ E f d (n + 1) := by
  refine forall_congr' fun n ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 (n + 1) X)).map_injective
      (h.trans (finiteEtaleReading_map_integersModPowReductionSmoothOrientation ℓ E f d
        (n + 1)).symm)
  · exact (congrArg (finiteEtaleReading ℓ E.1 (n + 1) X).map h).trans
      (finiteEtaleReading_map_integersModPowReductionSmoothOrientation ℓ E f d (n + 1))

/-- The canonical finite orientation modulo `ℓⁿ`
(`ProEtale.CondensedRing.integersModPowReductionSmoothOrientation`), read in the ambient derived
category of `𝒪_E ⧸ ℓⁿ`-module objects, as a morphism between the derived reductions
`(𝒪_E ⧸ ℓⁿ) ⊗ᴸ 𝒪_{E,X}(d)[2d] ⟶ (𝒪_E ⧸ ℓⁿ) ⊗ᴸ Rf^! 𝒪_{E,Y}`. -/
noncomputable def derivedReductionSmoothOrientation (n : ℕ) :
    (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
        ((boundedConstructible _).ι.obj
          ((shiftFunctor _ (2 * d : ℤ)).obj
            (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) ⟶
      (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
        ((boundedConstructible _).ι.obj
          ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))) :=
  derivedReductionMap ℓ E.1 n X.left (integersModPowReductionSmoothOrientation ℓ E f d n)

set_option maxHeartbeats 1600000 in
-- the kernel compares the étale reading of the reductions at two levels, through heavy terms
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The canonical finite orientations are compatible with the reduction of coefficients, on the
étale site**: through the isomorphisms `β : Ψ(red_{n+2} -) ≅ red_{n+1} -`
(`etaleReductionExtendScalarsIsoApp`), the derived extension of scalars `Ψ` along
`𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹` of the canonical finite orientation modulo `ℓⁿ⁺²` is the canonical
finite orientation modulo `ℓⁿ⁺¹`. -/
theorem map_finiteEtaleReadingSmoothOrientation_comp (n : ℕ) :
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
        (finiteEtaleReadingSmoothOrientation ℓ E f d (n + 1 + 1)) ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom =
    (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom ≫
      finiteEtaleReadingSmoothOrientation ℓ E f d (n + 1) := by
  have h1 := map_etaleReductionSmoothOrientationIso_hom_comp ℓ E f d n
  have h := map_reductionShift_comp_etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X
    (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) (2 * d : ℤ)
  simp only [finiteEtaleReadingSmoothOrientation, Functor.map_comp, Category.assoc]
  -- rewrite at explicit positions: a goal-wide `rw` tries to unify the pattern with every
  -- composite and unfolds the heavy definitions
  conv_lhs => rhs; rhs; rw [h1]
  conv_lhs => rw [← Functor.map_comp_assoc]
  exact (Eq.trans (by with_reducible_and_instances rfl)
    (((reassoc_of% h) (etaleReductionSmoothOrientationIso ℓ E f d (n + 1)).hom).trans
      (by with_reducible_and_instances rfl)))

set_option maxHeartbeats 1600000 in
-- the kernel compares the étale reading of the reductions at two levels, through heavy terms
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The canonical finite orientations are compatible with the reductions**
`𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹`: the reduction of the canonical finite orientation modulo `ℓⁿ⁺²` is
the canonical finite orientation modulo `ℓⁿ⁺¹` (SGA 4, Exposé XVIII). -/
theorem derivedExtendScalarsReduction_derivedReductionSmoothOrientation (n : ℕ) :
    Mod.derivedExtendScalarsReduction _ (integersModPowTransition X.left ℓ E.1 (n + 1)) _
        (integersModPowReduction_comp_integersModPowTransition X.left ℓ E.1 (n + 1))
        (derivedReductionSmoothOrientation ℓ E f d (n + 1 + 1)) =
      derivedReductionSmoothOrientation ℓ E f d (n + 1) := by
  have h := derivedExtendScalarsReduction_derivedReductionMap_eq_of_comp ℓ E.1 (n + 1) X
    (integersModPowReductionSmoothOrientation ℓ E f d (n + 1 + 1))
    (integersModPowReductionSmoothOrientation ℓ E f d (n + 1)) (by
      rw [finiteEtaleReading_map_integersModPowReductionSmoothOrientation,
        finiteEtaleReading_map_integersModPowReductionSmoothOrientation]
      exact map_finiteEtaleReadingSmoothOrientation_comp ℓ E f d n)
  exact h

set_option maxHeartbeats 1600000 in
-- the kernel compares the étale reading of the reductions at two levels, through heavy terms
/-- The canonical finite orientations are compatible with the canonical transitions
`Res_{n+2} (red_{n+2} K) ⟶ Res_{n+1} (red_{n+1} K)`, the hypothesis of
`ProEtale.exists_derivedReduction_map_eq`. -/
lemma map_derivedReductionSmoothOrientation_comp_reductionTransition (n : ℕ) :
    (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1 + 1))).mapDerivedCategory.map
        (derivedReductionSmoothOrientation ℓ E f d (n + 1 + 1)) ≫
      reductionTransition E.1 (n + 1) _ =
    reductionTransition E.1 (n + 1) _ ≫
      (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1))).mapDerivedCategory.map
        (derivedReductionSmoothOrientation ℓ E f d (n + 1)) := by
  exact (Mod.map_comp_derivedReductionTransition_app _
    (integersModPowTransition X.left ℓ E.1 (n + 1)) _
    (integersModPowReduction_comp_integersModPowTransition X.left ℓ E.1 (n + 1))
    (derivedReductionSmoothOrientation ℓ E f d (n + 1 + 1))).trans
    (congrArg (fun x ↦ reductionTransition E.1 (n + 1) _ ≫
      (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1))).mapDerivedCategory.map x)
      (derivedExtendScalarsReduction_derivedReductionSmoothOrientation ℓ E f d n))

end AlgebraicGeometry.ProEtale.CondensedRing
