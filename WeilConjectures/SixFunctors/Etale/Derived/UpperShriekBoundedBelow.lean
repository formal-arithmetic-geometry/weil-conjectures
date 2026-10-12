/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiberDimensionBound
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FiniteCohomologicalDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# The étale exceptional inverse image preserves bounded below objects

Let `Λ` be a finite ring and `f : X ⟶ Y` a morphism admitting a compactification `(i, g)`, with
`Y` quasi-compact. Then `Rf_! = D(i_!) ⋙ Rg_*` has finite cohomological amplitude: the fibres of
the proper `g` have dimension at most some `e`
(`AlgebraicGeometry.exists_topologicalKrullDim_pullback_le`), so `Rᵠg_* = 0` for `q > 2e` by
proper base change and the cohomological dimension of the geometric fibres
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isProper`). By adjunction, the
exceptional inverse image `Rf^!` lowers the lower bound of an object by at most `2e`, hence
preserves bounded below objects (`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`).

The quasi-compactness of `Y` cannot be dropped: for `Y = ⨆ₙ Spec k` and `X = ⨆ₙ ℙⁿ_k` over a
separably closed field `k`, `Rf^! Λ` has the components `Λ[2n](n)`, so it is not bounded below.

## Main statements

- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isProper`
- `AlgebraicGeometry.Etale.exists_hasRightCohomologicalDimensionLE_lowerStar`
- `AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriek_obj`
- `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

open ZeroObject in
/-- **Higher direct images of a proper morphism with fibres of bounded dimension.** Let
`g : Z ⟶ Y` be proper, with `dim (Z ×_Y Spec K) ≤ e` for every field-valued point
`Spec K ⟶ Y`, and `Λ` a finite ring. Then `Rʳg_* F = 0` for every étale sheaf `F` of
`Λ`-modules on `Z` and every `r > 2e`.

Vanishing is tested after pullback to the geometric points `t : Spec Ω ⟶ Y`; by proper base
change `t^* Rʳg_* F ≅ Rʳh_* (F|)` for the fibre `h : Z ×_Y Spec Ω ⟶ Spec Ω`, a scheme of finite
type over the separably closed `Ω` of dimension at most `e`, whose cohomology vanishes above
`2e` (`AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`). -/
theorem isZero_higherDirectImage_of_isProper {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]
    (e : ℕ) (he : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Y),
      topologicalKrullDim (pullback g s : Scheme.{u}) ≤ e)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r : ℤ) (hr : (2 * e : ℤ) < r) :
    IsZero (Etale.higherDirectImage Λ g r F) := by
  let G := Etale.higherDirectImage Λ g r F
  suffices H : ∀ y : Y, IsZero ((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ].obj G) by
    have hz : IsZero (0 : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := isZero_zero _
    have : IsIso (hz.from_ G) := by
      refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (fun y ↦ Y.algClosurePoint y)
        (fun y ↦ ⟨y, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
        fun y ↦ ?_
      have hz' : IsZero ((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ].obj 0) :=
        Functor.map_isZero _ hz
      exact ⟨⟨hz'.to_ _, (H y).eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
    exact IsZero.of_iso hz (asIso (hz.from_ G))
  intro y
  let t := Y.algClosurePoint y
  let sq' := IsPullback.of_hasPullback g t
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq'
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  have hvan := Etale.hasUniformDirectImageVanishingLE_two_mul Λ (pullback.snd g t)
    (pullback.snd g t) (𝟙 _) (Category.comp_id _) e (he _ t)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst g t)).obj F) r hr
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  refine IsZero.of_iso hvan
    (((Etale.upperStar (ModuleCat.{u + 1} Λ) t).mapDerivedCategoryPlusHomologyFunctorIso r).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.obj K) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ r).mapIso
        (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq'.toCommSq).app K)) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ r).mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd g t)).rightDerivedFunctorPlus.mapIso
          (((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst g t)).mapDerivedCategoryPlusSingleFunctor 0).app F)))

/-- For a proper morphism `g : Z ⟶ Y` with quasi-compact target and finite coefficients, the
direct image `g_*` has finite right cohomological dimension. -/
theorem exists_hasRightCohomologicalDimensionLE_lowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [IsProper g] [CompactSpace Y] :
    ∃ N : ℕ, ((g)_*[ModuleCat.{u + 1} Λ]).HasRightCohomologicalDimensionLE N := by
  have := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨e, he⟩ := exists_topologicalKrullDim_pullback_le g
  refine ⟨2 * e, fun q F hq ↦ ?_⟩
  exact (isZero_higherDirectImage_of_isProper Λ g e he F q (by exact_mod_cast hq)).of_iso
    ((g)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm

/-- For finite coefficients and a quasi-compact target, the derived lower shriek has finite
cohomological amplitude: there is `N` such that `Rf_!` sends `D^{≤ n}` into `D^{≤ n + N}`. -/
theorem exists_isLE_rightDerivedLowerShriek_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] :
    ∃ N : ℤ, ∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
      DerivedCategory.TStructure.t.IsLE K n →
        DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) (n + N) := by
  let c := HasCompactification.compactification f
  obtain ⟨N, hN⟩ := exists_hasRightCohomologicalDimensionLE_lowerStar Λ c.g
  refine ⟨N, fun K n hK ↦ ?_⟩
  let F := (c.i)_!open[ModuleCat.{u + 1} Λ]
  have : (F.mapDerivedCategory.obj K).IsLE n := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact (F.map_isZero (((DerivedCategory.isLE_iff K n).1 hK) i hi)).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso i).app K).symm
  exact hN.isLE_rightDerivedFunctor_obj.{u + 1} _ n

/-- For torsion coefficients and a quasi-compact target `Y`, `Rf_!` is a left adjoint
(`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`) and `Rf^!` preserves bounded
below objects: `Rf_!` has finite cohomological amplitude, at most twice the fibre dimension of
the compactification (`AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriek_obj`), so if
`Rf_!` sends `D^{≤ 0}` into `D^{≤ N}` then `Rf^!` sends `D^{≥ 0}` into `D^{≥ -N}`, by
adjunction [SGA 4, Exp. XVIII, 3.1.7].

The quasi-compactness of `Y` cannot be dropped: it bounds the fibre dimension of the proper
part of the compactification. For `Y = ⨆ₙ Spec k` and `X = ⨆ₙ ℙⁿ_k` over `k` separably closed,
`Rf^! Λ` has the components `Λ[2n](n)`, so it is not bounded below. -/
instance hasBoundedBelowUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [CompactSpace Y] : HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f where
  plus_rightDerivedUpperShriek_obj K hK := by
    obtain ⟨N, hN⟩ := exists_isLE_rightDerivedLowerShriek_obj Λ f
    exact DerivedCategory.TStructure.t.plus_rightAdjoint_obj DerivedCategory.TStructure.t
      (Adjunction.ofIsLeftAdjoint _) N hN K hK

end Etale

end AlgebraicGeometry
