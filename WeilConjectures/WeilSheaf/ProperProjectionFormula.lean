/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationProjection
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapReflect
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms

/-!
# The proper projection formula for native Weil complexes

For a proper morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type,
`Rg_* A ⊗ T ≅ Rg_*(A ⊗ g^* T)`, naturally in the Weil complexes `A` on `Z` and `T` on `Y`, the
tensor product being the native derived tensor product of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor`). This is the proper case of
`fix-prop-projection-formula` ("a projection formula for the derived direct image is asserted
only in the proper case").
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

/-- **The proper projection formula for Weil complexes** (blueprint:
`fix-prop-projection-formula`, the proper case, for `Λ = ℚ̄_ℓ` with Weil structures): for a
proper morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type,
`Rg_* A ⊗ T ≅ Rg_*(A ⊗ g^* T)`, naturally in the Weil complexes `A` on `Z` and `T` on `Y`.

The isomorphism is the projection map of `g^* ⊣ Rg_*` built from the native pullback–tensor
comparison (`AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTensor`). The derived condensed
realization reflects isomorphisms and carries this projection map to the projection map of the
geometric fibres of condensed `ℚ̲̄_ℓ`-modules
(`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv_of_reflects`, with the
coherence `AlgebraicGeometry.ProEtaleWeilSheaf.comparisonCompatible_derivedCondensedRealization`
and the invertible base change map
`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_mateEquiv_derivedCondensedRealizationUpperStarIso`),
which is invertible on bounded constructible complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_projectionMap_derivedCondensedRealization`). -/
theorem nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso :
    Nonempty (((objectProperty k₀ l Z).ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor).prod
          (objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.nativeDerivedTensor k₀ l Y ≅
      (objectProperty k₀ l Z).ι.prod
          ((objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.nativeOpenPull k₀ l g) ⋙
        ProEtaleWeilSheaf.nativeDerivedTensor k₀ l Z ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor) := by
  let adj := ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l g
  let adj' := ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  let PF := adj.rightAdjointProjectionMap (ProEtaleWeilSheaf.nativeCurriedPullTensor k₀ l g)
  have : (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).ReflectsIsomorphisms :=
    Functor.reflectsIsomorphisms_mapDerivedCategory _
  have hβ := ProEtaleWeilSheaf.isIso_mateEquiv_derivedCondensedRealizationUpperStarIso k₀ l g
  have hiso (M : WeilComplex k₀ l Z) (L : WeilComplex k₀ l Y) :
      IsIso ((PF.app M.obj).app L.obj) := by
    have : IsIso ((mateEquiv adj adj'
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).hom).app M.obj) :=
      NatIso.isIso_app_of_isIso _ _
    have : IsIso ((mateEquiv adj adj'
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).hom).app
          (((ProEtaleWeilSheaf.nativeCurriedTensor k₀ l Z).obj M.obj).obj
            ((ProEtaleWeilSheaf.nativeOpenPull k₀ l g).obj L.obj))) :=
      NatIso.isIso_app_of_isIso _ _
    have : IsIso (((adj'.rightAdjointProjectionMap
        (ProEtale.CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))).app
            ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Z).obj M.obj)).app
              ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).obj L.obj)) :=
      ProEtaleWeilSheaf.isIso_projectionMap_derivedCondensedRealization k₀ l g M L
    exact Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv_of_reflects adj adj'
      (ProEtaleWeilSheaf.comparisonCompatible_derivedCondensedRealization k₀ l g) M.obj L.obj
  refine ⟨NatIso.ofComponents (fun ML ↦ @asIso _ _ _ _ ((PF.app ML.1.obj).app ML.2.obj)
    (hiso ML.1 ML.2)) ?_⟩
  rintro ⟨M, L⟩ ⟨M', L'⟩ ⟨f₁, f₂⟩
  exact Functor.naturality_curry_postcompose₂ PF (objectProperty k₀ l Z).ι
    (objectProperty k₀ l Y).ι f₁ f₂

end WeilComplex

end AlgebraicGeometry
