/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import Submission.WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
public import Submission.WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationProjection
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionMapReflect
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The canonical proper projection isomorphism and its geometric compatibility -/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

/-- The proper projection formula whose hom is the canonical projection map of
`g^* ⊣ Rg_*`. The choice of inverses does not change this hom. -/
noncomputable def rightDerivedLowerStarNativeDerivedTensorIso :
    ((objectProperty k₀ l Z).ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor).prod
          (objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.nativeDerivedTensor k₀ l Y ≅
      (objectProperty k₀ l Z).ι.prod
          ((objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.nativeOpenPull k₀ l g) ⋙
        ProEtaleWeilSheaf.nativeDerivedTensor k₀ l Z ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor := by
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
  refine NatIso.ofComponents (fun ML ↦ @asIso _ _ _ _ ((PF.app ML.1.obj).app ML.2.obj)
    (hiso ML.1 ML.2)) ?_
  rintro ⟨M, L⟩ ⟨M', L'⟩ ⟨f₁, f₂⟩
  exact Functor.naturality_curry_postcompose₂ PF (objectProperty k₀ l Z).ι
    (objectProperty k₀ l Y).ι f₁ f₂

/-- The proper projection isomorphism uses the canonical projection morphism. -/
@[simp]
lemma rightDerivedLowerStarNativeDerivedTensorIso_hom_app
    (M : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y) :
    (rightDerivedLowerStarNativeDerivedTensorIso g).hom.app (M, T) =
      (((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l g).rightAdjointProjectionMap
        (ProEtaleWeilSheaf.nativeCurriedPullTensor k₀ l g)).app M.obj).app T.obj := rfl

end AlgebraicGeometry.WeilComplex
