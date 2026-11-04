/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedTensorSquare

/-!
# The condensed realization is compatible with the pullback–tensor comparisons

For a morphism `g : Z ⟶ Y` of `k₀`-schemes, the derived condensed realization `N` carries the
native pullback–tensor comparison `g^*(A ⊗ B) ≅ g^*A ⊗ g^*B`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTensor`) to the comparison
`Lḡ^*(K ⊗ᴸ L) ⟶ Lḡ^*K ⊗ᴸ Lḡ^*L` of condensed `ℚ̲̄_ℓ`-modules on the geometric fibres
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`), up to the tensor
comparisons `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor` and the pullback
comparison `AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`:
this is `CategoryTheory.Adjunction.ComparisonCompatible`, the hypothesis of
`CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The native derived tensor product of pro-étale Weil complexes, curried. -/
noncomputable abbrev nativeCurriedTensor (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :=
  Functor.curry.obj (nativeDerivedTensor k₀ l X)

/-- The condensed realization commutes with the derived tensor products, in curried form. -/
noncomputable abbrev condensedRealizationCurriedTensor (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :=
  Functor.curryCompIsoOfIso' (condensedRealizationTensor k₀ l X)

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The native pullback–tensor comparison `g^*(A ⊗ B) ⟶ g^*A ⊗ g^*B`, in curried form. -/
noncomputable abbrev nativeCurriedPullTensor :=
  (Functor.curryCompIsoOfIso (nativePullTensor k₀ l g)).hom

/-- **Compatibility of the condensed realization with the pullback–tensor comparisons.** -/
theorem comparisonCompatible_derivedCondensedRealization :
    Adjunction.ComparisonCompatible (derivedCondensedRealizationUpperStarIso k₀ l g)
      (nativeCurriedPullTensor k₀ l g)
      (ProEtale.CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (condensedRealizationCurriedTensor k₀ l Z) (condensedRealizationCurriedTensor k₀ l Y) := by
  let R := ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  let b := Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g)
  let θ := R.leftDerivedFunctorIsoMapDerivedCategory
  have he : (Functor.mapDerivedCategorySquareIso
      (condensedRealizationUpperStarIso k₀ l g).symm).hom = b.inv := by
    simp [b, Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm]
  intro M N
  have h := condensedRealizationTensor_pull_square k₀ l g M N
  dsimp only at h
  rw [he] at h
  have hh : (derivedCondensedRealization k₀ l Z).map
        ((nativePullTensor k₀ l g).hom.app (M, N)) ≫
      (condensedRealizationTensor k₀ l Z).hom.app
        ((nativeOpenPull k₀ l g).obj M, (nativeOpenPull k₀ l g).obj N) =
    b.inv.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      R.mapDerivedCategory.map ((condensedRealizationTensor k₀ l Y).hom.app (M, N)) ≫
      (R.mapDerivedCategoryTensorComparison.app
        ((derivedCondensedRealization k₀ l Y).obj M)).app
          ((derivedCondensedRealization k₀ l Y).obj N) ≫
      (b.hom.app M ⊗ₘ b.hom.app N) := by
    apply (cancel_mono (b.inv.app M ⊗ₘ b.inv.app N)).1
    simpa only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      Iso.hom_inv_id_app, MonoidalCategory.id_tensorHom_id, Category.comp_id] using h
  rw [Functor.mapDerivedCategoryTensorComparison_app_app] at hh
  have hn := θ.inv.naturality ((condensedRealizationTensor k₀ l Y).hom.app (M, N))
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc] at hh
  rw [reassoc_of% hn] at hh
  simp only [MonoidalCategory.tensorHom_comp_tensorHom] at hh
  change (derivedCondensedRealization k₀ l Z).map
        ((nativePullTensor k₀ l g).hom.app (M, N)) ≫
      (condensedRealizationTensor k₀ l Z).hom.app
        ((nativeOpenPull k₀ l g).obj M, (nativeOpenPull k₀ l g).obj N) = _
  rw [ProEtale.CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
  simpa only [derivedCondensedRealizationUpperStarIso, Functor.leftDerivedFunctorSquareIso,
    Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
    MonoidalCategory.tensorHom_def] using hh

end AlgebraicGeometry.ProEtaleWeilSheaf
