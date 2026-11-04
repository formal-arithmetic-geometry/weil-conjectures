/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-! # Comparison compatibility from the derived tensor square -/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- Rotate the exact-derived tensor square and transport it to the left derived functor. -/
theorem projectionComparisonCompatible_of_square
    (htensor : ∀ M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y),
      DerivedPullTensorSquare k₀ l g M N) :
    Adjunction.ComparisonCompatible (derivedCondensedRealizationUpperStarIso k₀ l g)
      (Functor.curryCompIsoOfIso (nativePullTensor k₀ l g)).hom
      (ProEtale.CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (Functor.curryCompIsoOfIso' (condensedRealizationTensor k₀ l Z))
      (Functor.curryCompIsoOfIso' (condensedRealizationTensor k₀ l Y)) := by
  let R := ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  let b := Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g)
  let θ := R.leftDerivedFunctorIsoMapDerivedCategory
  have he : (Functor.mapDerivedCategorySquareIso
      (condensedRealizationUpperStarIso k₀ l g).symm).hom = b.inv := by
    rw [Functor.mapDerivedCategorySquareIso_symm]
    rfl
  intro M N
  have h := htensor M N
  dsimp only [DerivedPullTensorSquare, PullTensorSquareWithComparison] at h
  simp only [Iso.symm_inv] at h
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
