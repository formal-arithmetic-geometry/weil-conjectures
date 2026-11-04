/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorSquare
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTotalTensor
public import WeilConjectures.Algebra.Homology.Monoidal.MapCochainComplexCoherence
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # The totalized native pullback tensor square -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The termwise pullback square in the orientation of the native tensor square. -/
abbrev condensedRealizationPullComplexIso :=
  Functor.mapHomologicalComplexCompIso (condensedRealizationUpperStarIso k₀ l g).symm
      (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (condensedRealization k₀ l Y ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))))
        (.up ℤ)).symm

@[simp]
lemma condensedRealizationPullComplexIso_hom_app_f
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (n : ℤ) :
    ((condensedRealizationPullComplexIso k₀ l g).hom.app P).f n =
      (condensedRealizationUpperStarIso k₀ l g).inv.app (P.X n) := by
  simp [condensedRealizationPullComplexIso,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f]

/-- Equality of the two total-complex tensor squares, checked on each tensor summand. -/
lemma condensedRealizationTotalTensor_pull_square
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
    let L := upperStar k₀ l g
    let V := condensedRealization k₀ l Z
    let F := condensedRealization k₀ l Y
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
    let LT := (L.mapHomologicalComplex (.up ℤ)).obj T
    let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
    let FT := (F.mapHomologicalComplex (.up ℤ)).obj T
    (V.mapHomologicalComplex (.up ℤ)).map ((nativePullTotalTensor k₀ l g).hom.app (P, T)) ≫
      (condensedRealizationTotalTensorIso k₀ l Z).hom.app (LP, LT) ≫
      ((condensedRealizationPullComplexIso k₀ l g).hom.app P ⊗ₘ
        (condensedRealizationPullComplexIso k₀ l g).hom.app T) =
    (condensedRealizationPullComplexIso k₀ l g).hom.app
        (((nativeTensorTotal k₀ l Y).obj P).obj T) ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((condensedRealizationTotalTensorIso k₀ l Y).hom.app (P, T)) ≫
      (R.mapCochainComplexμIso FP FT).inv := by
  dsimp only
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    condensedRealizationPullComplexIso_hom_app_f]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (upperStar k₀ l g ⋙ condensedRealization k₀ l Z)
    (F := (nativeTensorBifunctor k₀ l Y).flip)
  intro p q hpq
  dsimp only [Functor.comp_map]
  have hpull := (nativePullTotalTensor_summands k₀ l g) P T p q n hpq
  have hpull' := (condensedRealization k₀ l Z).congr_map hpull
  simp only [Functor.map_comp] at hpull'
  rw [← Category.assoc, ← Category.assoc, hpull']
  simp only [Category.assoc]
  rw [condensedRealizationTotalTensorIso_summand,
    CochainComplex.ιTensorObj_tensorHom_f]
  rw [condensedRealizationPullComplexIso_hom_app_f,
    condensedRealizationPullComplexIso_hom_app_f]
  rw [← Category.assoc, ← Category.assoc,
    condensedRealizationSheafTensor_pull_square]
  simp only [Category.assoc]
  have hn := (condensedRealizationUpperStarIso k₀ l g).inv.naturality
    (nativeOpenTensorInsertion k₀ l Y P T p q n hpq)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, condensedRealizationTotalTensorIso_summand,
    Functor.map_comp_assoc, Functor.map_ιTensorObj_mapCochainComplexμIso_inv_f]

end AlgebraicGeometry.ProEtaleWeilSheaf
