/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorSquare
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTotalSquareStatement
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

/-- Equality of the two total-complex tensor squares, checked on each tensor summand. -/
lemma condensedRealizationTotalTensor_pull_square
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
    TotalPullTensorSquare k₀ l g P T := by
  have : (upperStar k₀ l g).IsLeftAdjoint := (upperStarLowerStarAdjunction k₀ l g).isLeftAdjoint
  unfold TotalPullTensorSquare PullTensorSquareWithComparison
  simp only [Iso.symm_inv]
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
  rw [reassoc_of% hpull']
  simp only [Category.assoc]
  rw [reassoc_of% (condensedRealizationTotalTensorIso_summand k₀ l Z
      (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj P)
      (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj T) p q n hpq),
    CochainComplex.ιTensorObj_tensorHom_f]
  rw [condensedRealizationPullComplexIso_hom_app_f,
    condensedRealizationPullComplexIso_hom_app_f]
  rw [reassoc_of% (condensedRealizationSheafTensor_pull_square k₀ l g (P.X p) (T.X q))]
  simp only [Category.assoc]
  have hn := (condensedRealizationUpperStarIso k₀ l g).inv.naturality
    (nativeOpenTensorInsertion k₀ l Y P T p q n hpq)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, condensedRealizationTotalTensorIso_summand,
    Functor.map_comp_assoc, Functor.map_ιTensorObj_mapCochainComplexμIso_inv_f]

end AlgebraicGeometry.ProEtaleWeilSheaf
