/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.Native.Projection.NativeSheafSquareStatement
public import Submission.WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
public import Submission.WeilConjectures.WeilSheaf.Native.Projection.NativeTotalSquareStatement
public import Submission.WeilConjectures.Algebra.Homology.Monoidal.MapCochainComplexCoherence
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The totalized native pullback tensor square -/

@[expose] public noncomputable section

set_option Elab.async false

-- Use the coefficient-category instance fixed by the native tensor construction.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] projection_hasSmallColimits projection_hasTensor
  projection_nativeHasTotal projection_tensorLeftPreservesInitial
  projection_tensorRightPreservesInitial projection_hasGoodTensor12
  projection_hasGoodTensor23 projection_hasTensor4Ext

variable
  (L : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
  [L.Additive] [L.IsLeftAdjoint]
  (R : Mod (Sheaf (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
    Mod (Sheaf (Scheme.ProEt.topology (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber))
  [R.Additive] [R.Monoidal] [R.IsLeftAdjoint]
  (mu : nativeOpenSheafTensor k₀ l Y ⋙ L ≅ L.prod L ⋙ nativeOpenSheafTensor k₀ l Z)
  (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ L.mapHomologicalComplex (.up ℤ) ≅
    (L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
  (a : condensedRealization k₀ l Y ⋙ R ≅ L ⋙ condensedRealization k₀ l Z)

/-- The total tensor square with the pullback functors left abstract. -/
def ProjectionTotalTensorSquare
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) : Prop :=
  PullTensorSquareWithComparison (L.mapHomologicalComplex (.up ℤ))
    ((condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ))
    ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ))
    (R.mapHomologicalComplex (.up ℤ))
    (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
    (Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) t
    (condensedRealizationTotalTensorIso k₀ l Y) (condensedRealizationTotalTensorIso k₀ l Z)
    (Functor.mapHomologicalComplexCompIso a.symm (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (condensedRealization k₀ l Y ⋙ R)) (.up ℤ)).symm).symm
    (fun A B ↦ (R.mapCochainComplexμIso A B).inv) P T

variable
  (hmu : NativeRestrictionDescentProof.RestrictionTotalSummands L
    (nativeOpenSheafTensor k₀ l Z) (nativeOpenSheafTensor k₀ l Y)
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y) mu t)
  (hsheaf : ∀ M N, PullTensorSquare L (condensedRealization k₀ l Z)
    (condensedRealization k₀ l Y) R (nativeOpenSheafTensor k₀ l Y)
    (nativeOpenSheafTensor k₀ l Z) mu (condensedRealizationSheafTensorIso k₀ l Y)
    (condensedRealizationSheafTensorIso k₀ l Z) a M N)

set_option maxHeartbeats 600000 in
-- Profiling at 400000 heartbeats passes the sheaf square and naturality (21s);
-- reserve the cumulative budget needed to close the final summand calculation.
include hmu hsheaf in
/-- Equality of the two total-complex tensor squares, checked on each tensor summand. -/
lemma projection_totalTensorSquare_of_sheaf
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
    ProjectionTotalTensorSquare k₀ l L R t a P T := by
  unfold ProjectionTotalTensorSquare PullTensorSquareWithComparison
  simp only [Iso.symm_inv]
  ext n : 1
  have hcomp (A : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (i : ℤ) :=
    Functor.projection_complex_square_hom_app_f L (condensedRealization k₀ l Z)
      (condensedRealization k₀ l Y) R a A i
  dsimp only [Functor.ProjectionComplexSquareComponent] at hcomp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  conv_rhs => arg 1; rw [hcomp]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (L ⋙ condensedRealization k₀ l Z)
    (F := (nativeTensorBifunctor k₀ l Y).flip)
  intro p q hpq
  simp only [Functor.comp_map L (condensedRealization k₀ l Z)]
  have hpull := hmu P T p q n hpq
  have hpull' := (condensedRealization k₀ l Z).congr_map hpull
  dsimp only [nativeOpenTensorInsertion] at hpull'
  simp only [Functor.map_comp, Iso.app_hom, Functor.comp_obj,
    Functor.prod_obj, Functor.uncurry_obj_obj] at hpull'
  erw [reassoc_of% hpull']
  have hnZ := condensedRealizationTotalTensorIso_summand k₀ l Z
    ((L.mapHomologicalComplex (.up ℤ)).obj P)
    ((L.mapHomologicalComplex (.up ℤ)).obj T) p q n hpq
  dsimp only [nativeOpenTensorInsertion, Iso.app_hom] at hnZ
  conv_lhs =>
    arg 2
    erw [reassoc_of% hnZ, CochainComplex.ιTensorObj_tensorHom_f]
  conv_lhs =>
    arg 2
    arg 2
    arg 1
    erw [hcomp P p, hcomp T q]
  have hs := hsheaf (P.X p) (T.X q)
  dsimp only [PullTensorSquare] at hs
  erw [reassoc_of% hs]
  have hn := a.inv.naturality
    (nativeOpenTensorInsertion k₀ l Y P T p q n hpq)
  dsimp only [nativeOpenTensorInsertion] at hn
  simp only [Functor.comp_map L (condensedRealization k₀ l Z),
    Functor.comp_map (condensedRealization k₀ l Y) R] at hn
  conv_rhs => erw [reassoc_of% hn]
  have hnY := condensedRealizationTotalTensorIso_summand k₀ l Y P T p q n hpq
  dsimp only [nativeOpenTensorInsertion, Iso.app_hom] at hnY
  conv_rhs =>
    arg 2
    erw [← R.map_comp_assoc, hnY, R.map_comp_assoc,
      Functor.map_ιTensorObj_mapCochainComplexμIso_inv_f]
  try rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
