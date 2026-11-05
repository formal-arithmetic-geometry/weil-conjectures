/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromTotalFunctors
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareOfRepresentatives
public import WeilConjectures.WeilSheaf.Native.Projection.TotalSquareToModel
public import WeilConjectures.WeilSheaf.Native.Projection.NativeModelNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
public import WeilConjectures.WeilSheaf.Native.Projection.NativeRealizedPullNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquare
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.WeilSheaf.Native.Projection.StrictProof
import WeilConjectures.Tactic.ExactModProofs

/-! # Localization of the native pullback tensor square -/

@[expose] public noncomputable section

set_option Elab.async false
-- Keep dependent model data as lets; letToHave expands their native isomorphism types.
set_option cleanup.letToHave false

-- Use the coefficient-category instance fixed by the native tensor construction.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

attribute [local instance] projection_hasSmallColimits projection_hasTensor
  projection_nativeHasTotal projection_tensorLeftPreservesInitial
  projection_tensorRightPreservesInitial projection_hasGoodTensor12
  projection_hasGoodTensor23 projection_hasTensor4Ext

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

variable (htotal : ∀ P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ,
  TotalPullTensorSquare k₀ l g P T)

set_option maxHeartbeats 1000000 in
-- The native model interfaces previously exhausted 800000 elaboration heartbeats.
include htotal in
/-- On K-flat representatives, the native tensor square is the localization of the
square of total complexes. -/
lemma condensedRealizationTensor_pull_square_Q_of_total
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : NativeIsKFlat k₀ l Y P) (hT : NativeIsKFlat k₀ l Y T) :
    DerivedPullTensorSquare k₀ l g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  projection_strict
    unfold DerivedPullTensorSquare
    let L := upperStar k₀ l g
    let V := condensedRealization k₀ l Z
    let F := condensedRealization k₀ l Y
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
    let LT := (L.mapHomologicalComplex (.up ℤ)).obj T
    let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
    let FT := (F.mapHomologicalComplex (.up ℤ)).obj T
    have hLP : NativeIsKFlat k₀ l Z LP := by
      dsimp only [LP, L]
      exact_mod_proofs nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g P hP
    have hLT : NativeIsKFlat k₀ l Z LT := by
      dsimp only [LT, L]
      exact_mod_proofs nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g T hT
    have hr := projection_realized_nativePullTensor_normalization k₀ l L V
      (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g)
      (nativePullTotalTensor k₀ l g) (nativePullTensor k₀ l g)
      (by
        dsimp only [L]
        exact_mod_proofs projection_nativePullTensor_normalization k₀ l g)
      P T hP hT hLP hLT
    have hmU := projection_condensed_model_normalization k₀ l Z LP LT hLP hLT
    have h := projection_derived_square_of_total_functors L V F R
      (condensedRealizationUpperStarIso k₀ l g).symm
      (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      (condensedRealizationTensor k₀ l Y) (condensedRealizationTensor k₀ l Z)
      (nativePullTensor k₀ l g)
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
      (nativePullTotalTensor k₀ l g) (condensedRealizationTotalTensorIso k₀ l Y)
      (condensedRealizationTotalTensorIso k₀ l Z) P T
      (by
        dsimp only [Functor.uncurry_obj_obj]
        with_reducible exact nativeOpenTensorModel k₀ l Y P T hP hT)
      (by
        dsimp only [Functor.uncurry_obj_obj]
        with_reducible exact nativeOpenTensorModel k₀ l Z LP LT hLP hLT)
      (by
        dsimp only [L, V, LP, LT, NativeRestrictionDescentProof.totalFamily,
          Functor.uncurry_obj_obj, Functor.comp_obj, Functor.prod_obj, Iso.app] at hr ⊢
        with_reducible_and_instances exact_mod_proofs hr)
      (by
        dsimp only [V, LP, LT, L, derivedCondensedRealization,
          Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
          curriedTensor_obj_obj, MonoidalCategory.tensor_obj, Iso.app] at hmU ⊢
        dsimp only [Mod.monoidalCategoryCochainComplex, HomologicalComplex.monoidalCategory,
          Monoidal.induced, HomologicalComplex.monoidalCategoryStruct,
          HomologicalComplex.tensorObj, Functor.map₂CochainComplex,
          Functor.map₂HomologicalComplex] at hmU ⊢
        with_reducible_and_instances cast_proofs hmU)
      (fun A B ↦ (R.mapCochainComplexμIso A B).symm)
      (by
        have ht := htotal P T
        dsimp only [TotalPullTensorSquare, condensedRealizationPullComplexIso, Iso.symm] at ht
        dsimp only [projection_model_complex_square, L, V, F, R, Iso.symm]
        with_reducible_and_instances exact_mod_proofs ht)
      (by
        have hh := projection_condensed_model_normalization k₀ l Y P T hP hT
        dsimp only [F, FP, FT]
        simp only [Iso.app_hom] at hh ⊢
        dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
          curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at hh ⊢
        dsimp only [Mod.monoidalCategoryCochainComplex, HomologicalComplex.monoidalCategory,
          Monoidal.induced, HomologicalComplex.monoidalCategoryStruct,
          HomologicalComplex.tensorObj, Functor.map₂CochainComplex,
          Functor.map₂HomologicalComplex] at hh ⊢
        with_reducible_and_instances cast_proofs hh)
      (fun A B ↦ (R.mapDerivedCategoryTensorComparison.app A).app B)
      (by
        have ho := R.projection_mapDerivedCategoryTensorComparison_total_model
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) FP FT
          (F.mapDerivedCategoryFactors.hom.app P) (F.mapDerivedCategoryFactors.hom.app T)
        dsimp only [Iso.symm, FP, FT, Functor.postcompose₂, Functor.comp_obj,
          Functor.whiskeringRight_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
          Functor.comp_map, curriedTensor_obj_obj, curriedTensor_obj_map] at ho ⊢
        with_reducible_and_instances exact_mod_proofs ho)
    dsimp only [L, V, F, R, nativeOpenPull, derivedCondensedRealization] at h ⊢
    exact_mod_proofs h

include htotal in
/-- The native pullback tensor square on arbitrary derived objects, extended from K-flat
representatives by naturality. -/
lemma condensedRealizationTensor_pull_square_of_total
    (M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    DerivedPullTensorSquare k₀ l g M N := by
  exact projection_derived_square_of_representatives k₀ l g
    (condensedRealizationTensor_pull_square_Q_of_total k₀ l g htotal) M N

end AlgebraicGeometry.ProEtaleWeilSheaf
