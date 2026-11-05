/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ModelSquareCancellation
public import WeilConjectures.WeilSheaf.Native.Projection.NativeModelNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquare
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import all WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel
import WeilConjectures.Tactic.ExactModProofs

/-! # Localization of the native pullback tensor square -/

@[expose] public noncomputable section

set_option Elab.async false

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

-- Profiling at 800000 heartbeats completes model pasting and cancellation;
-- reserve the cumulative budget for the final proof-irrelevant goal conversion.
set_option maxHeartbeats 1000000 in
include htotal in
/-- On K-flat representatives, the native tensor square is the localization of the
square of total complexes. -/
lemma condensedRealizationTensor_pull_square_Q_of_total
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : NativeIsKFlat k₀ l Y P) (hT : NativeIsKFlat k₀ l Y T) :
    DerivedPullTensorSquare k₀ l g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  unfold DerivedPullTensorSquare PullTensorSquareWithComparison
  simp only [Iso.symm_inv]
  let L := upperStar k₀ l g
  let V := condensedRealization k₀ l Z
  let F := condensedRealization k₀ l Y
  let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
  let LT := (L.mapHomologicalComplex (.up ℤ)).obj T
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FT := (F.mapHomologicalComplex (.up ℤ)).obj T
  let WZ := ((nativeTensorTotal k₀ l Y).obj P).obj T
  let WU := ((nativeTensorTotal k₀ l Z).obj LP).obj LT
  let cZ := (condensedRealizationTotalTensorIso k₀ l Y).app (P, T)
  let cU := (condensedRealizationTotalTensorIso k₀ l Z).app (LP, LT)
  let tr := NativeRestrictionDescentProof.totalFamily L
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y) (nativePullTotalTensor k₀ l g) P T
  let mZ := F.mapDerivedCategory.mapIso (nativeOpenTensorModel k₀ l Y P T hP hT) ≪≫
    F.mapDerivedCategoryFactors.app WZ ≪≫ DerivedCategory.Q.mapIso cZ
  have hr := V.mapDerivedCategory.congr_map
    (projection_nativePullTensor_normalization k₀ l g P T hP hT)
  simp only [Functor.map_comp] at hr
  have hLP : NativeIsKFlat k₀ l Z LP := by
    dsimp only [LP, L]
    exact_mod_proofs nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g P hP
  have hLT : NativeIsKFlat k₀ l Z LT := by
    dsimp only [LT, L]
    exact_mod_proofs nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g T hT
  have hmU := projection_condensed_model_normalization k₀ l Z LP LT hLP hLT
  obtain ⟨mU, hmU', hsquare⟩ := final_total_diagram L V F R
    (condensedRealizationUpperStarIso k₀ l g).symm
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    (Functor.uncurry.obj (curriedTensor _)) (condensedRealizationTensor k₀ l Z)
    (Functor.projection_uncurryTensorIso _)
    (nativePullTensor k₀ l g) P T WZ WU
    (nativeOpenTensorModel k₀ l Y P T hP hT)
    (by with_reducible exact nativeOpenTensorModel k₀ l Z LP LT hLP hLT)
    (by with_reducible exact tr) (by
      dsimp only [L, V, LP, LT, WZ, WU, tr] at hr ⊢
      cast_proofs hr) cZ cU
    (by
      dsimp only [V, cU, WU, LP, LT, L, derivedCondensedRealization,
        Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
        curriedTensor_obj_obj] at hmU ⊢
      simp only [Functor.projection_uncurryTensorIso_hom_app, Category.id_comp,
        MonoidalCategory.tensor_map, Functor.uncurry_obj_obj, curriedTensor_obj_obj,
        MonoidalCategory.tensor_obj, Iso.app_hom] at hmU ⊢
      dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
        curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at hmU ⊢
      dsimp only [Mod.monoidalCategoryCochainComplex, HomologicalComplex.monoidalCategory,
        Monoidal.induced, HomologicalComplex.monoidalCategoryStruct,
        HomologicalComplex.tensorObj, Functor.map₂CochainComplex,
        Functor.map₂HomologicalComplex] at hmU ⊢
      with_reducible_and_instances cast_proofs hmU)
    (R.mapCochainComplexμIso FP FT).symm
    (by
      have ht := htotal P T
      dsimp only [TotalPullTensorSquare, PullTensorSquareWithComparison,
        condensedRealizationPullComplexIso] at ht
      dsimp only [complex_square, tr, NativeRestrictionDescentProof.totalFamily,
        WZ, WU, cZ, cU, L, V, F, R, LP, LT, FP, FT]
      dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
        curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at ht ⊢
      dsimp only [Iso.app, Iso.symm, MonoidalCategory.tensor_map] at ht ⊢
      with_reducible_and_instances cast_proofs ht) mZ rfl
  simp only [Functor.projection_uncurryTensorIso_hom_app, Category.id_comp,
    MonoidalCategory.tensor_map, Functor.uncurry_obj_obj, curriedTensor_obj_obj] at hmU'
  simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
    ← MonoidalCategory.tensorHom_def] at hsquare
  have hmZ : mZ.hom = (condensedRealizationTensor k₀ l Y).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
    (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q FP FT := by
    have hh := projection_condensed_model_normalization k₀ l Y P T hP hT
    dsimp only [mZ, cZ, WZ, F, FP, FT, Iso.trans_hom, Functor.mapIso_hom]
    simp only [Iso.app_hom] at hh ⊢
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at hh ⊢
    dsimp only [Mod.monoidalCategoryCochainComplex, HomologicalComplex.monoidalCategory,
      Monoidal.induced, HomologicalComplex.monoidalCategoryStruct,
      HomologicalComplex.tensorObj, Functor.map₂CochainComplex,
      Functor.map₂HomologicalComplex] at hh ⊢
    with_reducible_and_instances cast_proofs hh
  have ho := R.projection_mapDerivedCategoryTensorComparison_total_model
    (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
    (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) FP FT
    (F.mapDerivedCategoryFactors.hom.app P) (F.mapDerivedCategoryFactors.hom.app T)
  have hright := R.mapDerivedCategory.projection_map_model_square hmZ hmU' ho
  have hfinal := projection_cancel_model_square hsquare hright
  dsimp only [L, V, F, R, nativeOpenPull, derivedCondensedRealization,
    Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at hfinal ⊢
  run_tac do IO.FS.writeFile "/tmp/K5-derived-0825-before-exact" "ready"
  with_reducible_and_instances exact hfinal
  run_tac do IO.FS.writeFile "/tmp/K5-derived-0825-proof-elaborated" "ready"

run_cmd do IO.FS.writeFile "/tmp/K5-derived-0825-Q-checked" "ready"

include htotal in
/-- The native pullback tensor square on arbitrary derived objects, extended from K-flat
representatives by naturality. -/
lemma condensedRealizationTensor_pull_square_of_total
    (M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    DerivedPullTensorSquare k₀ l g M N := by
  unfold DerivedPullTensorSquare PullTensorSquareWithComparison
  simp only [Iso.symm_inv]
  let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  let c : Functor.uncurry.obj (curriedTensor _) ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙
        Functor.uncurry.obj (curriedTensor _) :=
    NatIso.ofComponents
      (fun MN ↦ asIso ((R.mapDerivedCategoryTensorComparison.app MN.1).app MN.2))
      (fun fg ↦ by
        simpa only [asIso_hom, Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
          curriedTensor_map_app, curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] using
          R.projection_mapDerivedCategoryTensorComparison_naturality fg.1 fg.2)
  have h := Adjunction.tensorSquare_of_representatives DerivedCategory.Q.obj
    (NativeIsKFlat k₀ l Y) (native_two_sided_kflat_representatives k₀ l Y)
    (nativeOpenPull k₀ l g) (derivedCondensedRealization k₀ l Z)
    (derivedCondensedRealization k₀ l Y) R.mapDerivedCategory
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    (Functor.uncurry.obj (curriedTensor _)) (Functor.uncurry.obj (curriedTensor _))
    (nativePullTensor k₀ l g) (condensedRealizationTensor k₀ l Z)
    (condensedRealizationTensor k₀ l Y)
    (Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g).symm) c
    (fun P T hP hT ↦ by
      have hQ := condensedRealizationTensor_pull_square_Q_of_total k₀ l g htotal P T hP hT
      dsimp only [DerivedPullTensorSquare, PullTensorSquareWithComparison] at hQ
      simp only [Iso.symm_inv] at hQ
      simp only [c, NatIso.ofComponents_hom_app, asIso_hom,
        Functor.uncurry_obj_map, curriedTensor_map_app,
        curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def]
      dsimp only [R]
      exact_mod_proofs hQ) M N
  simp only [c, NatIso.ofComponents_hom_app, asIso_hom,
    Functor.uncurry_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] at h
  dsimp only [R] at h
  exact_mod_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
