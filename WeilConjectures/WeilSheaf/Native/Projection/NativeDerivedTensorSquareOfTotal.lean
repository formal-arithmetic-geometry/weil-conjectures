/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.InstanceNormalization
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
set_option trace.profiler true
set_option trace.profiler.threshold 500

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

-- Profiling at 200000 heartbeats reaches a deferred model-square proof (16s);
-- reserve a larger cumulative budget for the native comparison assembly.
set_option maxHeartbeats 400000 in
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
  have hmU := (condensedRealizationTensor_hom_app_comp k₀ l Z LP LT hLP hLT).symm
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
        Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
        ← MonoidalCategory.tensorHom_def, Iso.app_hom, condensedTensorModel,
        asIso_hom, MonoidalCategory.tensor_map, Functor.uncurry_obj_obj,
        curriedTensor_obj_obj] at hmU ⊢
      dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
        curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at hmU ⊢
      simp only [Endofunctor.IsoAlgebra.projection_abelian_toPreadditive] at hmU ⊢
      with_reducible exact_mod_proofs hmU)
    (R.mapCochainComplexμIso FP FT).symm
    (by
      have ht := htotal P T
      dsimp only [TotalPullTensorSquare, PullTensorSquareWithComparison,
        condensedRealizationPullComplexIso] at ht
      dsimp only [complex_square, tr, NativeRestrictionDescentProof.totalFamily,
        WZ, WU, cZ, cU, L, V, F, R, LP, LT, FP, FT]
      simp only [Iso.symm_inv, Iso.symm_hom, Iso.app_hom,
        MonoidalCategory.tensor_map] at ht ⊢
      dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
        curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at ht ⊢
      exact_mod_proofs ht) mZ rfl
  simp only [Functor.projection_uncurryTensorIso_hom_app, Category.id_comp,
    MonoidalCategory.tensor_map, Functor.uncurry_obj_obj, curriedTensor_obj_obj] at hmU'
  simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
    ← MonoidalCategory.tensorHom_def] at hsquare
  have hmZ : mZ.hom = (condensedRealizationTensor k₀ l Y).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
    (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q FP FT := by
    have hh := (condensedRealizationTensor_hom_app_comp k₀ l Y P T hP hT).symm
    dsimp only [mZ, cZ, WZ, F, FP, FT, Iso.trans_hom, Functor.mapIso_hom]
    simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
      ← MonoidalCategory.tensorHom_def, Iso.app_hom, condensedTensorModel,
      asIso_hom] at hh ⊢
    dsimp only [derivedCondensedRealization, Functor.comp_obj, Functor.prod_obj,
      Functor.uncurry_obj_obj, curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at hh ⊢
    simp only [Endofunctor.IsoAlgebra.projection_abelian_toPreadditive] at hh ⊢
    with_reducible exact_mod_proofs hh
  have ho := R.projection_mapDerivedCategoryTensorComparison_total_model
    (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
    (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) FP FT
    (F.mapDerivedCategoryFactors.hom.app P) (F.mapDerivedCategoryFactors.hom.app T)
  have hright : R.mapDerivedCategory.map mZ.hom ≫
      R.mapDerivedCategoryFactors.hom.app (FP ⊗ FT) ≫
      DerivedCategory.Q.map (R.mapCochainComplexμIso FP FT).inv =
    R.mapDerivedCategory.map ((condensedRealizationTensor k₀ l Y).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
      (R.mapDerivedCategoryTensorComparison.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) ≫ mU.hom := by
    rw [hmZ, Functor.map_comp, Category.assoc, ← ho, hmU']
    rfl
  apply (cancel_mono mU.hom).1
  simp only [Category.assoc, hright] at hsquare
  dsimp only [L, V, F, R, nativeOpenPull, derivedCondensedRealization,
    Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at hsquare ⊢
  cast_proofs hsquare

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
