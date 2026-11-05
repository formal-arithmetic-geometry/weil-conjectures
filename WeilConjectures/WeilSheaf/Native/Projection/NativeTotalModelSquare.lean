/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.CochainTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModels
public import WeilConjectures.WeilSheaf.Native.Projection.TotalSquareToModel
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTotalSquareStatement
import WeilConjectures.WeilSheaf.Native.Projection.StrictProof
import WeilConjectures.Tactic.ExactModProofs

/-! # The native total square in the model-pasting interface -/

@[expose] public noncomputable section
set_option Elab.async false
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

/-- Express the native total tensor square using the model maps required for localization. -/
lemma projection_native_total_model_square
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (htotal : TotalPullTensorSquare k₀ l g P T) :
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
  ProjectionTotalModelSquare
    (L.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
    (projection_model_complex_square L V F R (condensedRealizationUpperStarIso k₀ l g).symm)
    P T WZ WU tr cZ cU (R.mapCochainComplexμIso FP FT).symm := by
  projection_strict
    dsimp only
    let L := upperStar k₀ l g
    let V := condensedRealization k₀ l Z
    let F := condensedRealization k₀ l Y
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    have ht := projection_model_square_from_tensor_square
      (L.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
      (nativePullTotalTensor k₀ l g) (condensedRealizationTotalTensorIso k₀ l Y)
      (condensedRealizationTotalTensorIso k₀ l Z)
      (projection_model_complex_square L V F R
        (condensedRealizationUpperStarIso k₀ l g).symm)
      (fun A B ↦ (R.mapCochainComplexμIso A B).symm) P T
      (by
        have h := htotal
        dsimp only [TotalPullTensorSquare, condensedRealizationPullComplexIso, Iso.symm] at h
        dsimp only [projection_model_complex_square, L, V, F, R, Iso.symm]
        with_reducible_and_instances exact_mod_proofs h)
    dsimp only [L, V, F, R] at ht
    dsimp only [NativeRestrictionDescentProof.totalFamily]
    cast_proofs ht

end AlgebraicGeometry.ProEtaleWeilSheaf
