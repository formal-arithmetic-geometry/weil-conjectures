/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorSquare
public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquare
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import all WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel

/-! # Localization of the native pullback tensor square -/

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
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The normalization of the native pullback tensor comparison on K-flat complexes. -/
lemma projection_nativePullTensor_normalization :
    OpenTensorRestrictionNormalization (upperStar k₀ l g)
      (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
      (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
      (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y)
      (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g)
      (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
      (fun P T ↦ (nativePullTotalTensor k₀ l g).app (P, T))
      (nativePullTensor k₀ l g) := by
  have := native_open_tensor_full_kflat_localization k₀ l Y
  exact NativeRestrictionDescentProof.restrictionDerivedOfTotal_normalization
    (upperStar k₀ l g) (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y)
    (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g)
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (nativeOpenTensorModel_naturality k₀ l Z) (nativeOpenTensorModel_naturality k₀ l Y)
    (nativePullTotalTensor k₀ l g)

/-- On K-flat representatives, the native tensor square is the localization of the
square of total complexes. -/
lemma condensedRealizationTensor_pull_square_Q
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : NativeIsKFlat k₀ l Y P) (hT : NativeIsKFlat k₀ l Y T) :
    let F := condensedRealization k₀ l Y
    let V := condensedRealization k₀ l Z
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    let e := Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g).symm
    V.mapDerivedCategory.map ((nativePullTensor k₀ l g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
      (condensedRealizationTensor k₀ l Z).hom.app
        ((nativeOpenPull k₀ l g).obj (DerivedCategory.Q.obj P),
          (nativeOpenPull k₀ l g).obj (DerivedCategory.Q.obj T)) ≫
      (e.hom.app (DerivedCategory.Q.obj P) ⊗ₘ e.hom.app (DerivedCategory.Q.obj T)) =
    e.hom.app ((nativeDerivedTensor k₀ l Y).obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
      R.mapDerivedCategory.map ((condensedRealizationTensor k₀ l Y).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
      (R.mapDerivedCategoryTensorComparison.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) := by
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
  let mZ := F.mapDerivedCategory.mapIso (nativeOpenTensorModel k₀ l Y P T hP hT) ≪≫
    F.mapDerivedCategoryFactors.app WZ ≪≫ DerivedCategory.Q.mapIso cZ
  have hr := V.mapDerivedCategory.congr_map
    (projection_nativePullTensor_normalization k₀ l g P T hP hT)
  simp only [Functor.map_comp] at hr
  have hLP := nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g P hP
  have hLT := nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g T hT
  have hmU := (condensedRealizationTensor_hom_app_comp k₀ l Z LP LT hLP hLT).symm
  obtain ⟨mU, hmU', hsquare⟩ := final_total_diagram L V F R
    (condensedRealizationUpperStarIso k₀ l g).symm
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    (MonoidalCategory.tensor _) (condensedRealizationTensor k₀ l Z) (Iso.refl _)
    (nativePullTensor k₀ l g) P T WZ WU
    (nativeOpenTensorModel k₀ l Y P T hP hT)
    (nativeOpenTensorModel k₀ l Z LP LT hLP hLT)
    ((nativePullTotalTensor k₀ l g).app (P, T)) hr cZ cU
    (by simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] using hmU)
    (R.mapCochainComplexμIso FP FT).symm
    (condensedRealizationTotalTensor_pull_square k₀ l g P T) mZ rfl
  have hmZ : mZ.hom = (condensedRealizationTensor k₀ l Y).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
    (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q FP FT :=
    (condensedRealizationTensor_hom_app_comp k₀ l Y P T hP hT).symm
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
  simpa only [Category.assoc, hright] using hsquare

/-- The native pullback tensor square on arbitrary derived objects, extended from K-flat
representatives by naturality. -/
lemma condensedRealizationTensor_pull_square
    (M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    let F := condensedRealization k₀ l Y
    let V := condensedRealization k₀ l Z
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    let e := Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g).symm
    V.mapDerivedCategory.map ((nativePullTensor k₀ l g).hom.app (M, N)) ≫
      (condensedRealizationTensor k₀ l Z).hom.app
        ((nativeOpenPull k₀ l g).obj M, (nativeOpenPull k₀ l g).obj N) ≫
      (e.hom.app M ⊗ₘ e.hom.app N) =
    e.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      R.mapDerivedCategory.map ((condensedRealizationTensor k₀ l Y).hom.app (M, N)) ≫
      (R.mapDerivedCategoryTensorComparison.app (F.mapDerivedCategory.obj M)).app
        (F.mapDerivedCategory.obj N) := by
  let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  let c : MonoidalCategory.tensor _ ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ MonoidalCategory.tensor _ :=
    Functor.uncurry.mapIso (asIso R.mapDerivedCategoryTensorComparison)
  exact Adjunction.tensorSquare_of_representatives DerivedCategory.Q.obj
    (NativeIsKFlat k₀ l Y) (native_two_sided_kflat_representatives k₀ l Y)
    (nativeOpenPull k₀ l g) (derivedCondensedRealization k₀ l Z)
    (derivedCondensedRealization k₀ l Y) R.mapDerivedCategory
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    (MonoidalCategory.tensor _) (MonoidalCategory.tensor _)
    (nativePullTensor k₀ l g) (condensedRealizationTensor k₀ l Z)
    (condensedRealizationTensor k₀ l Y)
    (Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g).symm) c
    (condensedRealizationTensor_pull_square_Q k₀ l g) M N

end AlgebraicGeometry.ProEtaleWeilSheaf
