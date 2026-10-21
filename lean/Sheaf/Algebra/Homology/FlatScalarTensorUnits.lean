/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients

/-! # Units for the recorded derived sheaf tensor -/

@[expose] public section

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ZeroObject

namespace SheafOfModules

/-- The degree-zero ring sheaf is the unit for the recorded derived tensor.
Source: Stacks Project, Cohomology on Sites, Tag 06YU
(blueprint: lem-sfb-flat-scalar-tensor-units).
Proof: resolve the module by a flat-term K-flat complex, apply the resolving-class
comparison with the unit complex, and localize the ordinary complex unitors. -/
theorem flat_scalar_tensor_units
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v})
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasDerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (M : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    Nonempty ((siteDerivedTensorIndependentCoefficients J R).obj
      ((DerivedCategory.singleFunctor _ 0).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)),
        (DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj M) ∧
    Nonempty ((siteDerivedTensorIndependentCoefficients J R).obj
      ((DerivedCategory.singleFunctor _ 0).obj M,
        (DerivedCategory.singleFunctor _ 0).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ≅
      (DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  let A := SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let S := (CochainComplex.singleFunctor A 0).obj M
  let U := (CochainComplex.singleFunctor A 0).obj (unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  have hU : U.IsKFlatIndependentCoefficients := by
    intro Z hZ
    exact fun i ↦ (hZ i).of_iso (HomologicalComplex.rightUnitor Z).symm
  have hunit : IsFlatOnSite (J := J) (R := R) (unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := by
    have h : exactFunctor A A (MonoidalCategory.tensorRight (𝟙_ A)) :=
      (exactFunctor A A).prop_of_iso (MonoidalCategory.rightUnitorNatIso A).symm
        ⟨inferInstanceAs (PreservesFiniteLimits (𝟭 A)),
          inferInstanceAs (PreservesFiniteColimits (𝟭 A))⟩
    exact (exactFunctor A A).prop_of_iso (siteSheafTensorRightIso R _).symm h
  have hUflat (i : ℤ) : IsFlatOnSite (J := J) (R := R) (U.X i) := by
    by_cases hi : i = 0
    · subst i
      exact (exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso R _).symm
        ((flat_to_cat R _ hunit).2)
    · have hz : IsZero (U.X i) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      have hcat : ObjectProperty.flat (U.X i) := ObjectProperty.flat.prop_of_isZero hz
      exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm hcat.2
  obtain ⟨P, f, hP, hPflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) S
  have hPf (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm (hPflat i)
  let Q := DerivedCategory.Q.{w} (C := A)
  have : IsIso (Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso A f).2 hf
  let eP : Q.obj P ≅ (DerivedCategory.singleFunctor A 0).obj M :=
    asIso (Q.map f) ≪≫ ((DerivedCategory.singleFunctorIsoCompQ A 0).app M).symm
  let eU : Q.obj U ≅ (DerivedCategory.singleFunctor A 0).obj (𝟙_ A) :=
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app (𝟙_ A)).symm
  let T := siteDerivedTensorIndependentCoefficients J R
  obtain ⟨el⟩ := (KFlatTotalTensorModel.kFlat_total_tensor_model R U P hU hP hUflat hPf).2.2.2
  obtain ⟨er⟩ := (KFlatTotalTensorModel.kFlat_total_tensor_model R P U hP hU hPf hUflat).2.2.2
  constructor
  · exact ⟨(T.mapIso (eU.prod eP)).symm ≪≫ el.symm ≪≫
      Q.mapIso (HomologicalComplex.leftUnitor P) ≪≫ eP⟩
  · exact ⟨(T.mapIso (eP.prod eU)).symm ≪≫ er.symm ≪≫
      Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫ eP⟩


end SheafOfModules
