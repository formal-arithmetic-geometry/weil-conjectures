/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import Mathlib.CategoryTheory.Localization.Predicate

/-! # The fixed exact-derived adjunction unit commutes with shifts

The cochain comparisons are the standard identity-in-each-degree comparisons
`Functor.mapCochainComplexShiftIso`, including their zero and addition coherence.
The derived comparisons are the standard exact-functor comparisons, and the
adjunction is the localization of the specified degreewise adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB vA vB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- The degreewise unit and its specified localization commute with all integer shifts. -/
theorem mapExactDerivedCategory_unit_commShift
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {L : A ⥤ B} {P : B ⥤ A} [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (a : L ⊣ P) :
    NatTrans.CommShift (a.mapHomologicalComplex (ComplexShape.up ℤ)).unit ℤ ∧
      NatTrans.CommShift a.mapExactDerivedCategory.unit ℤ := by
  -- The canonical comparisons are identities in every degree.
  have hu : NatTrans.CommShift (a.mapHomologicalComplex (.up ℤ)).unit ℤ := by
    constructor
    intro n
    ext K i
    dsimp [Adjunction.mapHomologicalComplex]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      HomologicalComplex.id_f, CochainComplex.shiftFunctor_obj_X', Category.id_comp]
    erw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    erw [Functor.map_id, Category.comp_id, Category.comp_id]
  refine ⟨hu, ?_⟩
  let := hu
  -- Express the specified localized unit using the fixed factorization comparisons.
  have he : Functor.whiskerLeft DerivedCategory.Q a.mapExactDerivedCategory.unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (a.mapHomologicalComplex (.up ℤ)).unit DerivedCategory.Q ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ)) P.mapDerivedCategoryFactors.inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryFactors.inv P.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom := by
    ext K
    simp [mapExactDerivedCategory, Adjunction.localization_unit_app]
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q a.mapExactDerivedCategory.unit) ℤ := by
    rw [he]
    infer_instance
  -- Detect the square on localized complexes, then cancel the shift comparison.
  constructor
  intro n
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  have h := NatTrans.shift_app_comm
    (Functor.whiskerLeft DerivedCategory.Q a.mapExactDerivedCategory.unit) n K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  erw [← a.mapExactDerivedCategory.unit.naturality_assoc
    ((DerivedCategory.Q.commShiftIso n).hom.app K)] at h
  simpa only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc] using
    (cancel_epi ((𝟭 (DerivedCategory A)).map
      ((DerivedCategory.Q.commShiftIso n).hom.app K))).1 h

end CategoryTheory.Adjunction
