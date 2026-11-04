/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Single complexes, shifts and the exact derived adjunction

Auxiliary lemmas for the supported-Hom adjunction transpose
(blueprint: lem-pur-supported-hom-adjunction-transpose).

* `DerivedCategory.singleFunctors_shiftIso_inv_app_comp_shift_Q_map_mkHomFromSingle`: the
  shifted image of the cochain map `X[-a] ⟶ K` defined by a cocycle `X ⟶ Kᵃ` is the
  morphism `X[0] ⟶ K[a]` attached to the corresponding Hom-complex cocycle.
* `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction_homEquiv_symm_Q_map`:
  the derived adjunction of an adjunction with exact left adjoint transposes localized
  cochain maps into a complex of the form `R(I)` by the localized termwise transpose.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Abelian CochainComplex.HomComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The shift isomorphisms of `DerivedCategory.singleFunctors` are the images under `Q` of
those of `CochainComplex.singleFunctors`. -/
lemma singleFunctors_shiftIso_inv_app (n a a' : ℤ) (h : n + a = a') (X : C) :
    ((singleFunctors C).shiftIso n a a' h).inv.app X =
      Q.map (((CochainComplex.singleFunctors C).shiftIso n a a' h).inv.app X) ≫
        (Q.commShiftIso n).hom.app _ := by
  have := congr_app ((singleFunctorsPostcompQIso C).hom.comm n a a' h) X
  simp only [NatTrans.comp_app, singleFunctorsPostcompQIso_hom_hom,
    SingleFunctors.postcomp_shiftIso_hom_app] at this
  replace this : ((singleFunctors C).shiftIso n a a' h).hom.app X =
      (Q.commShiftIso n).inv.app _ ≫
        Q.map (((CochainComplex.singleFunctors C).shiftIso n a a' h).hom.app X) := by
    simpa using this
  rw [← cancel_epi (((singleFunctors C).shiftIso n a a' h).hom.app X), Iso.hom_inv_id_app]
  simp only [this, Category.assoc]
  simp [← Functor.map_comp_assoc]
  rfl

omit [HasDerivedCategory C] in
/-- The cochain map `X[0] ⟶ K[a]` attached to the cocycle defined by `f : X ⟶ Kᵃ` is the
shift of the cochain map `X[-a] ⟶ K` defined by `f`. -/
lemma _root_.CochainComplex.singleFunctors_shiftIso_inv_app_comp_shift_map_mkHomFromSingle
    (X : C) (K : CochainComplex C ℤ) (a : ℤ) (f : X ⟶ K.X a) (hf : f ≫ K.d a (a + 1) = 0) :
    ((CochainComplex.singleFunctors C).shiftIso a 0 a (add_zero a)).inv.app X ≫
      (HomologicalComplex.mkHomFromSingle f (fun j hj => by
        obtain rfl : a + 1 = j := hj
        exact hf))⟦a⟧' =
    Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [Cocycle.equivHomShift_symm_apply]
  simp only [CochainComplex.shiftFunctor_obj_X', Functor.comp_obj, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctor_map_f', Cocycle.homOf_f, Cocycle.rightShift_coe,
    Cocycle.fromSingleMk_coe, CochainComplex.singleFunctors,
    Cochain.rightShift_v _ a 0 (zero_add a) 0 0 (add_zero 0) a (zero_add a)]
  rw [← cancel_mono (HomologicalComplex.XIsoOfEq K (zero_add a)).hom]
  simp only [Category.assoc]
  rw [HomologicalComplex.XIsoOfEq_hom_naturality, HomologicalComplex.mkHomFromSingle_f]
  simp [HomologicalComplex.XIsoOfEq, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

/-- The shifted image in the derived category of the cochain map `X[-a] ⟶ K` defined by a
cocycle `f : X ⟶ Kᵃ` is the morphism `X[0] ⟶ K[a]` attached to the corresponding
Hom-complex cocycle. -/
lemma singleFunctors_shiftIso_inv_app_comp_shift_Q_map_mkHomFromSingle
    (X : C) (K : CochainComplex C ℤ) (a : ℤ) (f : X ⟶ K.X a) (hf : f ≫ K.d a (a + 1) = 0) :
    ((singleFunctors C).shiftIso a 0 a (add_zero a)).inv.app X ≫
      (Q.map (HomologicalComplex.mkHomFromSingle f (fun j hj => by
        obtain rfl : a + 1 = j := hj
        exact hf)))⟦a⟧' =
    (singleFunctorIsoCompQ C 0).hom.app X ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) Q := by
  rw [singleFunctors_shiftIso_inv_app, ShiftedHom.map,
    ← CochainComplex.singleFunctors_shiftIso_inv_app_comp_shift_map_mkHomFromSingle,
    Functor.map_comp]
  simp [singleFunctorIsoCompQ, Functor.commShiftIso_hom_naturality]

end DerivedCategory

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The single comparison of `F.mapDerivedCategory` in degree `n`, on cochain complexes. -/
@[reassoc]
lemma mapDerivedCategorySingleFunctor_inv_app_comp_factors_hom_app
    (n : ℤ) (X : C₁) :
    (F.mapDerivedCategorySingleFunctor n).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C₁ (.up ℤ) n).obj X) =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor n).inv.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

end Functor

namespace Adjunction

variable {C : Type*} {D : Type*} [Category* C] [Category* D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D] [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- The adjoint of a morphism killed by a further morphism is killed by its image. -/
lemma homEquiv_comp_eq_zero (adj : L ⊣ R) {X : C} {Y Z : D} (f : L.obj X ⟶ Y) (d : Y ⟶ Z)
    (h : f ≫ d = 0) : adj.homEquiv _ _ f ≫ R.map d = 0 := by
  rw [← adj.homEquiv_naturality_right, h, adj.homEquiv_unit, R.map_zero, Limits.comp_zero]

/-- The derived adjunction of an adjunction with exact left adjoint transposes the localized
cochain map `K ⟶ R(I)`, followed by the derived unit, into the localization of its termwise
transpose `L(K) ⟶ I`. -/
lemma mapDerivedCategoryRightDerivedAdjunction_homEquiv_symm_Q_map (adj : L ⊣ R)
    {K : CochainComplex C ℤ} {I : CochainComplex D ℤ}
    (ψ : K ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :
    (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm
        (DerivedCategory.Q.map ψ ≫
          (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
          R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) =
      L.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _).symm ψ) ≫
        (DerivedCategory.quotientCompQhIso D).inv.app I := by
  have hε := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj I)
  have hα := L.mapDerivedCategoryFactorsh_hom_app
    ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  erw [hε]
  rw [adj.mapHomotopyCategory_counit_app_quotient (ComplexShape.up ℤ)]
  erw [hα]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  have h1 := L.mapDerivedCategoryFactors.hom.naturality ψ
  have h2 := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)
  simp only [Functor.comp_map] at h1 h2
  have h0 : L.mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso C).inv.app
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      L.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  erw [reassoc_of% h0, Functor.map_id, Category.id_comp,
    reassoc_of% h1]
  erw [← h2]
  rfl

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- The termwise transpose of the cochain map `X[-a] ⟶ R(I)` defined by the adjoint of a
cocycle `f : L(X) ⟶ Iᵃ` is the cochain map `L(X)[-a] ⟶ I` defined by `f`. -/
lemma mapCochainComplexSingleFunctor_inv_app_comp_homEquiv_symm_mkHomFromSingle (adj : L ⊣ R)
    (X : C) (I : CochainComplex D ℤ) (a : ℤ) (f : L.obj X ⟶ I.X a)
    (hf : f ≫ I.d a (a + 1) = 0) :
    (L.mapCochainComplexSingleFunctor a).inv.app X ≫
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _).symm
        (HomologicalComplex.mkHomFromSingle (adj.homEquiv _ _ f) (fun j hj => by
          obtain rfl : a + 1 = j := hj
          exact adj.homEquiv_comp_eq_zero f _ hf) :
          (HomologicalComplex.single C (.up ℤ) a).obj X ⟶
            (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) =
    HomologicalComplex.mkHomFromSingle f (fun j hj => by
      obtain rfl : a + 1 = j := hj
      exact hf) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [Functor.mapCochainComplexSingleFunctor, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_unit]

/-- The shifted transpose, under the derived adjunction of an adjunction with exact left
adjoint, of the localized cochain map `X[-a] ⟶ R(I)` defined by the adjoint of a cocycle
`f : L(X) ⟶ Iᵃ` is the morphism `L(X)[0] ⟶ I[a]` attached to the Hom-complex cocycle `f`. -/
lemma mapDerivedCategoryRightDerivedAdjunction_shiftedTranspose (adj : L ⊣ R) (X : C)
    (I : CochainComplex D ℤ) (a : ℤ) (f : L.obj X ⟶ I.X a) (hf : f ≫ I.d a (a + 1) = 0) :
    ((DerivedCategory.singleFunctors D).shiftIso a 0 a (add_zero a)).inv.app (L.obj X) ≫
      ((L.mapDerivedCategorySingleFunctor a).inv.app X)⟦a⟧' ≫
      ((adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm
        (DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle (adj.homEquiv _ _ f)
          (fun j hj => by
            obtain rfl : a + 1 = j := hj
            exact adj.homEquiv_comp_eq_zero f _ hf) :
            (HomologicalComplex.single C (.up ℤ) a).obj X ⟶
              (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
          R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)))⟦a⟧' =
    (DerivedCategory.singleFunctorIsoCompQ D 0).hom.app (L.obj X) ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
      ((DerivedCategory.quotientCompQhIso D).inv.app I)⟦a⟧' := by
  erw [mapDerivedCategoryRightDerivedAdjunction_homEquiv_symm_Q_map]
  erw [← Functor.map_comp,
    Functor.mapDerivedCategorySingleFunctor_inv_app_comp_factors_hom_app_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc]
  erw [mapCochainComplexSingleFunctor_inv_app_comp_homEquiv_symm_mkHomFromSingle adj X I a f hf]
  rw [Functor.map_comp, ← Category.assoc,
    DerivedCategory.singleFunctors_shiftIso_inv_app_comp_shift_Q_map_mkHomFromSingle,
    Category.assoc]

end Adjunction

end CategoryTheory

namespace CategoryTheory

/-- The functor `preadditiveCoyoneda.obj X` acts on morphisms by postcomposition. -/
@[simp]
lemma preadditiveCoyoneda_obj_map_apply {C : Type*} [Category* C] [Preadditive C] (X : Cᵒᵖ)
    {Y Z : C} (g : Y ⟶ Z) (x : X.unop ⟶ Y) :
    (preadditiveCoyoneda.obj X).map g x = x ≫ g :=
  rfl

end CategoryTheory
