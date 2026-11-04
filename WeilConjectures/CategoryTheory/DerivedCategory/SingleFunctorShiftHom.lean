/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
import WeilConjectures.CategoryTheory.R.RHomDerivedRoof

/-!
# Morphisms out of shifted single complexes

Degree-`n` versions of the projective single-complex Hom computations: for a projective `P`,
`H^n(K)` is in bijection with morphisms `P[-n] ⟶ K` in the derived category. Also shift
compatibilities of single functors, and the transpose formula for the derived adjunction obtained
from an adjunction with exact left adjoint, evaluated on localized complexes.
(blueprint: lem-pur-supported-hom-adjunction-transpose)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace DerivedCategory

open Category CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

variable (C) in
lemma singleFunctorCompHomologyFunctorIso_inv_app (n : ℤ) (A : C) :
    (singleFunctorCompHomologyFunctorIso C n).inv.app A =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n A).inv ≫
        (homologyFunctorFactors C n).inv.app ((HomologicalComplex.single C (.up ℤ) n).obj A) := by
  have : (singleFunctorCompHomologyFunctorIso C n).hom.app A =
      (homologyFunctorFactors C n).hom.app ((HomologicalComplex.single C (.up ℤ) n).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) n).hom.app A := by
    simp only [singleFunctorCompHomologyFunctorIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.mapIso_hom,
      SingleFunctors.evaluation_map, singleFunctorsPostcompQIso_hom_hom, NatTrans.id_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    erw [CategoryTheory.Functor.map_id, id_comp, id_comp]
    rfl
  rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso C n).hom.app A), Iso.inv_hom_id_app,
    this]
  simp

omit [HasDerivedCategory C] in
lemma singleObjHomologySelfIso_inv_homologyMap' (n : ℤ) (P : C) {K : CochainComplex C ℤ}
    (f : (HomologicalComplex.single C (.up ℤ) n).obj P ⟶ K) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n P).inv ≫
      HomologicalComplex.homologyMap f n =
      K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ f.f n) (n + 1)
        (by simp)
        (by rw [assoc, f.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]) ≫
        K.homologyπ n := by
  have h : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n P).inv ≫
      HomologicalComplex.cyclesMap f n =
      K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ f.f n) (n + 1)
        (by simp)
        (by rw [assoc, f.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]) := by
    rw [← cancel_mono (K.iCycles n)]
    simp
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ_assoc,
    HomologicalComplex.homologyπ_naturality, reassoc_of% h]

/-- The morphism `P ⟶ Hⁿ(Q(K))` induced by a morphism of complexes `f : P[-n] ⟶ K`. -/
lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map' (n : ℤ) (P : C)
    {K : CochainComplex C ℤ} (f : (HomologicalComplex.single C (.up ℤ) n).obj P ⟶ K) :
    (singleFunctorCompHomologyFunctorIso C n).inv.app P ≫ (homologyFunctor C n).map (Q.map f) =
      K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ f.f n) (n + 1)
        (by simp)
        (by rw [assoc, f.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]) ≫
        K.homologyπ n ≫ (homologyFunctorFactors C n).inv.app K := by
  have h : (homologyFunctor C n).map (Q.map f) =
      (homologyFunctorFactors C n).hom.app _ ≫ HomologicalComplex.homologyMap f n ≫
        (homologyFunctorFactors C n).inv.app K := by
    rw [← homologyFunctorFactors_hom_naturality_assoc]
    simp
  refine (congrArg₂ (· ≫ ·) (singleFunctorCompHomologyFunctorIso_inv_app C n P) h).trans ?_
  rw [assoc, Iso.inv_hom_id_app_assoc]
  exact (reassoc_of% (singleObjHomologySelfIso_inv_homologyMap' n P f)) _

omit [HasDerivedCategory C] in
lemma nonempty_homotopy_zero_of_single' {n : ℤ} {P : C} {K : CochainComplex C ℤ}
    (f : (CochainComplex.singleFunctor C n).obj P ⟶ K) (h : P ⟶ K.X (n - 1))
    (hf : (HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ f.f n = h ≫ K.d (n - 1) n) :
    Nonempty (Homotopy f 0) := by
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨Cochain.fromSingleMk h (p := n) (by lia), ?_⟩⟩
  rw [Cochain.δ_fromSingleMk _ _ 0 n (by simp), Cochain.ofHom_zero, add_zero]
  apply (Cochain.fromSingleEquiv (X := P) (K := K) (p := n) (q := n) (n := 0) (by simp)).injective
  simpa [Cochain.fromSingleEquiv] using hf

lemma bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp_Q_obj' (n : ℤ) (P : C)
    [Projective P] (K : CochainComplex C ℤ) :
    Function.Bijective fun (φ : (singleFunctor C n).obj P ⟶ Q.obj K) ↦
      ((singleFunctorCompHomologyFunctorIso C n).inv.app P ≫ (homologyFunctor C n).map φ :
        P ⟶ (homologyFunctor C n).obj (Q.obj K)) := by
  have : CochainComplex.IsKProjective ((HomologicalComplex.single C (.up ℤ) n).obj P) :=
    inferInstanceAs ((CochainComplex.singleFunctor C n).obj P).IsKProjective
  have hK := ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk (K.toCycles (n - 1) n)
    (K.homologyπ n) (by simp)) (K.homologyIsCokernel (n - 1) n (by simp))
  refine ⟨fun φ₁ φ₂ h ↦ ?_, fun ψ ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨f, hf⟩ := exists_Q_map_eq_of_isKProjective
      ((HomologicalComplex.single C (.up ℤ) n).obj P) K (φ₁ - φ₂)
    replace h : (singleFunctorCompHomologyFunctorIso C n).inv.app P ≫
        (homologyFunctor C n).map (Q.map f) = 0 := by
      rw [hf, Functor.map_sub, Preadditive.comp_sub, sub_eq_zero]
      exact h
    rw [singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map',
      ← assoc, Preadditive.IsIso.comp_right_eq_zero] at h
    obtain ⟨g⟩ := nonempty_homotopy_zero_of_single' f (hK.liftFromProjective _ h) (by
      rw [← HomologicalComplex.toCycles_i, ← assoc, hK.liftFromProjective_comp,
        HomologicalComplex.liftCycles_i])
    rw [← hf, Q_map_eq_of_homotopy (C := C) g, Functor.map_zero]
  · obtain ⟨x, hx'⟩ : ∃ x, x ≫ K.homologyπ n = ψ ≫ (homologyFunctorFactors C n).hom.app K :=
      ⟨_, Projective.factorThru_comp _ _⟩
    let f := HomologicalComplex.mkHomFromSingle (x ≫ K.iCycles n) (fun k _ ↦ by simp)
    refine ⟨Q.map f, ?_⟩
    have hx : K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ f.f n) (n + 1)
        (by simp) (by simp [f]) = x := by
      rw [← cancel_mono (K.iCycles n), HomologicalComplex.liftCycles_i]
      simp [f]
    dsimp only
    rw [singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map', hx,
      reassoc_of% hx', Iso.hom_inv_id_app]
    exact comp_id ψ

lemma bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp' (n : ℤ) (P : C) [Projective P]
    (X : DerivedCategory C) :
    Function.Bijective fun (φ : (singleFunctor C n).obj P ⟶ X) ↦
      ((singleFunctorCompHomologyFunctorIso C n).inv.app P ≫ (homologyFunctor C n).map φ :
        P ⟶ (homologyFunctor C n).obj X) := by
  let e := Q.objObjPreimageIso X
  have : (fun (φ : (singleFunctor C n).obj P ⟶ X) ↦
      ((singleFunctorCompHomologyFunctorIso C n).inv.app P ≫ (homologyFunctor C n).map φ :
        P ⟶ (homologyFunctor C n).obj X)) =
      ((Iso.refl P).homCongr ((homologyFunctor C n).mapIso e)) ∘
        (fun (φ : (singleFunctor C n).obj P ⟶ Q.obj (Q.objPreimage X)) ↦
          ((singleFunctorCompHomologyFunctorIso C n).inv.app P ≫ (homologyFunctor C n).map φ :
            P ⟶ (homologyFunctor C n).obj (Q.obj (Q.objPreimage X)))) ∘
        ((Iso.refl _).homCongr e).symm := by
    ext φ
    simp [← Functor.map_comp]
  rw [this]
  exact (Equiv.bijective _).comp
    ((bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp_Q_obj' n P _).comp
      (Equiv.bijective _))

end DerivedCategory

namespace DerivedCategory

open Category CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

omit [Abelian C] in
lemma singleFunctors_shiftIso_inv_app_comp_shift_map {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] (n : ℤ) (P : C) {K : CochainComplex C ℤ}
    (χ : (CochainComplex.singleFunctor C n).obj P ⟶ K) (f : P ⟶ K.X n)
    (hf : f ≫ K.d n (n + 1) = 0)
    (hχ : (HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ χ.f n = f) :
    ((CochainComplex.singleFunctors C).shiftIso n 0 n (add_zero n)).inv.app P ≫ χ⟦n⟧' =
      Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf) := by
  apply HomologicalComplex.from_single_hom_ext
  subst hχ
  simp only [Cocycle.equivHomShift, CochainComplex.singleFunctors, AddEquiv.symm_trans_apply,
    HomologicalComplex.comp_f, shiftFunctor_map_f']
  simp only [shiftFunctor_obj_X', Functor.comp_obj, NatIso.ofComponents_inv_app,
    HomologicalComplex.Hom.isoOfComponents_inv_f, eqToIso.inv, AddEquiv.symm_symm,
    Cocycle.rightShiftAddEquiv_apply, Cocycle.equivHom_symm_apply, Cocycle.homOf_f,
    Cocycle.rightShift_coe, Cocycle.fromSingleMk_coe,
    Cochain.rightShift_v _ _ _ _ 0 0 _ n (zero_add n), Cochain.fromSingleMk_v,
    shiftFunctorObjXIso, Category.assoc]
  rw [← cancel_mono (K.XIsoOfEq (zero_add n)).hom]
  simp [HomologicalComplex.XIsoOfEq, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

variable [HasDerivedCategory C]

lemma singleFunctors_shiftIso_inv_app_comp_shift_map_Q_map (n : ℤ) (P : C)
    {K : CochainComplex C ℤ} (χ : (CochainComplex.singleFunctor C n).obj P ⟶ K) :
    ((singleFunctors C).shiftIso n 0 n (add_zero n)).inv.app P ≫ (Q.map χ)⟦n⟧' =
      ShiftedHom.map (((CochainComplex.singleFunctors C).shiftIso n 0 n (add_zero n)).inv.app P ≫
        χ⟦n⟧') Q := by
  have h := ((singleFunctorsPostcompQIso C).hom.comm n 0 n (add_zero n))
  rw [singleFunctorsPostcompQIso_hom_hom, singleFunctorsPostcompQIso_hom_hom] at h
  have h' := congrArg (fun t ↦ t.app P) h
  simp only [Functor.whiskerRight_id', Category.comp_id,
    Category.id_comp, SingleFunctors.postcomp_shiftIso_hom_app] at h'
  rw [← cancel_epi (((singleFunctors C).shiftIso n 0 n (add_zero n)).hom.app P),
    Iso.hom_inv_id_app_assoc, h']
  simp only [ShiftedHom.map]
  simp [← Functor.map_comp_assoc]

end DerivedCategory

namespace CategoryTheory.Adjunction

open Category CochainComplex

open _root_.DerivedCategory

set_option backward.defeqAttrib.useBackward true in
theorem mapDerivedCategoryRightDerivedAdjunction_counit_Q
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (I : CochainComplex B ℤ) :
    F.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ I) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I) := by
  let J := (HomotopyCategory.quotient B (.up ℤ)).obj I
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso B (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit J
  let d := adj.mapDerivedCategoryRightDerivedAdjunction
  let e := (DerivedCategory.quotientCompQhIso B).app I
  have ht :
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app J) ≫
        e.hom =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I) := by
    have hf := F.mapDerivedCategoryFactorsh_hom_app
      ((G.mapHomologicalComplex (.up ℤ)).obj I)
    change F.mapDerivedCategoryFactorsh.hom.app
      ((G.mapHomotopyCategory (.up ℤ)).obj J) = _ at hf
    rw [hf]
    dsimp [J]
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      Category.assoc]
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    dsimp only [Functor.comp_obj]
    erw [CategoryTheory.Functor.map_id]
    erw [CategoryTheory.Functor.map_id DerivedCategory.Qh]
    repeat' erw [Category.id_comp]
    rfl
  calc
    _ = F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        (F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
          d.counit.app (DerivedCategory.Qh.obj J)) ≫ e.hom := by
      dsimp only [Functor.rightDerivedFunctorUnitQ]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [d.counit.naturality e.hom]
      rfl
    _ = F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        (F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app J)) ≫
        e.hom := by erw [hfac]
    _ = _ := by
      rw [Category.assoc, ht]
      simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
        Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

theorem mapDerivedCategoryRightDerivedAdjunction_transpose_Q
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (a : P ⟶ (G.mapHomologicalComplex (.up ℤ)).obj I) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map a ≫ G.rightDerivedFunctorUnitQ I) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        (((adj.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm a) := by
  have hc : (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I =
      (adj.mapHomologicalComplex (.up ℤ)).counit.app I := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (Adjunction.mapHomologicalComplex_counit_app_f (.up ℤ) adj I i).symm
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    mapDerivedCategoryRightDerivedAdjunction_counit_Q adj I]
  rw [F.mapDerivedCategoryFactors_hom_naturality_assoc a]
  rw [Adjunction.homEquiv_counit, hc, CategoryTheory.Functor.map_comp]

/-- The derived transpose of a cochain map into `G(I)` followed by the derived unit is the
localization of the ordinary transpose. -/
theorem mapDerivedCategoryRightDerivedAdjunction_homEquiv_symm_Q
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (a : P ⟶ (G.mapHomologicalComplex (.up ℤ)).obj I) :
    (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm
      (DerivedCategory.Q.map a ≫ (DerivedCategory.quotientCompQhIso A).inv.app _ ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        (((adj.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm a) ≫
        (DerivedCategory.quotientCompQhIso B).inv.app I := by
  have h : (DerivedCategory.quotientCompQhIso A).inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) =
      G.rightDerivedFunctorUnitQ I ≫
        G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso B).inv.app I) := by
    simp [Functor.rightDerivedFunctorUnitQ, ← Functor.map_comp]
  rw [h, ← Category.assoc, Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
    mapDerivedCategoryRightDerivedAdjunction_transpose_Q, Category.assoc]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

open Category CochainComplex

lemma mapDerivedCategorySingleFunctor_inv_app
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (X : C₁) :
    (F.mapDerivedCategorySingleFunctor n).inv.app X =
      DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).inv.app X) ≫
        F.mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single C₁ (.up ℤ) n).obj X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
  rfl

end CategoryTheory.Functor
