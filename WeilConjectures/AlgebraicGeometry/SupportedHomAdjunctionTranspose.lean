/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.CategoryTheory.R.RHomDerivedRoof
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology

/-!
# The normalized supported-Hom map and the adjunction transpose

Source: blueprint `sec-smooth-purity/sk-thm-regular`, proof Step 5
(blueprint: lem-pur-supported-hom-adjunction-transpose).

The normalization is specified on every bounded-below injective complex. Naturality
then specifies it on every bounded-below object, independently of a resolution.
The degree-a single object is the canonical presentation of A[-a].
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace DerivedCategory

open Category CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A projective object placed in a single degree is K-projective. -/
instance isKProjective_singleFunctor_obj (P : C) [Projective P] (n : ℤ) :
    ((CochainComplex.singleFunctor C n).obj P).IsKProjective := by
  have (k : ℤ) : Projective (((CochainComplex.singleFunctor C n).obj P).X k) := by
    by_cases hk : k = n
    · subst hk
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) k P).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ n P k hk).projective
  exact isKProjective_of_projective _ n

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
  simp [Cochain.rightShift_v _ _ _ _ 0 0 _ n (zero_add n), Cochain.fromSingleMk_v]
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


namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Supported cohomology, as an additive-group-valued functor on D+.
Source: the definition of H^a RΓ_Z (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomCohomologyFunctor (a : ℤ) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.ι ⋙ supportedSectionsDerived A i ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}

/-- Morphisms from i_*A_Z in degree zero into the shifted bounded-below object.
Source: supported-Hom identification (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomMorphismFunctor (a : ℤ) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.ι ⋙
    shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) a ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
        ((supportedCoefficients A i).obj (ModuleCat.of A A))))

/-- The actual derived unit on a cochain representative, with the canonical localization
comparison on its source. Source: Stacks Tags 05TH, 05TI and the prescribed injective
normalization (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomDerivedUnit
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      (supportedSectionsDerived A i).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} A)).inv.app _ ≫
    (supportSections i A).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)

/-- The class of an abstract cycle of Γ_Z(I), transported by the actual derived unit.
Source: Stacks Tags 05TH, 05TI (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomCycleClass
    (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (s : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a) :
    (supportedHomCohomologyFunctor A i a).obj (DerivedCategory.Plus.Q.obj I) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map
    (supportedHomDerivedUnit A i I.obj)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) a).inv.app _
      ((((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a s))

/-- Evaluation at 1 on the degree-a cohomology of a map A[-a] → RΓ_Z(F).
This is the inverse of the cocycle-to-morphism identification in the statement.
Source: the specified cocycle convention
(blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomClassOfMorphism
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomCohomologyFunctor A i a).obj F :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map f
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u + 1} A) a).inv.app
      (ModuleCat.of A A) (1 : A))

variable [IsLocallyNoetherian X]

/-- Derive the normalized ordinary adjunction with its exact left adjoint.
Source: blueprint `def-pur-supported-exterior-product`, K-flat and injective derivation
(blueprint: def-pur-proetale-supported-exterior-product). -/
noncomputable def supportedCoefficientDerivedAdjunction :
    (supportedCoefficients A i).mapDerivedCategory ⊣ supportedSectionsDerived A i :=
  (supportedCoefficientAdjunction A i).mapDerivedCategoryRightDerivedAdjunction

/-- The adjoint of A[-a] → RΓ_Z(F), shifted by a. The two comparison isomorphisms
identify C_i(A[-a])[a] with C_i(A)[0]. Source: the cochain shift convention and the
normalized supported adjunction (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomShiftedTranspose
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomMorphismFunctor A i a).obj F :=
  ((DerivedCategory.singleFunctors
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).shiftIso a 0 a
      (add_zero a)).inv.app ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≫
    (((supportedCoefficients A i).mapDerivedCategorySingleFunctor a).inv.app
      (ModuleCat.of A A))⟦a⟧' ≫
    (((supportedCoefficientDerivedAdjunction A i).homEquiv _ _).symm f)⟦a⟧'

/-- The supported-Hom isomorphism has exactly the evaluation normalization on injectives.
For a cocycle f, its supported section is the ordinary adjoint evaluated at 1; the
ordinary quotient normalization identifies this with f_X(q_i(1)). The right side is
precisely the derived-Hom cocycle formula. Source: Stacks Tags 06XR, 070I
(blueprint: lem-pur-supported-hom-adjunction-transpose). -/
def SupportedHomEvaluationNormalization (a : ℤ)
    (χ : supportedHomCohomologyFunctor A i a ≅ supportedHomMorphismFunctor A i a) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_hi : ∀ r : ℤ, Injective (I.obj.X r))
    (f : (supportedCoefficients A i).obj (ModuleCat.of A A) ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a),
    (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).iCycles a s =
      ((supportedCoefficientAdjunction A i).homEquiv _ _ f) 1 →
    χ.hom.app (DerivedCategory.Plus.Q.obj I) (supportedHomCycleClass A i I a s) =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app
          ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧'

/-- Finiteness of the coefficient quotient in the purity conventions.
Source: finite coefficient datum, sk-def-purity-conv
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
instance purityCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  haveI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

section SupportedHomTranspose

open Category



/-- The class of a morphism `A[-a] ⟶ RΓ_Z(F)`, as an additive map. -/
noncomputable def supportedHomClassAddHom
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) →+ (supportedHomCohomologyFunctor A i a).obj F where
  toFun := supportedHomClassOfMorphism A i F a
  map_zero' := by simp [supportedHomClassOfMorphism]
  map_add' f g := by simp [supportedHomClassOfMorphism]

omit [IsLocallyNoetherian X] in
/-- Every degree-`a` cohomology class of `RΓ_Z(F)` is the class of a unique morphism
`A[-a] ⟶ RΓ_Z(F)`, since `A` is free of rank one. -/
lemma supportedHomClassOfMorphism_bijective
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) : Function.Bijective (supportedHomClassOfMorphism A i F a) := by
  have h := DerivedCategory.bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp' a
    (ModuleCat.of A A) ((supportedSectionsDerived A i).obj F.obj)
  exact ((ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf A A _).toEquiv).bijective.comp
    h :)

/-- The shifted transpose, as an additive map. -/
noncomputable def supportedHomShiftedTransposeAddHom
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) →+ (supportedHomMorphismFunctor A i a).obj F where
  toFun := supportedHomShiftedTranspose A i F a
  map_zero' := by simp [supportedHomShiftedTranspose, supportedHomMorphismFunctor]
  map_add' f g := by
    simp [supportedHomShiftedTranspose, supportedHomMorphismFunctor, Adjunction.homEquiv_counit]

/-- The shifted transpose is bijective. -/
lemma supportedHomShiftedTranspose_bijective
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) : Function.Bijective (supportedHomShiftedTranspose A i F a) := by
  refine ⟨fun f g h ↦ ?_, fun y ↦ ?_⟩
  · simp only [supportedHomShiftedTranspose] at h
    rw [cancel_epi, cancel_epi] at h
    exact ((supportedCoefficientDerivedAdjunction A i).homEquiv _ _).symm.injective
      ((CategoryTheory.shiftFunctor _ a).map_injective h)
  · obtain ⟨g, hg⟩ := (CategoryTheory.shiftFunctor (DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) a).map_surjective
      (inv (((DerivedCategory.singleFunctors
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).shiftIso a 0 a
          (add_zero a)).inv.app ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≫
        (((supportedCoefficients A i).mapDerivedCategorySingleFunctor a).inv.app
          (ModuleCat.of A A))⟦a⟧') ≫ y)
    refine ⟨(supportedCoefficientDerivedAdjunction A i).homEquiv _ _ g, ?_⟩
    dsimp only [supportedHomShiftedTranspose]
    erw [Equiv.symm_apply_apply]
    rw [hg, ← Category.assoc, IsIso.hom_inv_id_assoc]

omit [IsLocallyNoetherian X] in
/-- Naturality of the class of a morphism. -/
lemma supportedHomCohomologyFunctor_map_classOfMorphism
    {F G : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (g : F ⟶ G) (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomCohomologyFunctor A i a).map g (supportedHomClassOfMorphism A i F a f) =
      supportedHomClassOfMorphism A i G a
        (f ≫ (supportedSectionsDerived A i).map (DerivedCategory.Plus.ι.map g)) := by
  simp [supportedHomClassOfMorphism, supportedHomCohomologyFunctor]

omit [Finite A] [IsClosedImmersion i] [IsLocallyNoetherian X] in
/-- The preadditive coyoneda functor acts by postcomposition. -/
lemma preadditiveCoyoneda_obj_map_apply {C : Type*} [Category C] [Preadditive C] (S : C)
    {Y Y' : C} (h : Y ⟶ Y') (x : S ⟶ Y) :
    (preadditiveCoyoneda.obj (op S)).map h x = x ≫ h :=
  rfl

/-- Naturality of the shifted transpose. -/
lemma supportedHomMorphismFunctor_map_shiftedTranspose
    {F G : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (g : F ⟶ G) (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomMorphismFunctor A i a).map g (supportedHomShiftedTranspose A i F a f) =
      supportedHomShiftedTranspose A i G a
        (f ≫ (supportedSectionsDerived A i).map (DerivedCategory.Plus.ι.map g)) := by
  simp [supportedHomShiftedTranspose, supportedHomMorphismFunctor,
    Adjunction.homEquiv_naturality_right_symm, preadditiveCoyoneda_obj_map_apply]

/-- The component of the supported-Hom isomorphism at `F`. -/
noncomputable def supportedHomTransposeIsoApp
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) :
    (supportedHomCohomologyFunctor A i a).obj F ≅ (supportedHomMorphismFunctor A i a).obj F :=
  AddEquiv.toAddCommGrpIso
    ((AddEquiv.ofBijective (supportedHomClassAddHom A i F a)
      (supportedHomClassOfMorphism_bijective A i F a)).symm.trans
      (AddEquiv.ofBijective (supportedHomShiftedTransposeAddHom A i F a)
        (supportedHomShiftedTranspose_bijective A i F a)))

/-- The component sends the class of a morphism to its shifted transpose. -/
lemma supportedHomTransposeIsoApp_hom_classOfMorphism
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomTransposeIsoApp A i F a).hom (supportedHomClassOfMorphism A i F a f) =
      supportedHomShiftedTranspose A i F a f := by
  have h := (AddEquiv.ofBijective (supportedHomClassAddHom A i F a)
      (supportedHomClassOfMorphism_bijective A i F a)).symm_apply_apply f
  exact congrArg (supportedHomShiftedTranspose A i F a) h

/-- The supported-Hom isomorphism `H^a RΓ_Z(F) ≅ Hom(C_i(A)[0], F[a])`: a class is written
as the class of a morphism `A[-a] ⟶ RΓ_Z(F)`, which is sent to its shifted transpose. -/
noncomputable def supportedHomTransposeIso (a : ℤ) :
    supportedHomCohomologyFunctor A i a ≅ supportedHomMorphismFunctor A i a :=
  NatIso.ofComponents (fun F ↦ supportedHomTransposeIsoApp A i F a) (fun {F G} g ↦ by
    ext x
    obtain ⟨f, rfl⟩ := (supportedHomClassOfMorphism_bijective A i F a).2 x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      supportedHomCohomologyFunctor_map_classOfMorphism,
      supportedHomTransposeIsoApp_hom_classOfMorphism,
      supportedHomTransposeIsoApp_hom_classOfMorphism,
      supportedHomMorphismFunctor_map_shiftedTranspose])

/-- The supported-Hom isomorphism sends the class of a morphism to its shifted transpose. -/
lemma supportedHomTransposeIso_hom_app_classOfMorphism
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomTransposeIso A i a).hom.app F (supportedHomClassOfMorphism A i F a f) =
      supportedHomShiftedTranspose A i F a f :=
  supportedHomTransposeIsoApp_hom_classOfMorphism A i F a f

/-- The evaluation normalization of the supported-Hom isomorphism on injective complexes. -/
lemma supportedHomTransposeIso_normalization (a : ℤ) :
    SupportedHomEvaluationNormalization A i a (supportedHomTransposeIso A i a) := by
  intro I _ f hf s hs
  have hb : (supportedCoefficientAdjunction A i).homEquiv _ _ f ≫
      (supportSections i A).map (I.obj.d a (a + 1)) = 0 := by
    rw [← Adjunction.homEquiv_naturality_right, hf]
    simp [Adjunction.homEquiv_unit]
  let φ : (HomologicalComplex.single (ModuleCat.{u + 1} A) (.up ℤ) a).obj (ModuleCat.of A A) ⟶
      ((supportSections i A).mapHomologicalComplex (.up ℤ)).obj I.obj :=
    HomologicalComplex.mkHomFromSingle ((supportedCoefficientAdjunction A i).homEquiv _ _ f)
      (fun k hk ↦ by
        obtain rfl : a + 1 = k := hk
        simp [hb])
  have h1 : supportedHomCycleClass A i I a s = supportedHomClassOfMorphism A i
      (DerivedCategory.Plus.Q.obj I) a
      (DerivedCategory.Q.map φ ≫ supportedHomDerivedUnit A i I.obj) := by
    have key := congrArg (fun g ↦ g (1 : A))
      (DerivedCategory.singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map'
        a (ModuleCat.of A A) φ)
    simp only [ConcreteCategory.comp_apply] at key
    have hl : ((((supportSections i A).mapHomologicalComplex (.up ℤ)).obj I.obj).liftCycles
        ((HomologicalComplex.singleObjXSelf (.up ℤ) a (ModuleCat.of A A)).inv ≫ φ.f a) (a + 1)
        (by simp) (by simp [φ, hb])) (1 : A) = s := by
      apply (ModuleCat.mono_iff_injective
        ((((supportSections i A).mapHomologicalComplex (.up ℤ)).obj I.obj).iCycles a)).1
        inferInstance
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i, hs]
      simp [φ]
      rfl
    dsimp only [supportedHomCycleClass, supportedHomClassOfMorphism]
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
    erw [key, hl]
    rfl
  rw [h1, supportedHomTransposeIso_hom_app_classOfMorphism]
  dsimp only [supportedHomShiftedTranspose, supportedHomDerivedUnit,
    supportedCoefficientDerivedAdjunction]
  erw [Adjunction.mapDerivedCategoryRightDerivedAdjunction_homEquiv_symm_Q,
    Functor.mapDerivedCategorySingleFunctor_inv_app]
  rw [← DerivedCategory.singleFunctors_shiftIso_inv_app_comp_shift_map a _
      ((HomologicalComplex.singleMapHomologicalComplex (supportedCoefficients A i) (.up ℤ)
        a).inv.app
        (ModuleCat.of A A) ≫ ((Adjunction.mapHomologicalComplex (.up ℤ)
          (supportedCoefficientAdjunction A i)).homEquiv _ _).symm φ) f hf ?_,
    ← DerivedCategory.singleFunctors_shiftIso_inv_app_comp_shift_map_Q_map]
  · simp only [Functor.map_comp, Category.assoc, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    erw [← Functor.map_comp_assoc (CategoryTheory.shiftFunctor _ a)
      ((supportedCoefficients A i).mapDerivedCategoryFactors.inv.app _), Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  · simp [φ, Adjunction.homEquiv_counit]
    rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

end SupportedHomTranspose

/-- The canonical, evaluation-normalized supported-Hom isomorphism equals the shifted
transpose under the supported adjunction. Source: blueprint sk-thm-regular, proof Step 5
(blueprint: lem-pur-supported-hom-adjunction-transpose).

Proof:
1. Put P=C_i(A) and G=Γ_Z. The quotient normalization of
   def-pur-proetale-supported-exterior-product identifies the ordinary adjoint b of f
   by f_X(q_i(1))=b(1). Evaluation at 1 identifies Hom_A(A,G(M)) with G(M), naturally.
2. On the chosen small pro-etale site, prop-pur-kinjective-resolutions-exist and
   lem-sp-grothendieck-enough-injectives supply injectives. By
   lem-sc-bounded-below-injective-resolution choose F→I, bounded below, termwise
   injective and K-injective. The derived unit computes RG there, by
   lem-weil-pbc-right-derived-plus-injective.
3. The ordinary evaluation bijection is a natural additive isomorphism. Apply it
   degreewise to I and derive its inverse. Uniqueness of the right-derived extension
   identifies the result on I with its termwise map, sending s to its ordinary adjoint f_s.
4. By lem-sc-p1-rhom-hom-derived-roof, f_s represents the derived morphism
   P[0]→I[a]→F[a]. This gives χ, its naturality, and the displayed normalization.
5. By lem-sc-derived-adjunction-from-underived the derived counit on I is the
   localized ordinary counit. Hence the transpose of the map taking 1 to s is
   P[-a]→I→F, with degree-a component f_s.
6. Shift by a, using (K[a])^r=K^(r+a). Components of a degree-zero map do not change,
   so this is the same map as in step 4. Boundaries give homotopies with component
   (-1)^a f_t after shifting. Naturality transports both formulas from I to F.
   Every cohomology class is represented by a map A[-a]→RG(F), because A is free of
   rank one. Thus the quantified formula is χ(x)=x^flat[a] for every class x. -/
theorem supportedHom_adjunction_transpose (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] (a : ℤ) :
    ∃ χ : supportedHomCohomologyFunctor P.Coefficient i a ≅
        supportedHomMorphismFunctor P.Coefficient i a,
      SupportedHomEvaluationNormalization P.Coefficient i a χ ∧
      ∀ (F : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
        (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} P.Coefficient) a).obj
            (ModuleCat.of P.Coefficient P.Coefficient) ⟶
          (supportedSectionsDerived P.Coefficient i).obj F.obj),
        χ.hom.app F (supportedHomClassOfMorphism P.Coefficient i F a f) =
          supportedHomShiftedTranspose P.Coefficient i F a f :=
  ⟨supportedHomTransposeIso P.Coefficient i a,
    supportedHomTransposeIso_normalization P.Coefficient i a,
    fun F f ↦ supportedHomTransposeIso_hom_app_classOfMorphism P.Coefficient i F a f⟩

end AlgebraicGeometry.ProEtale
