/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Paper.RealizationCompletedPullData
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Scalar units for the ordinary continuous-coefficient pullback comparison

Source: Stacks, Tags 03D2, 03CZ, 0D6D and 07A6; Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-realization-ordinary-pull-scalar-unit)

This concerns ambient unbounded objects before completion or restriction to integral
constructible objects. The ordinary comparison is the supplied, normalized comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] completedModulePullback proEtaleRingModulePullback


variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {k : Type u} [Field k]
variable {T U : RealizationPullScheme l k} {f : T.scheme ⟶ U.scheme}
  {sT : RealizationScalarFunctorData l E T.scheme}
  {sU : RealizationScalarFunctorData l E U.scheme}

/-- Fixed ordinary module coordinate, kept folded in the diagram calculation. -/
@[irreducible] private def moduleCoordinate
    (a : RealizationCompletedPullArrow T U f sT sU) :
    pbcActualModulePull f (pbcIntegralDatum l E) ≅
      proEtaleRingModulePullback f _ _
        (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
          a.coefficient_isIso) :=
  (pbcActualModuleAdjunction f (pbcIntegralDatum l E)).leftAdjointUniq
    (proEtaleRingModuleAdjunction f _ _
      (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
        a.coefficient_isIso))

/-- Fixed ordinary derived coordinate, kept folded in the diagram calculation. -/
@[irreducible] private def derivedCoordinate
    (a : RealizationCompletedPullArrow T U f sT sU) :
    pbcActualDerivedPull f (pbcIntegralDatum l E) ≅
      proEtaleRingDerivedPullback f _ _
        (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
          a.coefficient_isIso) :=
  (pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).leftAdjointUniq
    (proEtaleRingDerivedAdjunction f _ _
      (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
        a.coefficient_isIso))

/-- Cochain factorization of the standard derived square. This only uses the
three exact-functor factorization formulas, without monoidal or six-functor data.
Source: Stacks Tag 0D6D; the generic calculation is also used in
`Sheaf.SixFunctors.ExactLocalizationInverseMate`. -/
private lemma cochainSquare_fac
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : CochainComplex A ℤ) :
    F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app K) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app K) := by
  have hF := Functor.mapDerivedCategoryCompIso_fac F₁ F₂ K
  have hG := Functor.mapDerivedCategoryCompIso_fac G₁ G₂ K
  have he := Functor.mapDerivedCategoryNatIso_fac e K
  have hG' : (Functor.mapDerivedCategoryCompIso G₁ G₂).hom.app (DerivedCategory.Q.obj K) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      (G₁ ⋙ G₂).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app K) := by
    rw [← hG]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hF' : F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app K) ≫
      (Functor.mapDerivedCategoryCompIso F₁ F₂).inv.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app K) ≫
        (F₁ ⋙ F₂).mapDerivedCategoryFactors.inv.app K := by
    rw [← cancel_mono ((F₁ ⋙ F₂).mapDerivedCategoryFactors.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hF, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hF', hG', reassoc_of% he, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]

private theorem squareHom_fac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have h := cochainSquare_fac e K
  have hh : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂))
        (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂))
          (.up ℤ)).inv.app K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
    congr 1
    ext n
    change 𝟙 _ ≫ e.hom.app (K.X n) ≫ 𝟙 _ = e.hom.app (K.X n)
    exact (Category.id_comp _).trans (Category.comp_id _)
  have h := h.trans hh
  let i := F₂.mapDerivedCategoryFactors.inv.app
    ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app K)
  have hi : i ≫ (F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K)) =
      𝟙 _ := by
    dsimp only [i]
    rw [Category.assoc, ← Category.assoc
      (F₂.mapDerivedCategory.map _) (F₂.mapDerivedCategory.map _),
      ← F₂.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
    erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
  apply (cancel_epi i).1
  calc
    _ = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
      exact (Category.assoc _ _ _).trans h
    _ = _ := by
      have hc := congrArg (· ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K)) hi
      simp only [Category.assoc, Category.id_comp] at hc
      exact hc.symm

private theorem squareInv_fac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso G₁ G₂).symm ≪≫
        Functor.mapDerivedCategoryNatIso e.symm ≪≫
        Functor.mapDerivedCategoryCompIso F₁ F₂).inv.app (DerivedCategory.Q.obj K) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have hb : ((Functor.mapDerivedCategoryCompIso G₁ G₂).symm ≪≫
      Functor.mapDerivedCategoryNatIso e.symm ≪≫
      Functor.mapDerivedCategoryCompIso F₁ F₂).inv =
      (Functor.mapDerivedCategorySquareIso e).hom := by
    dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.symm_inv]
    rw [← Functor.mapDerivedCategoryNatIso_symm e.symm]
    simp only [Iso.symm_symm_eq, Category.assoc]
  rw [hb]
  exact squareHom_fac e K

private theorem leftUniq_of_counit
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (x : L ⟶ L')
    (hx : ∀ Z, x.app (R.obj Z) ≫ adj'.counit.app Z = adj.counit.app Z) :
    x = (adj.leftAdjointUniq adj').hom := by
  apply (conjugateEquiv adj' adj).injective
  rw [conjugateEquiv_leftAdjointUniq_hom]
  ext Z
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, conjugateEquiv_counit, hx]
  simp only [NatTrans.id_app, Adjunction.homEquiv_counit, L.map_id,
    Category.id_comp]

private theorem derivedLeftUniq_fac
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (Q : C ⥤ C') (Q' : D ⥤ D') (W : MorphismProperty C) (W' : MorphismProperty D)
    [Q.IsLocalization W] [Q'.IsLocalization W']
    (LD LD' : C' ⥤ D') (RD : D' ⥤ C')
    (α : Q ⋙ LD ⟶ L ⋙ Q') (α' : Q ⋙ LD' ⟶ L' ⋙ Q')
    (β : R ⋙ Q ⟶ Q' ⋙ RD)
    [LD.IsLeftDerivedFunctor α W] [LD'.IsLeftDerivedFunctor α' W]
    [RD.IsRightDerivedFunctor β W']
    [(LD ⋙ RD).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RD) W]
    [(RD ⋙ LD).IsRightDerivedFunctor
      (Functor.whiskerRight β LD ≫ (Functor.associator _ _ _).hom) W']
    [(LD' ⋙ RD).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α' RD) W]
    [(RD ⋙ LD').IsRightDerivedFunctor
      (Functor.whiskerRight β LD' ≫ (Functor.associator _ _ _).hom) W']
    (K : C) :
    ((adj.derived W W' α β).leftAdjointUniq (adj'.derived W W' α' β)).hom.app
        (Q.obj K) ≫ α'.app K =
      α.app K ≫ Q'.map ((adj.leftAdjointUniq adj').hom.app K) := by
  let x := Functor.leftDerivedNatTrans LD LD' α α' W
    (Functor.whiskerRight (adj.leftAdjointUniq adj').hom Q')
  have hx : x =
      ((adj.derived W W' α β).leftAdjointUniq (adj'.derived W W' α' β)).hom := by
    apply leftUniq_of_counit
    have hc : Functor.whiskerLeft RD x ≫ (adj'.derived W W' α' β).counit =
        (adj.derived W W' α β).counit := by
      apply (RD ⋙ LD).rightDerived_ext
        (Functor.whiskerRight β LD ≫ (Functor.associator _ _ _).hom) W'
      ext Z
      have hn := x.naturality (β.app Z)
      have hf := Functor.leftDerivedNatTrans_app LD LD' α α' W
        (Functor.whiskerRight (adj.leftAdjointUniq adj').hom Q') (R.obj Z)
      dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.whiskerLeft_app]
      simp only [Category.comp_id]
      change LD.map (β.app Z) ≫ x.app (RD.obj (Q'.obj Z)) =
        x.app (Q.obj (R.obj Z)) ≫ LD'.map (β.app Z) at hn
      rw [← Category.assoc]
      apply Eq.trans (congrArg (· ≫ (adj'.derived W W' α' β).counit.app (Q'.obj Z)) hn)
      rw [Category.assoc]
      rw [Adjunction.derived_counit, adj'.derivedε_fac_app]
      rw [← Category.assoc, hf, Category.assoc]
      dsimp only [Functor.whiskerRight_app]
      rw [← Q'.map_comp]
      rw [adj.leftAdjointUniq_hom_app_counit]
      exact (adj.derivedε_fac_app W' α β Z).symm
    exact congr_app hc
  rw [← hx]
  exact Functor.leftDerivedNatTrans_app LD LD' α α' W
    (Functor.whiskerRight (adj.leftAdjointUniq adj').hom Q') K

private theorem homotopyLeftUniq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {L L' : C ⥤ D} {R : D ⥤ C} [L.Additive] [L'.Additive] [R.Additive]
    (adj : L ⊣ R) (adj' : L' ⊣ R) :
    NatTrans.mapHomotopyCategory (adj.leftAdjointUniq adj').hom (.up ℤ) =
      ((adj.mapHomotopyCategory (.up ℤ)).leftAdjointUniq
        (adj'.mapHomotopyCategory (.up ℤ))).hom := by
  apply leftUniq_of_counit
  intro K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ =
    (HomotopyCategory.quotient D (.up ℤ)).map _
  rw [← Functor.map_comp]
  congr 1
  ext n
  exact adj.leftAdjointUniq_hom_app_counit adj' (K.X n)

private theorem derivedLeftUniq_complex_fac
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F F' : C ⥤ D} {R : D ⥤ C} [F.Additive] [F'.Additive] [R.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (adj : F ⊣ R) (adj' : F' ⊣ R)
    (LD : DerivedCategory C ⥤ DerivedCategory D)
    (α : DerivedCategory.Qh ⋙ LD ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LD.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ))]
    [(LD ⋙ R.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α R.rightDerivedFunctor)
      (HomotopyCategory.quasiIso C (.up ℤ))]
    [(R.rightDerivedFunctor ⋙ LD).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorUnit LD ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso D (.up ℤ))]
    (K : CochainComplex C ℤ) :
    (((adj.mapHomotopyCategory (.up ℤ)).derived
        (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ))
        α R.rightDerivedFunctorUnit).leftAdjointUniq
      adj'.mapDerivedCategoryRightDerivedAdjunction).hom.app (DerivedCategory.Q.obj K) ≫
        F'.mapDerivedCategoryFactors.hom.app K =
      (LD.map ((DerivedCategory.quotientCompQhIso C).inv.app K) ≫
        α.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (adj.leftAdjointUniq adj').hom (.up ℤ)).app K) := by
  have he := derivedLeftUniq_fac (adj.mapHomotopyCategory (.up ℤ))
    (adj'.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ))
    LD F'.mapDerivedCategory R.rightDerivedFunctor α F'.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  rw [← homotopyLeftUniq] at he
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at he
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors] at he ⊢
  repeat first
    | erw [CategoryTheory.Functor.map_id] at he
    | erw [Category.id_comp] at he
    | erw [Category.comp_id] at he
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  exact he

private theorem ordinaryPull_coordinate_computation
    (a : RealizationCompletedPullArrow T U f sT sU)
    (K : CochainComplex
      (pbcModules U.scheme (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))) ℤ) :
    (derivedCoordinate a).hom.app (DerivedCategory.Q.obj K) ≫
      (proEtaleRingDerivedPullbackFactors f _ _
        (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
          a.coefficient_isIso)).hom.app K =
    pbcActualPullComplexCounit f (pbcIntegralDatum l E) K ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (moduleCoordinate a).hom (.up ℤ)).app K) := by
  unfold derivedCoordinate moduleCoordinate
  let cA := @asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
    a.coefficient_isIso
  let adj' : proEtaleRingModulePullback f _ _ cA ⊣
      pbcActualModulePush f (pbcIntegralDatum l E) :=
    proEtaleRingModuleAdjunction f _ _ cA
  have : ((pbcActualModulePush f (pbcIntegralDatum l E)).rightDerivedFunctor ⋙
      pbcActualDerivedPull f (pbcIntegralDatum l E)).IsRightDerivedFunctor
      (Functor.whiskerRight
        (pbcActualModulePush f (pbcIntegralDatum l E)).rightDerivedFunctorUnit
        (pbcActualDerivedPull f (pbcIntegralDatum l E)) ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    pbcActualDerivedRightComposite f (pbcIntegralDatum l E)
  exact derivedLeftUniq_complex_fac
    (pbcActualModuleAdjunction f (pbcIntegralDatum l E)) adj'
    (pbcActualDerivedPull f (pbcIntegralDatum l E))
    (pbcActualPullCounit f (pbcIntegralDatum l E)) K

private theorem ringModuleUnit_normalized
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleAdjunctionNormalized g R S c
      (proEtaleRingModuleAdjunction g R S c) := by
  let : (proEtaleModelBaseChange g).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
    proEtaleModelBaseChange_isContinuous g
  unfold proEtaleRingModuleAdjunctionNormalized
  intro M V m
  rw [← (proEtaleRingModuleAdjunction g R S c).homEquiv_id]
  obtain ⟨z, hz, he⟩ := (Classical.choose_spec
    (proEtaleRingModuleAdjunction_existsUnique g R S c)).1 M _ (𝟙 _)
  dsimp only [proEtaleRingModuleAdjunction]
  erw [he]
  rw [Adjunction.homEquiv_unit]
  change z.val.app _
    (((SheafOfModules.pullbackPushforwardAdjunction
      (proEtaleModelRingUnit g R)).unit.app ((proEtaleModuleToModel _).obj M)).val.app
        (AsSmall.up.op.obj (Opposite.op V)) m) = _
  erw [hz]
  unfold proEtaleRingModuleUnitSection
  rfl

private theorem ordinaryModule_scalarUnit
    (a : RealizationCompletedPullArrow T U f sT sU)
    (M : pbcModules U.scheme (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))) :
    (pbcScalarAdjunction (realizationPullScalarMap l E sT)).unit.app
        ((pbcActualModulePull f (pbcIntegralDatum l E)).obj M) ≫
      (pbcRestrict (realizationPullScalarMap l E sT)).map
        (a.moduleComparison.hom.app M) =
    (pbcActualModulePull f (pbcIntegralDatum l E)).map
        ((pbcScalarAdjunction (realizationPullScalarMap l E sU)).unit.app M) ≫
      (moduleCoordinate a).hom.app
          ((pbcRestrict (realizationPullScalarMap l E sU)).obj
            ((pbcExtend (realizationPullScalarMap l E sU)).obj M)) ≫
      (proEtaleRingRestrictionPullbackInv f
        (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
        (rationalCoefficientSheaf l U.scheme E)
        (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
        (rationalCoefficientSheaf l T.scheme E)
        (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
        (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
          a.coefficient_isIso) a.rationalCoefficient a.coefficient_square.symm).app
            ((pbcExtend (realizationPullScalarMap l E sU)).obj M) := by
  unfold moduleCoordinate
  let cA := @asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
    a.coefficient_isIso
  let adj := pbcActualModuleAdjunction f (pbcIntegralDatum l E)
  let adjA : proEtaleRingModulePullback f _ _ cA ⊣
      pbcActualModulePush f (pbcIntegralDatum l E) :=
    proEtaleRingModuleAdjunction f _ _ cA
  let adjE := proEtaleRingModuleAdjunction f _ _ a.rationalCoefficient
  let jT := (pbcScalarAdjunction (realizationPullScalarMap l E sT)).unit
  let jU := (pbcScalarAdjunction (realizationPullScalarMap l E sU)).unit
  let rT := pbcRestrict (realizationPullScalarMap l E sT)
  let rU := pbcRestrict (realizationPullScalarMap l E sU)
  let FU := pbcExtend (realizationPullScalarMap l E sU)
  let P := pbcActualModulePull f (pbcIntegralDatum l E)
  let Q := pbcActualModulePush f (pbcIntegralDatum l E)
  let e := adj.leftAdjointUniq adjA
  let b := proEtaleRingRestrictionPullbackInv f
    (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l U.scheme E)
    (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l T.scheme E)
    (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
    cA a.rationalCoefficient a.coefficient_square.symm
  let d := proEtaleRingRestrictionDirectImage f
    (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l U.scheme E)
    (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l T.scheme E)
    (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
    cA a.rationalCoefficient a.coefficient_square.symm
  change jT.app (P.obj M) ≫ rT.map (a.moduleComparison.hom.app M) =
    P.map (jU.app M) ≫ e.hom.app (rU.obj (FU.obj M)) ≫ b.app (FU.obj M)
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hnat := adj.unit.naturality (jU.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hnat
  rw [← reassoc_of% hnat]
  rw [adj.unit_leftAdjointUniq_hom_app_assoc]
  have hu := unit_mateEquiv adjE adjA (TwoSquare.mk _ _ _ _ b) (FU.obj M)
  have hm := restrictionPullback_mate f
    (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l U.scheme E)
    (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l T.scheme E)
    (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
    cA a.rationalCoefficient a.coefficient_square.symm
  change rU.map (adjE.unit.app (FU.obj M)) ≫
      (mateEquiv adjE adjA (TwoSquare.mk _ _ _ _ b)).natTrans.app _ =
    adjA.unit.app (rU.obj (FU.obj M)) ≫ Q.map (b.app (FU.obj M)) at hu
  erw [hm] at hu
  rw [← hu]
  apply SheafOfModules.hom_ext
  ext V m
  change (a.moduleComparison.hom.app M).val.app
      ((proEtaleBaseChange f).op.obj V)
      ((jT.app (P.obj M)).val.app ((proEtaleBaseChange f).op.obj V)
        ((adj.unit.app M).val.app V m)) =
    (d.hom.app
      ((proEtaleRingModulePullback f _ _ a.rationalCoefficient).obj (FU.obj M))).val.app V
      ((adjE.unit.app (FU.obj M)).val.app V ((jU.app M).val.app V m))
  have hd := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique f
      (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
      (rationalCoefficientSheaf l U.scheme E)
      (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
      (rationalCoefficientSheaf l T.scheme E)
      (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
      cA a.rationalCoefficient a.coefficient_square.symm)).1
      ((proEtaleRingModulePullback f _ _ a.rationalCoefficient).obj (FU.obj M)) V
      ((adjE.unit.app (FU.obj M)).val.app V ((jU.app M).val.app V m))
  have hA := (pbcActualModuleAdjunction_exists f (pbcIntegralDatum l E)).exists.choose_spec
    M V.unop m
  have hE := ringModuleUnit_normalized f _ _ a.rationalCoefficient (FU.obj M) V.unop
    ((jU.app M).val.app V m)
  have hT : (jT.app (P.obj M)).val.app ((proEtaleBaseChange f).op.obj V)
      (pbcActualModuleUnitSection f (pbcIntegralDatum l E) M V.unop m) =
      pbcTensorSection (realizationPullScalarMap l E sT) (P.obj M)
        ((proEtaleBaseChange f).op.obj V) 1
        (pbcActualModuleUnitSection f (pbcIntegralDatum l E) M V.unop m) := by
    unfold jT realizationPullScalarMap
    exact sT.tensor_unit (P.obj M) ((proEtaleBaseChange f).op.obj V) _
  have hU : (jU.app M).val.app V m =
      pbcTensorSection (realizationPullScalarMap l E sU) M V 1 m := by
    unfold jU realizationPullScalarMap
    exact sU.tensor_unit M V m
  exact (congrArg (fun z ↦ (a.moduleComparison.hom.app M).val.app
      ((proEtaleBaseChange f).op.obj V) ((jT.app (P.obj M)).val.app
        ((proEtaleBaseChange f).op.obj V) z)) hA).trans
    ((congrArg (fun z ↦ (a.moduleComparison.hom.app M).val.app
      ((proEtaleBaseChange f).op.obj V) z) hT).trans
      ((a.module_unit M V.unop m).trans
        ((congrArg (fun z ↦ proEtaleRingModuleUnitSection f _ _
          a.rationalCoefficient (FU.obj M) V.unop z) hU).symm.trans
          (hE.symm.trans hd.symm))))

private theorem rightFactor
    {X Y W V : Type*} [Category X] [Category Y] [Category W] [Category V]
    (P A : X ⥤ Y) (B : W ⥤ V) (r : W ⥤ X) (s : V ⥤ Y)
    (e : P ≅ A) (b : B ⋙ s ≅ r ⋙ A)
    {N : X} {Z Z' : W} {X' : X} {Y₀ Y₁ Y₂ : Y}
    (j : N ⟶ r.obj Z) (δ : Z ⟶ Z') (u : r.obj Z' ⟶ X')
    (v : A.obj X' ⟶ Y₁) (w : s.obj (B.obj Z') ⟶ Y₂)
    (q : Y₁ ⟶ Y₂) (c : P.obj X' ⟶ Y₀) (t : Y₀ ⟶ Y₁)
    (hb : b.inv.app Z' ≫ w = A.map u ≫ v ≫ q)
    (he : e.hom.app X' ≫ v = c ≫ t) :
    (P.map j ≫ e.hom.app (r.obj Z) ≫ b.inv.app Z) ≫
        s.map (B.map δ) ≫ w =
      P.map (j ≫ r.map δ ≫ u) ≫ c ≫ t ≫ q := by
  simp only [Category.assoc]
  have hn := b.inv.naturality δ
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← e.hom.naturality_assoc, hb, ← e.hom.naturality_assoc]
  rw [reassoc_of% he]
  simp only [Functor.map_comp, Category.assoc]

private theorem scalarUnit_named
    (W : RealizationPullScheme l k) (d : RealizationScalarFunctorData l E W.scheme)
    (K : CochainComplex
      (pbcModules W.scheme (pbcAdicCompletion W.scheme (pbcIntegralDatum l E))) ℤ) :
    (pbcDerivedScalarAdjunction (realizationPullScalarMap l E d)).unit.app
        (DerivedCategory.Q.obj K) ≫
      (pbcDerivedRestrict (realizationPullScalarMap l E d)).map
        (pbcComplexCounit (realizationPullScalarMap l E d) K) ≫
      (pbcRestrict (realizationPullScalarMap l E d)).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (realizationPullScalarMap l E d)).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (pbcScalarAdjunction (realizationPullScalarMap l E d)).unit (.up ℤ)).app K) := by
  unfold realizationPullScalarMap
  exact d.unit K

private theorem leftFactor
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (r : B ⥤ A) (Q : C ⥤ B) (S : C ⥤ A)
    (η : 𝟭 A ⟶ F ⋙ r) (fac : Q ⋙ r ⟶ S)
    {X X' : A} {Z : B} {K K' : C}
    (c : X ⟶ X') (α : F.obj X ⟶ Z) (v : Z ⟶ Q.obj K)
    (δ : F.obj X' ⟶ Q.obj K') (a : K' ⟶ K) (j : X' ⟶ S.obj K')
    (hc : α ≫ v = F.map c ≫ δ ≫ Q.map a)
    (hu : η.app X' ≫ r.map δ ≫ fac.app K' = j) :
    (η.app X ≫ r.map α) ≫ r.map v ≫ fac.app K = c ≫ j ≫ S.map a := by
  simp only [Category.assoc]
  rw [← r.map_comp_assoc, hc, r.map_comp, r.map_comp]
  have hη := η.naturality c
  dsimp only [Functor.id_map, Functor.comp_map] at hη
  simp only [Category.assoc]
  rw [← reassoc_of% hη]
  have hf := fac.naturality a
  dsimp only [Functor.comp_map] at hf
  rw [hf, ← Category.assoc (r.map δ), ← Category.assoc (η.app X'), hu]

private theorem computationNaturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ B) (P : B ⥤ D) (Pc : A ⥤ C) (Q' : C ⥤ D)
    (cp : Q ⋙ P ⟶ Pc ⋙ Q') {K K' : A} {Y Z : C}
    (u : K ⟶ K') (v : Pc.obj K' ⟶ Y) (w : Y ⟶ Z) :
    P.map (Q.map u) ≫ cp.app K' ≫ Q'.map v ≫ Q'.map w =
      cp.app K ≫ Q'.map (Pc.map u ≫ v ≫ w) := by
  have hn := cp.naturality u
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]

private theorem unitSquare_computations
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P PA : A ⥤ B) (PE : C ⥤ D) (FT : B ⥤ D) (FU : A ⥤ C)
    (rT : D ⥤ B) (rU : C ⥤ A)
    [P.Additive] [PA.Additive] [PE.Additive] [FT.Additive] [FU.Additive]
    [rT.Additive] [rU.Additive]
    [PreservesFiniteLimits PA] [PreservesFiniteColimits PA]
    [PreservesFiniteLimits PE] [PreservesFiniteColimits PE]
    [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
    [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
    (DP : DerivedCategory A ⥤ DerivedCategory B)
    (DFT : DerivedCategory B ⥤ DerivedCategory D)
    (DFU : DerivedCategory A ⥤ DerivedCategory C)
    (α : DP ⋙ DFT ≅ DFU ⋙ PE.mapDerivedCategory)
    (αc : P.mapHomologicalComplex (.up ℤ) ⋙ FT.mapHomologicalComplex (.up ℤ) ≅
      FU.mapHomologicalComplex (.up ℤ) ⋙ PE.mapHomologicalComplex (.up ℤ))
    (e₀ : P ≅ PA) (e : DP ≅ PA.mapDerivedCategory)
    (b₀ : rU ⋙ PA ⟶ PE ⋙ rT)
    (b : PE.mapDerivedCategory ⋙ rT.mapDerivedCategory ≅
      rU.mapDerivedCategory ⋙ PA.mapDerivedCategory)
    (jT : 𝟭 B ⟶ FT ⋙ rT) (jU : 𝟭 A ⟶ FU ⋙ rU)
    (ηT : 𝟭 (DerivedCategory B) ⟶ DFT ⋙ rT.mapDerivedCategory)
    (ηU : 𝟭 (DerivedCategory A) ⟶ DFU ⋙ rU.mapDerivedCategory)
    (cp : DerivedCategory.Q ⋙ DP ⟶
      P.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δT : ∀ L : CochainComplex B ℤ, DFT.obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj ((FT.mapHomologicalComplex (.up ℤ)).obj L))
    (δU : ∀ L : CochainComplex A ℤ, DFU.obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj ((FU.mapHomologicalComplex (.up ℤ)).obj L))
    (K : CochainComplex A ℤ) [IsIso (δU K)]
    (hc : α.hom.app (DerivedCategory.Q.obj K) ≫ PE.mapDerivedCategory.map (δU K) ≫
      PE.mapDerivedCategoryFactors.hom.app ((FU.mapHomologicalComplex (.up ℤ)).obj K) =
      DFT.map (cp.app K) ≫ δT ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (αc.hom.app K))
    (hT : ηT.app (DerivedCategory.Q.obj ((P.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      rT.mapDerivedCategory.map (δT ((P.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      rT.mapDerivedCategoryFactors.hom.app
        ((FT.mapHomologicalComplex (.up ℤ)).obj ((P.mapHomologicalComplex (.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex jT (.up ℤ)).app
        ((P.mapHomologicalComplex (.up ℤ)).obj K)))
    (hU : ηU.app (DerivedCategory.Q.obj K) ≫ rU.mapDerivedCategory.map (δU K) ≫
      rU.mapDerivedCategoryFactors.hom.app ((FU.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex jU (.up ℤ)).app K))
    (hb : b.inv.app (DerivedCategory.Q.obj ((FU.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      rT.mapDerivedCategory.map (PE.mapDerivedCategoryFactors.hom.app
        ((FU.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      rT.mapDerivedCategoryFactors.hom.app ((PE.mapHomologicalComplex (.up ℤ)).obj
        ((FU.mapHomologicalComplex (.up ℤ)).obj K)) =
      PA.mapDerivedCategory.map (rU.mapDerivedCategoryFactors.hom.app
        ((FU.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      PA.mapDerivedCategoryFactors.hom.app ((rU.mapHomologicalComplex (.up ℤ)).obj
        ((FU.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b₀ (.up ℤ)).app
        ((FU.mapHomologicalComplex (.up ℤ)).obj K)))
    (hec : e.hom.app (DerivedCategory.Q.obj ((rU.mapHomologicalComplex (.up ℤ)).obj
        ((FU.mapHomologicalComplex (.up ℤ)).obj K))) ≫
      PA.mapDerivedCategoryFactors.hom.app _ = cp.app _ ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app _))
    (hterm : (NatTrans.mapHomologicalComplex jT (.up ℤ)).app
        ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (rT.mapHomologicalComplex (.up ℤ)).map (αc.hom.app K) =
      (P.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex jU (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app
        ((rU.mapHomologicalComplex (.up ℤ)).obj ((FU.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      (NatTrans.mapHomologicalComplex b₀ (.up ℤ)).app
        ((FU.mapHomologicalComplex (.up ℤ)).obj K)) :
    ηT.app (DP.obj (DerivedCategory.Q.obj K)) ≫
        rT.mapDerivedCategory.map (α.hom.app (DerivedCategory.Q.obj K)) =
      DP.map (ηU.app (DerivedCategory.Q.obj K)) ≫
        e.hom.app (rU.mapDerivedCategory.obj (DFU.obj (DerivedCategory.Q.obj K))) ≫
        b.inv.app (DFU.obj (DerivedCategory.Q.obj K)) := by
  let DT := rT.mapDerivedCategory
  let DU := rU.mapDerivedCategory
  let DPA := PA.mapDerivedCategory
  let DPE := PE.mapDerivedCategory
  let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
  let FUK := (FU.mapHomologicalComplex (.up ℤ)).obj K
  let PEK := (PE.mapHomologicalComplex (.up ℤ)).obj FUK
  let t := DT.map (DPE.map (δU K)) ≫
    DT.map (PE.mapDerivedCategoryFactors.hom.app FUK) ≫
    rT.mapDerivedCategoryFactors.hom.app PEK
  apply (cancel_mono t).1
  have hl : (ηT.app (DP.obj (DerivedCategory.Q.obj K)) ≫
      DT.map (α.hom.app (DerivedCategory.Q.obj K))) ≫ t =
    cp.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex jT (.up ℤ)).app PK ≫
        (rT.mapHomologicalComplex (.up ℤ)).map (αc.hom.app K)) := by
    have h := leftFactor DFT DT DerivedCategory.Q
      (rT.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ηT
      rT.mapDerivedCategoryFactors.hom (cp.app K)
      (α.hom.app (DerivedCategory.Q.obj K))
      (DPE.map (δU K) ≫ PE.mapDerivedCategoryFactors.hom.app FUK)
      (δT PK) (αc.hom.app K)
      (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex jT (.up ℤ)).app PK))
      hc hT
    have hm := DerivedCategory.Q.map_comp
      ((NatTrans.mapHomologicalComplex jT (.up ℤ)).app PK)
      ((rT.mapHomologicalComplex (.up ℤ)).map (αc.hom.app K))
    have h := h.trans (congrArg (cp.app K ≫ ·) hm.symm)
    dsimp only [t]
    have hm := congrArg
      (fun z ↦ (ηT.app (DP.obj (DerivedCategory.Q.obj K)) ≫
        DT.map (α.hom.app (DerivedCategory.Q.obj K))) ≫
        z ≫ rT.mapDerivedCategoryFactors.hom.app PEK)
      (DT.map_comp (DPE.map (δU K))
        (PE.mapDerivedCategoryFactors.hom.app FUK))
    exact (congrArg
      ((ηT.app (DP.obj (DerivedCategory.Q.obj K)) ≫
        DT.map (α.hom.app (DerivedCategory.Q.obj K))) ≫ ·)
      (Category.assoc _ _ _).symm).trans (hm.symm.trans h)
  have hr : (DP.map (ηU.app (DerivedCategory.Q.obj K)) ≫
      e.hom.app _ ≫ b.inv.app _) ≫ t =
    cp.app K ≫ DerivedCategory.Q.map
      ((P.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex jU (.up ℤ)).app K) ≫
        (NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app
          ((rU.mapHomologicalComplex (.up ℤ)).obj FUK) ≫
        (NatTrans.mapHomologicalComplex b₀ (.up ℤ)).app FUK) := by
    have h := rightFactor DP DPA DPE DU DT e b
      (ηU.app (DerivedCategory.Q.obj K)) (δU K)
      (rU.mapDerivedCategoryFactors.hom.app FUK)
      (PA.mapDerivedCategoryFactors.hom.app _)
      (DT.map (PE.mapDerivedCategoryFactors.hom.app FUK) ≫
        rT.mapDerivedCategoryFactors.hom.app PEK)
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b₀ (.up ℤ)).app FUK))
      (cp.app _) (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app _)) hb hec
    rw [hU] at h
    exact h.trans (computationNaturality DerivedCategory.Q DP
      (P.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q cp
      ((NatTrans.mapHomologicalComplex jU (.up ℤ)).app K)
      ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app
        ((rU.mapHomologicalComplex (.up ℤ)).obj FUK))
      ((NatTrans.mapHomologicalComplex b₀ (.up ℤ)).app FUK))
  exact hl.trans ((congrArg (fun z ↦ cp.app K ≫ DerivedCategory.Q.map z) hterm).trans hr.symm)

attribute [local irreducible] pbcScalarAdjunction
  pbcDerivedScalarAdjunction pbcActualDerivedAdjunction pbcActualModuleAdjunction
  proEtaleRingDerivedAdjunction proEtaleRingModuleAdjunction Adjunction.leftAdjointUniq
  proEtaleRingRestrictionPullbackInv
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The ordinary scalar comparison preserves the scalar unit after the canonical
coefficient-restriction comparison and the canonical ordinary-pull coordinate change.
Source: Stacks, Tags 03D2, 03CZ, 0D6D and 07A6; Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-realization-ordinary-pull-scalar-unit)

Proof: write F and r for scalar extension and restriction, P for ordinary integral
pullback, and P_E for rational pullback. At module level the comparison sends
1 tensor pull(m) to pull(1 tensor m), by module_unit. The scalar units are exactly
m mapping to 1 tensor m, by sT.tensor_unit and sU.tensor_unit. Apply the normalized
module geometric adjunction to this equation; its bijectivity identifies the two
maps from P(M). The inverse restriction comparison b is the adjunct of the
identity-on-sections direct-image comparison, so this gives j_T followed by
r_T(moduleComparison) = P(j_U) followed by b inverse, with the unique left-adjoint
identification inserted for the integral pullback.
Apply the identity in every degree of a complex. The scalar computation counits
are invertible on every complex by sT.computes and sU.computes; their unit equations
are sT.unit and sU.unit. Ordinary pullback is exact because its coefficient map is
an isomorphism. Its universal left-derived pair therefore identifies with termwise
pullback; uniqueness of derived adjoints makes this identification the displayed
leftAdjointUniq, since both use the same actual direct image. Substitute these
factorizations into a.derived_normalization and use a.complex_terms. The termwise
module-unit equation, naturality, and cancellation of the invertible computation
maps give the displayed equation at Q(P). Every ambient derived object is isomorphic
to such a Q(P); naturality transports the equation. No boundedness, constructibility,
or completeness of this object is used. -/
theorem realizationOrdinaryPull_scalarUnit
    (a : RealizationCompletedPullArrow T U f sT sU)
    (N : PbcCompletedDerived U.scheme (pbcIntegralDatum l E)) :
    (pbcDerivedScalarAdjunction (realizationPullScalarMap l E sT)).unit.app
        ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj N) ≫
      (pbcDerivedRestrict (realizationPullScalarMap l E sT)).map
        (a.ordinaryComparison.hom.app N) =
    (pbcActualDerivedPull f (pbcIntegralDatum l E)).map
        ((pbcDerivedScalarAdjunction (realizationPullScalarMap l E sU)).unit.app N) ≫
      ((pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).leftAdjointUniq
        (proEtaleRingDerivedAdjunction f _ _
          (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
            a.coefficient_isIso))).hom.app
          ((pbcDerivedRestrict (realizationPullScalarMap l E sU)).obj
            ((pbcDerivedExtend (realizationPullScalarMap l E sU)).obj N)) ≫
      (proEtaleRingRestrictionDerivedPullback f
        (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
        (rationalCoefficientSheaf l U.scheme E)
        (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
        (rationalCoefficientSheaf l T.scheme E)
        (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
        (@asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
          a.coefficient_isIso) a.rationalCoefficient a.coefficient_square.symm).inv.app
            ((pbcDerivedExtend (realizationPullScalarMap l E sU)).obj N) := by
  let aT := realizationPullScalarMap l E sT
  let aU := realizationPullScalarMap l E sU
  let rT := pbcRestrict aT
  let rU := pbcRestrict aU
  let FT := pbcExtend aT
  let FU := pbcExtend aU
  let DFT := pbcDerivedExtend aT
  let DFU := pbcDerivedExtend aU
  let DT := rT.mapDerivedCategory
  let DU := rU.mapDerivedCategory
  let P := pbcActualModulePull f (pbcIntegralDatum l E)
  let DP := pbcActualDerivedPull f (pbcIntegralDatum l E)
  let cA := @asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E))
    a.coefficient_isIso
  let PA := proEtaleRingModulePullback f _ _ cA
  let PE := proEtaleRingModulePullback f _ _ a.rationalCoefficient
  let DPA := proEtaleRingDerivedPullback f _ _ cA
  let DPE := proEtaleRingDerivedPullback f _ _ a.rationalCoefficient
  let e₀ : P ≅ PA := moduleCoordinate a
  let e : DP ≅ DPA := derivedCoordinate a
  let b₀ : rU ⋙ PA ⟶ PE ⋙ rT := proEtaleRingRestrictionPullbackInv f
    (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l U.scheme E)
    (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l T.scheme E) aU aT cA a.rationalCoefficient
    a.coefficient_square.symm
  let b : DPE ⋙ DT ≅ DU ⋙ DPA := proEtaleRingRestrictionDerivedPullback f
    (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l U.scheme E)
    (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
    (rationalCoefficientSheaf l T.scheme E) aU aT cA a.rationalCoefficient
    a.coefficient_square.symm
  let α : DP ⋙ DFT ≅ DFU ⋙ DPE := a.ordinaryComparison
  let αc : P.mapHomologicalComplex (.up ℤ) ⋙ FT.mapHomologicalComplex (.up ℤ) ≅
      FU.mapHomologicalComplex (.up ℤ) ⋙ PE.mapHomologicalComplex (.up ℤ) :=
    a.complexComparison
  let ηT : 𝟭 (PbcCompletedDerived T.scheme (pbcIntegralDatum l E)) ⟶ DFT ⋙ DT :=
    (pbcDerivedScalarAdjunction aT).unit
  let ηU : 𝟭 (PbcCompletedDerived U.scheme (pbcIntegralDatum l E)) ⟶ DFU ⋙ DU :=
    (pbcDerivedScalarAdjunction aU).unit
  let x : DP ⟶ DFU ⋙ DPE ⋙ DT :=
    Functor.whiskerLeft DP ηT ≫ Functor.whiskerRight α.hom DT
  let y : DP ⟶ DFU ⋙ DPE ⋙ DT :=
    Functor.whiskerRight ηU DP ≫ Functor.whiskerLeft (DFU ⋙ DU) e.hom ≫
      Functor.whiskerLeft DFU b.inv
  have hxy : x = y := by
    as_aux_lemma =>
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (.up ℤ))
      intro K
      let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
      let FUK := (FU.mapHomologicalComplex (.up ℤ)).obj K
      let PEK := (PE.mapHomologicalComplex (.up ℤ)).obj FUK
      have hu : IsIso (pbcComplexCounit aU K) := by
        unfold aU realizationPullScalarMap
        exact sU.computes K
      have hc : α.hom.app (DerivedCategory.Q.obj K) ≫
          DPE.map (pbcComplexCounit aU K) ≫ PE.mapDerivedCategoryFactors.hom.app FUK =
        DFT.map (pbcActualPullComplexCounit f (pbcIntegralDatum l E) K) ≫
          pbcComplexCounit aT PK ≫ DerivedCategory.Q.map (αc.hom.app K) :=
        a.derived_normalization K
      have hT : ηT.app (DerivedCategory.Q.obj PK) ≫
          DT.map (pbcComplexCounit aT PK) ≫
          rT.mapDerivedCategoryFactors.hom.app
            ((FT.mapHomologicalComplex (.up ℤ)).obj PK) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction aT).unit (.up ℤ)).app PK) := by
        exact scalarUnit_named T sT PK
      have hU : ηU.app (DerivedCategory.Q.obj K) ≫
          DU.map (pbcComplexCounit aU K) ≫
          rU.mapDerivedCategoryFactors.hom.app FUK =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction aU).unit (.up ℤ)).app K) := by
        exact scalarUnit_named U sU K
      let cp : DerivedCategory.Q ⋙ DP ⟶
          P.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
        Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv DP ≫
          Functor.whiskerLeft (HomotopyCategory.quotient _ _)
            (pbcActualPullCounit f (pbcIntegralDatum l E)) ≫
          Functor.whiskerRight (P.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
          Functor.whiskerLeft (P.mapHomologicalComplex (.up ℤ))
            (DerivedCategory.quotientCompQhIso _).hom
      have hb : b.inv.app (DerivedCategory.Q.obj FUK) ≫
          DT.map (PE.mapDerivedCategoryFactors.hom.app FUK) ≫
          rT.mapDerivedCategoryFactors.hom.app PEK =
        DPA.map (rU.mapDerivedCategoryFactors.hom.app FUK) ≫
          PA.mapDerivedCategoryFactors.hom.app
            ((rU.mapHomologicalComplex (.up ℤ)).obj FUK) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b₀ (.up ℤ)).app FUK) := by
        have : IsIso b₀ := proEtaleRingRestrictionPullbackInv_isIso f _ _ _ _
          aU aT cA a.rationalCoefficient a.coefficient_square.symm
        change ((Functor.mapDerivedCategoryCompIso PE rT).symm ≪≫
            Functor.mapDerivedCategoryNatIso (asIso b₀).symm ≪≫
            Functor.mapDerivedCategoryCompIso rU PA).inv.app _ ≫ _ = _
        exact squareInv_fac (asIso b₀) FUK
      have hec := ordinaryPull_coordinate_computation a
        ((rU.mapHomologicalComplex (.up ℤ)).obj FUK)
      change e.hom.app (DerivedCategory.Q.obj
          ((rU.mapHomologicalComplex (.up ℤ)).obj FUK)) ≫
          PA.mapDerivedCategoryFactors.hom.app _ = cp.app _ ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app _) at hec
      have hterm : (NatTrans.mapHomologicalComplex
            (pbcScalarAdjunction aT).unit (.up ℤ)).app PK ≫
          (rT.mapHomologicalComplex (.up ℤ)).map (αc.hom.app K) =
        (P.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction aU).unit (.up ℤ)).app K) ≫
          (NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app
            ((rU.mapHomologicalComplex (.up ℤ)).obj FUK) ≫
          (NatTrans.mapHomologicalComplex b₀ (.up ℤ)).app FUK := by
        ext n : 1
        change (pbcScalarAdjunction aT).unit.app (P.obj (K.X n)) ≫
            rT.map ((αc.hom.app K).f n) =
          P.map ((pbcScalarAdjunction aU).unit.app (K.X n)) ≫
            e₀.hom.app (rU.obj (FU.obj (K.X n))) ≫ b₀.app (FU.obj (K.X n))
        change _ ≫ rT.map ((a.complexComparison.hom.app K).f n) = _
        rw [a.complex_terms]
        exact ordinaryModule_scalarUnit a (K.X n)
      exact unitSquare_computations P PA PE FT FU rT rU DP DFT DFU α αc e₀ e b₀ b
        (pbcScalarAdjunction aT).unit (pbcScalarAdjunction aU).unit ηT ηU cp
        (pbcComplexCounit aT) (pbcComplexCounit aU) K hc hT hU hb hec hterm
  have hn := congr_app hxy N
  dsimp only [x, y, e, derivedCoordinate, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn
  dsimp only [DP, DFU, DPE, DT, DU, rT, rU, aT, aU, ηT, ηU, α, b, cA,
    pbcDerivedRestrict] at hn ⊢
  unfold derivedCoordinate at hn
  dsimp only [Functor.comp_obj] at hn
  exact hn

end WeilConjectures
