/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison

import all Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.Paper.BoundedConstructibleTower
import all Sheaf.SecSmoothPurity.ConstantScalarPullbackSquare
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Coefficient cocycle for the ambient direct-image mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md, Step 4; Stacks Tags 07A7 and 0E47
(blueprint: lem-sp-proetale-direct-image-scalar-cocycle).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
  SheafOfModules.SuccessiveDerivedQuotient.pure
  Scheme.completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Scheme.proEtaleRingModulePullback
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDerivedAdjunction

private abbrev coefficientPresentation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    SheafOfModules.SuccessiveDerivedQuotient.Presentation.{u + 1, u, u + 1, u + 2}
      (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R) a where
  ordinary := reductionChange T a
  obj_eq := reductionChange_obj_eq T a
  map_eq := reductionChange_map_eq T a
  additive := reductionChangeAdditive T a
  derived := reductionDerivedChange T a
  counit := reductionDerivedCounit T a
  universal := reductionDerivedUniversal T a

private theorem coefficient_tensor (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : proEtaleRingModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
      (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R)
      (coefficientPresentation.{u} T a) M U s x = reductionTensorSection T a M U s x := by
  unfold SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
    SheafOfModules.SuccessiveDerivedQuotient.pure reductionTensorSection
  rfl

private theorem quotient_hom_identity {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (P : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app P = 𝟙 _ := rfl

private theorem quotient_inv_identity {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (P : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).inv.app P = 𝟙 _ := rfl

private theorem homotopy_factor_hom {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (P : CochainComplex C ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl

private theorem homotopy_factor_inv {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (P : CochainComplex C ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl

private theorem quotient_map {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality f
  simp only [Functor.comp_map, quotient_hom_identity] at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h

private theorem derived_factor_hom {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, quotient_hom_identity,
    quotient_inv_identity, homotopy_factor_inv]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id]

private theorem complex_counit_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    reductionComplexCounit F L eps P =
      eps.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  dsimp only [reductionComplexCounit]
  rw [quotient_inv_identity, quotient_hom_identity, homotopy_factor_hom]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id]

private theorem hom_comparison_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (U : D ⥤ C) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (a : F ⊣ U) (d : L ⊣ U.mapDerivedCategory)
    (hd : ∀ (H : HomotopyCategory C (.up ℤ)) (K : HomotopyCategory D (.up ℤ))
      (f : (F.mapHomotopyCategory (.up ℤ)).obj H ⟶ K),
      d.homEquiv _ _ (eps.app H ≫ DerivedCategory.Qh.map f) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv H K f) ≫
          U.mapDerivedCategoryFactorsh.inv.app K)
    (P : CochainComplex C ℤ) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
        U.mapDerivedCategory.map (reductionComplexCounit F L eps P) ≫
        U.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P) := by
  let H := (HomotopyCategory.quotient C (.up ℤ)).obj P
  have hp := hd H ((F.mapHomotopyCategory (.up ℤ)).obj H) (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at hp
  rw [Adjunction.homEquiv_unit] at hp
  have hp' := congrArg (fun f ↦ f ≫ U.mapDerivedCategoryFactorsh.hom.app _) hp
  simp only [Category.assoc, Iso.inv_hom_id_app] at hp'
  erw [Category.comp_id] at hp'
  have heps : reductionComplexCounit F L eps P = eps.app H := by
    dsimp only [reductionComplexCounit]
    rw [quotient_inv_identity, quotient_hom_identity, homotopy_factor_hom]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id, Category.comp_id]
  rw [heps]
  have hh := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ) a P
  erw [hh] at hp'
  change d.unit.app (DerivedCategory.Q.obj P) ≫ U.mapDerivedCategory.map (eps.app H) ≫
    U.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) = _ at hp'
  erw [derived_factor_hom, quotient_map] at hp'
  exact hp'

private theorem coefficient_hom (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (H : HomotopyCategory (proEtaleRingModules T R) (.up ℤ))
    (K : HomotopyCategory (proEtaleRingModules T S) (.up ℤ))
    (f : ((reductionChange T a).mapHomotopyCategory (.up ℤ)).obj H ⟶ K) :
    (proEtaleRingDerivedExtensionAdjunction a).homEquiv _ _
        ((reductionDerivedCounit T a).app H ≫ DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map
          (((pbcScalarAdjunction.{u} a).mapHomotopyCategory (.up ℤ)).homEquiv H K f) ≫
        (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.{u + 2, u + 2}.inv.app K := by
  obtain ⟨d, hd⟩ := @SheafOfModules.sheafRingDerivedHomComparison.{u + 2, u + 1, u + 1, u}
    T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (ProEt.topology T) inferInstance inferInstance inferInstance R S a
    (proEtaleRingModules_hasDerivedCategory T R)
    (proEtaleRingModules_hasDerivedCategory T S) inferInstance inferInstance
    (reductionChange T a) (fun M ↦ reductionChange_obj_eq T a M)
    (fun {M N} f ↦ reductionChange_map_eq T a f) inferInstance
    (pbcScalarAdjunction.{u} a) (reductionDerivedChange T a) (reductionDerivedCounit T a)
    (reductionDerivedUniversal T a)
  have he : d = pbcDerivedScalarAdjunction a := by
    apply (pbcDerivedScalarAdjunction_exists a).unique
    · intro P hP
      exact hom_comparison_unit (reductionChange T a) (proEtaleRingRestrictScalars a)
        (reductionDerivedChange T a) (reductionDerivedCounit T a)
        (pbcScalarAdjunction.{u} a) d hd P
    · exact (pbcDerivedScalarAdjunction_exists a).exists.choose_spec
  rw [he] at hd
  exact hd H K f

private noncomputable def coefficientAdjData (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    @SheafOfModules.SuccessiveDerivedQuotient.AdjData.{u + 1, u, u + 1, u + 2}
      T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (ProEt.topology T) inferInstance inferInstance inferInstance
      (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) R S a
      (coefficientPresentation.{u} T a) := by
  refine @SheafOfModules.SuccessiveDerivedQuotient.AdjData.mk.{u + 1, u, u + 1, u + 2}
    T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (ProEt.topology T) inferInstance inferInstance inferInstance
    (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) R S a
    (coefficientPresentation.{u} T a) ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 => exact pbcScalarAdjunction.{u} a
  case refine_2 =>
    intro M U x
    change ((pbcScalarAdjunction.{u} a).unit.app M).val.app U x =
      SheafOfModules.SuccessiveDerivedQuotient.sectionTensor.{u + 1, u, u + 1, u + 2}
        (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R)
        (coefficientPresentation.{u} T a) M U 1 x
    rw [coefficient_tensor.{u}]
    exact (pbcScalarAdjunction_exists.{u} a).exists.choose_spec M U x
  case refine_3 => exact proEtaleRingDerivedExtensionAdjunction a
  case refine_4 => exact fun P hP _ ↦ pbcExtensionCounit_isIso.{u} a P hP
  case refine_6 => exact coefficient_hom T a
  case refine_5 =>
    intro P hP hf
    have h := coefficient_hom.{u} T a ((HomotopyCategory.quotient _ _).obj P)
      (((reductionChange T a).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at h
    rw [Adjunction.homEquiv_unit] at h
    have h' := congrArg (fun f ↦ f ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.{u + 2, u + 2}.hom.app _) h
    simp only [Category.assoc, Iso.inv_hom_id_app] at h'
    erw [Category.comp_id] at h'
    exact h'

private theorem coefficient_adj_ordinary (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    @SheafOfModules.SuccessiveDerivedQuotient.AdjData.ordinary.{u + 1, u, u + 1, u + 2}
      T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (ProEt.topology T) inferInstance inferInstance inferInstance
      (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) R S a
      (coefficientPresentation T a) (coefficientAdjData T a) = pbcScalarAdjunction a := rfl

private theorem coefficient_adj_derived (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    @SheafOfModules.SuccessiveDerivedQuotient.AdjData.derived.{u + 1, u, u + 1, u + 2}
      T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (ProEt.topology T) inferInstance inferInstance inferInstance
      (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) R S a
      (coefficientPresentation T a) (coefficientAdjData T a) =
      proEtaleRingDerivedExtensionAdjunction a := rfl

attribute [local irreducible] coefficientAdjData

private theorem coefficient_restriction_comp (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) :
    SheafOfModules.SuccessiveDerivedQuotient.resComp.{u + 1, u, u + 1} a b =
      pbcRestrictComp a b (a ≫ b) rfl := by
  apply (pbcRestrictComp_exists a b (a ≫ b) rfl).unique
  · intros
    rfl
  · exact (pbcRestrictComp_exists a b (a ≫ b) rfl).exists.choose_spec

private theorem coefficient_unit (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : proEtaleRingModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction a).unit.app M).val.app U x =
      SheafOfModules.SuccessiveDerivedQuotient.sectionTensor.{u + 1, u, u + 1, u + 2}
        (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R)
        (coefficientPresentation T a) M U 1 x := by
  rw [coefficient_tensor]
  exact (pbcScalarAdjunction_exists a).exists.choose_spec M U x

private theorem coefficient_right_comp (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) :
    @SheafOfModules.SuccessiveDerivedQuotient.rightComp.{u + 1, u, u + 1, u + 2}
      T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (ProEt.topology T) inferInstance inferInstance inferInstance
      (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) R S V a b =
      pbcDerivedRestrictComp.{u} a b (a ≫ b) rfl := by
  unfold SheafOfModules.SuccessiveDerivedQuotient.rightComp pbcDerivedRestrictComp
  rw [coefficient_restriction_comp.{u} T a b]

attribute [local irreducible] pbcScalarAdjunction pbcDerivedScalarAdjunction
  Adjunction.leftAdjointCompIso SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp
  pbcDerivedRestrictComp

private theorem coefficient_balance (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (P : CochainComplex (proEtaleRingModules T R) ℤ) :
    let p := fun {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) ↦
      coefficientPresentation T a
    let A : ∀ {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S),
        (p a).ordinary ⊣ proEtaleRingRestrictScalars (T := T) a :=
      fun a ↦ pbcScalarAdjunction a
    (NatTrans.mapHomologicalComplex
      (SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp.{u + 1, u, u + 1, u + 2}
          (C := T.ProEt) (J := ProEt.topology T)
          (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p A a b).hom (.up ℤ)).app P =
      reductionBalance T a b (a ≫ b) rfl P := by
  dsimp only
  let p := fun {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) ↦
    coefficientPresentation T a
  let A : ∀ {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S),
      (p a).ordinary ⊣ proEtaleRingRestrictScalars (T := T) a :=
    fun a ↦ pbcScalarAdjunction a
  apply (reductionBalance_exists T a b (a ≫ b) rfl P).unique
  · refine ⟨?_, ?_⟩
    · exact inferInstanceAs (IsIso
        ((NatIso.mapHomologicalComplex
          (SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp.{u + 1, u, u + 1, u + 2}
            (C := T.ProEt) (J := ProEt.topology T)
            (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p A a b)
          (.up ℤ)).hom.app P))
    · intro i U s r x
      have hu :=
        @SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp_hom.{u + 1, u, u + 1, u + 2}
        T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (ProEt.topology T) inferInstance inferInstance inferInstance
        (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p A
        (fun a M U x ↦ coefficient_unit T a M U x) R S V a b (P.X i) U x r s
      simp only [p, coefficient_tensor.{u}, mul_comm, CommRingCat.Hom.hom,
        NatTrans.mapHomologicalComplex_app_f, reductionChangeComplex,
        Functor.mapHomologicalComplex_obj_X] at hu ⊢
      convert hu using 1
      rfl
  · exact (reductionBalance_exists T a b (a ≫ b) rfl P).exists.choose_spec

private theorem coefficient_composition_computation (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (P : CochainComplex (proEtaleRingModules T R) ℤ) :
    (Adjunction.leftAdjointCompIso (proEtaleRingDerivedExtensionAdjunction a)
      (proEtaleRingDerivedExtensionAdjunction b) (proEtaleRingDerivedExtensionAdjunction c)
      (pbcDerivedRestrictComp a b c h)).hom.app (DerivedCategory.Q.obj P) ≫
        reductionScalarComplexCounit T c P =
      (reductionDerivedChange T b).map (reductionScalarComplexCounit T a P) ≫
        reductionScalarComplexCounit T b ((reductionChangeComplex T a).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T a b c h P) := by
  subst c
  let p := fun {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) ↦
    coefficientPresentation.{u} T a
  let D := fun {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) ↦
    coefficientAdjData.{u} T a
  let A : ∀ {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S),
      (p a).ordinary ⊣ proEtaleRingRestrictScalars (T := T) a :=
    fun a ↦ pbcScalarAdjunction.{u} a
  have he := coefficient_right_comp T a b
  have hb := coefficient_balance T a b P
  have hr :=
    @SheafOfModules.SuccessiveDerivedQuotient.derivedComp_representative.{u + 1, u, u + 1, u + 2}
    T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (ProEt.topology T) inferInstance inferInstance inferInstance
    (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p D R S V a b
    ((HomotopyCategory.quotient _ _).obj P)
  have hcomp :=
    @SheafOfModules.SuccessiveDerivedQuotient.derivedComp_eq.{u + 1, u, u + 1, u + 2}
    T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (ProEt.topology T) inferInstance inferInstance inferInstance
    (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p D R S V a b
  rw [hcomp, he] at hr
  dsimp only [reductionScalarComplexCounit]
  rw [complex_counit_eq, complex_counit_eq, complex_counit_eq]
  have hh : (Functor.mapHomotopyCategoryCompIso
      (SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp.{u + 1, u, u + 1, u + 2}
          (C := T.ProEt) (J := ProEt.topology T)
          (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p A a b) (.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj P) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex
          (SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp.{u + 1, u, u + 1, u + 2}
          (C := T.ProEt) (J := ProEt.topology T)
          (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p A a b).hom
          (.up ℤ)).app P) := rfl
  have hOrd :
      SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp.{u + 1, u, u + 1, u + 2}
        (C := T.ProEt) (J := ProEt.topology T)
        (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R)
        p (fun {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) ↦
          @SheafOfModules.SuccessiveDerivedQuotient.AdjData.ordinary.{u + 1, u, u + 1, u + 2}
            T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
            (ProEt.topology T) inferInstance inferInstance inferInstance
            (fun R ↦ proEtaleRingModules_hasDerivedCategory T R) R S a (p a) (D a)) a b =
      SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp.{u + 1, u, u + 1, u + 2}
        (C := T.ProEt) (J := ProEt.topology T)
        (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R) p A a b := by
    dsimp only [D]
    simp only [coefficient_adj_ordinary]
    rfl
  rw [hOrd, hh, hb, quotient_map] at hr
  dsimp only [D] at hr
  simp only [coefficient_adj_derived] at hr
  exact hr

attribute [local semireducible] pbcDerivedRestrictComp Adjunction.leftAdjointCompIso
  SheafOfModules.SuccessiveDerivedQuotient.ordinaryComp

private theorem scalar_associator_normalized
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) (T : Scheme.{u}) :
    scalarExtensionFunctor_composition a b T =
      Adjunction.leftAdjointCompIso
        (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) a))
        (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) b))
        (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) (b.comp a)))
        (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp a b T)) := by
  apply (scalarExtensionFunctor_composition_existsUnique a b T).unique
  · exact (scalarExtensionFunctor_composition_existsUnique a b T).exists.choose_spec
  · intro P hP
    exact coefficient_composition_computation T _ _ _ _ P

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {G G' : C ⥤ E} {H : D ⥤ F}
    (w : TwoSquare G' L L' H) (t : G ⟶ G') :
    mateEquiv a b (w.whiskerTop t) = (mateEquiv a b w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a b w t (𝟙 H)

private theorem mate_whisker_bottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {G : C ⥤ E} {H H' : D ⥤ F}
    (w : TwoSquare G L L' H) (t : H ⟶ H') :
    mateEquiv a b (w.whiskerBottom t) = (mateEquiv a b w).whiskerLeft t := by
  simpa [TwoSquare.whiskerTop, TwoSquare.whiskerRight] using
    mateEquiv_whiskerTop_whiskerBottom a b w (𝟙 G) t

private abbrev scalar_restriction (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) :=
  proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) a)

private abbrev scalar_restriction_comp (T : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) :=
  pbcRestrictComp (proEtaleConstantRingMap (T := T) a)
    (proEtaleConstantRingMap (T := T) b)
    (proEtaleConstantRingMap (T := T) (b.comp a))
    (scalarExtensionFunctor_ringMap_comp a b T)

private theorem scalar_restriction_comp_inv_apply (T : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((scalar_restriction_comp T a b).inv.app M).val.app U x = x := by
  let e := scalar_restriction_comp T a b
  have hh := (pbcRestrictComp_exists _ _ _
    (scalarExtensionFunctor_ringMap_comp a b T)).exists.choose_spec
  have hi := congrArg (fun f ↦ f.val.app U x) (e.inv_hom_id_app M)
  change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at hi
  exact (hh M U ((e.inv.app M).val.app U x)).symm.trans hi

private abbrev restriction_pullback
    {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B)
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) :=
  proEtaleRingRestrictionPullbackInv q
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) a) (proEtaleConstantRingMap (T := Z) a)
    (proEtaleConstantRingComparison q A) (proEtaleConstantRingComparison q B)
    (by
      simpa [proEtaleConstantRingComparison, proEtaleConstantRingMap] using
        (proEtaleConstantInverseImageMap_naturality q
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} a))).symm)

private abbrev restriction_pullback_iso
    {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B)
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) :=
  letI := proEtaleRingRestrictionPullbackInv_isIso
    q (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) a) (proEtaleConstantRingMap (T := Z) a)
    (proEtaleConstantRingComparison q A) (proEtaleConstantRingComparison q B)
    (DirectScalar.coeffSquare a q)
  asIso (restriction_pullback a q)

private theorem ordinary_coefficient_square
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    ((TwoSquare.mk _ _ _ _ (restriction_pullback b q)).hComp
      (TwoSquare.mk _ _ _ _ (restriction_pullback a q))).whiskerTop
        (scalar_restriction_comp Y a b).inv =
      (TwoSquare.mk _ _ _ _ (restriction_pullback (b.comp a) q)).whiskerBottom
        (scalar_restriction_comp Z a b).inv := by
  let adj (R : Type u) [CommRing R] := proEtaleConstantRingAdjunction R q
  apply (mateEquiv (adj C) (adj A)).injective
  rw [mate_whisker_top, mate_whisker_bottom,
    mateEquiv_vcomp (adj C) (adj B) (adj A)]
  have hm {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S) :
      mateEquiv (adj S) (adj R) (TwoSquare.mk _ _ _ _ (restriction_pullback c q)) =
        TwoSquare.mk _ _ _ _ (DirectScalar.directComparison c q).hom := by
    apply TwoSquare.ext
    intro N
    exact congr_app (restrictionPullback_mate q _ _ _ _ _ _ _ _
      (DirectScalar.coeffSquare c q)) N
  rw [hm, hm, hm]
  ext N U x
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  simp only [TwoSquare.mk, TwoSquare.natTrans]
  change ((DirectScalar.directComparison a q).hom.app
      ((scalar_restriction Z b).obj N)).val.app U
      (((DirectScalar.directComparison b q).hom.app N).val.app U
        (((scalar_restriction_comp Y a b).inv.app
          ((proEtaleConstantRingPushforward C q).obj N)).val.app U x)) =
    ((scalar_restriction_comp Z a b).inv.app N).val.app
      ((proEtaleBaseChange q).op.obj U)
      (((DirectScalar.directComparison (b.comp a) q).hom.app N).val.app U x)
  erw [scalar_restriction_comp_inv_apply, DirectScalar.directComparison_apply,
    DirectScalar.directComparison_apply, DirectScalar.directComparison_apply,
    scalar_restriction_comp_inv_apply]

private theorem scalar_mate_composition
    {CY CZ DY DZ EY EZ : Type*}
    [Category CY] [Category CZ] [Category DY] [Category DZ] [Category EY] [Category EZ]
    {aY : CY ⥤ DY} {raY : DY ⥤ CY} {aZ : CZ ⥤ DZ} {raZ : DZ ⥤ CZ}
    {bY : DY ⥤ EY} {rbY : EY ⥤ DY} {bZ : DZ ⥤ EZ} {rbZ : EZ ⥤ DZ}
    {cY : CY ⥤ EY} {rcY : EY ⥤ CY} {cZ : CZ ⥤ EZ} {rcZ : EZ ⥤ CZ}
    (aaY : aY ⊣ raY) (aaZ : aZ ⊣ raZ) (abY : bY ⊣ rbY) (abZ : bZ ⊣ rbZ)
    (acY : cY ⊣ rcY) (acZ : cZ ⊣ rcZ)
    {pA : CY ⥤ CZ} {pB : DY ⥤ DZ} {pC : EY ⥤ EZ}
    (qa : TwoSquare raY pB pA raZ) (qb : TwoSquare rbY pC pB rbZ)
    (qc : TwoSquare rcY pC pA rcZ)
    (rY : rbY ⋙ raY ≅ rcY) (rZ : rbZ ⋙ raZ ≅ rcZ)
    (h : (qb.hComp qa).whiskerTop rY.inv = qc.whiskerBottom rZ.inv) :
    let da := Adjunction.leftAdjointCompIso aaY abY acY rY
    let db := Adjunction.leftAdjointCompIso aaZ abZ acZ rZ
    let la := (mateEquiv aaY aaZ).symm qa
    let lb := (mateEquiv abY abZ).symm qb
    let lc := (mateEquiv acY acZ).symm qc
    (la.vComp lb).whiskerLeft da.hom = lc.whiskerRight db.hom := by
  dsimp only
  apply (mateEquiv acY (aaZ.comp abZ)).injective
  rw [conjugateEquiv_mateEquiv_vcomp acY (aaY.comp abY) (aaZ.comp abZ),
    mateEquiv_conjugateEquiv_vcomp acY acZ (aaZ.comp abZ)]
  have hdY : conjugateEquiv acY (aaY.comp abY)
      (Adjunction.leftAdjointCompIso aaY abY acY rY).hom = rY.inv := by
    dsimp only [Adjunction.leftAdjointCompIso, conjugateIsoEquiv]
    exact (conjugateEquiv acY (aaY.comp abY)).apply_symm_apply _
  have hdZ : conjugateEquiv acZ (aaZ.comp abZ)
      (Adjunction.leftAdjointCompIso aaZ abZ acZ rZ).hom = rZ.inv := by
    dsimp only [Adjunction.leftAdjointCompIso, conjugateIsoEquiv]
    exact (conjugateEquiv acZ (aaZ.comp abZ)).apply_symm_apply _
  rw [hdY, hdZ, mateEquiv_hcomp aaY aaZ abY abZ, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

private theorem derived_coefficient_square
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    let da := Functor.mapDerivedCategorySquareIso (restriction_pullback_iso a q)
    let db := Functor.mapDerivedCategorySquareIso (restriction_pullback_iso b q)
    let dc := Functor.mapDerivedCategorySquareIso (restriction_pullback_iso (b.comp a) q)
    let rY := pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp a b Y)
    let rZ := pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp a b Z)
    ((TwoSquare.mk _ _ _ _ db.hom).hComp
      (TwoSquare.mk _ _ _ _ da.hom)).whiskerTop rY.inv =
      (TwoSquare.mk _ _ _ _ dc.hom).whiskerBottom rZ.inv := by
  let qa := restriction_pullback_iso a q
  let qb := restriction_pullback_iso b q
  let qc := restriction_pullback_iso (b.comp a) q
  let rY := scalar_restriction_comp Y a b
  let rZ := scalar_restriction_comp Z a b
  have h (M : proEtaleRingModules Y (proEtaleConstantRing Y C)) :
      qc.inv.app M ≫ (proEtaleConstantRingPullback A q).map (rY.inv.app M) =
        rZ.inv.app ((proEtaleConstantRingPullback C q).obj M) ≫
          (scalar_restriction Z a).map (qb.inv.app M) ≫
          qa.inv.app ((scalar_restriction Y b).obj M) := by
    have ho := congr_app (congrArg TwoSquare.natTrans
      (ordinary_coefficient_square a b q)) M
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] at ho
    apply (cancel_epi (qc.hom.app M)).mp
    apply (cancel_mono (qa.hom.app ((scalar_restriction Y b).obj M) ≫
      (scalar_restriction Z a).map (qb.hom.app M))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact ho
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    qb.symm qa.symm qc.symm rZ.symm rY.symm h
  dsimp only
  ext M
  have hm := hd M
  let da := Functor.mapDerivedCategorySquareIso qa
  let db := Functor.mapDerivedCategorySquareIso qb
  let dc := Functor.mapDerivedCategorySquareIso qc
  let ry := pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp a b Y)
  let rz := pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp a b Z)
  have hsa : Functor.mapDerivedCategorySquareIso qa.symm = da.symm := by
    apply Iso.ext
    simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm, da]
  have hsb : Functor.mapDerivedCategorySquareIso qb.symm = db.symm := by
    apply Iso.ext
    simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm, db]
  have hsc : Functor.mapDerivedCategorySquareIso qc.symm = dc.symm := by
    apply Iso.ext
    simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm, dc]
  have hty : Functor.mapDerivedCategoryTriangleIso rY.symm = ry.symm := by
    apply Iso.ext
    simp [Functor.mapDerivedCategoryTriangleIso, ry, pbcDerivedRestrictComp, rY,
      scalar_restriction_comp, Functor.mapDerivedCategoryNatIso_symm]
  have htz : Functor.mapDerivedCategoryTriangleIso rZ.symm = rz.symm := by
    apply Iso.ext
    simp [Functor.mapDerivedCategoryTriangleIso, rz, pbcDerivedRestrictComp, rZ,
      scalar_restriction_comp, Functor.mapDerivedCategoryNatIso_symm]
  rw [hsa, hsb, hsc, hty, htz] at hm
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  change (proEtaleConstantRingDerivedPullback A q).map (ry.inv.app M) ≫
      da.hom.app ((scalar_restriction Y b).mapDerivedCategory.obj M) ≫
      (scalar_restriction Z a).mapDerivedCategory.map (db.hom.app M) =
    dc.hom.app M ≫ rz.inv.app ((proEtaleConstantRingDerivedPullback C q).obj M)
  apply (cancel_epi (dc.inv.app M)).mp
  apply (cancel_mono
    ((scalar_restriction Z a).mapDerivedCategory.map (db.inv.app M) ≫
      da.inv.app ((scalar_restriction Y b).mapDerivedCategory.obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [← (scalar_restriction Z a).mapDerivedCategory.map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
    Category.comp_id]
  exact hm

private theorem invertible_square
    {D : Type*} [Category D] {X Y Z W : D}
    (e : X ≅ Y) (i : Z ≅ W) (f : X ⟶ Z) (h : Y ⟶ W)
    (hh : e.inv ≫ f = h ≫ i.inv) : f ≫ i.hom = e.hom ≫ h := by
  apply (cancel_epi e.inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hh, Iso.inv_hom_id, Category.comp_id]

private theorem counit_cocycle
    {YA ZA YB ZB YC ZC : Type*}
    [Category YA] [Category ZA] [Category YB] [Category ZB] [Category YC] [Category ZC]
    {pA : YA ⥤ ZA} {gA : ZA ⥤ YA} {pB : YB ⥤ ZB} {gB : ZB ⥤ YB}
    {pC : YC ⥤ ZC} {gC : ZC ⥤ YC}
    (adA : pA ⊣ gA) (adB : pB ⊣ gB) (adC : pC ⊣ gC)
    {aY : YA ⥤ YB} {aZ : ZA ⥤ ZB} {bY : YB ⥤ YC} {bZ : ZB ⥤ ZC}
    {cY : YA ⥤ YC} {cZ : ZA ⥤ ZC}
    (alY : aY ⋙ bY ≅ cY) (alZ : aZ ⋙ bZ ≅ cZ)
    (la : aY ⋙ pB ≅ pA ⋙ aZ) (lb : bY ⋙ pC ≅ pB ⋙ bZ)
    (lc : cY ⋙ pC ≅ pA ⋙ cZ)
    (hc : ∀ N, pC.map (alY.hom.app N) ≫ lc.hom.app N =
      lb.hom.app (aY.obj N) ≫ bZ.map (la.hom.app N) ≫ alZ.hom.app (pA.obj N))
    (E : ZA) :
    alY.hom.app (gA.obj E) ≫ (mateEquiv adA adC (TwoSquare.mk _ _ _ _ lc.hom)).natTrans.app E =
      bY.map ((mateEquiv adA adB (TwoSquare.mk _ _ _ _ la.hom)).natTrans.app E) ≫
        (mateEquiv adB adC (TwoSquare.mk _ _ _ _ lb.hom)).natTrans.app (aZ.obj E) ≫
        gC.map (alZ.hom.app E) := by
  have ht {LY : YA ⥤ YC} {LZ : ZA ⥤ ZC} (l : LY ⋙ pC ≅ pA ⋙ LZ) (M : ZA) :
      pC.map ((mateEquiv adA adC (TwoSquare.mk _ _ _ _ l.hom)).natTrans.app M) ≫
          adC.counit.app (LZ.obj M) =
        l.hom.app (gA.obj M) ≫ LZ.map (adA.counit.app M) :=
    mateEquiv_counit adA adC (TwoSquare.mk _ _ _ _ l.hom) M
  have hta (M : ZA) :
      pB.map ((mateEquiv adA adB (TwoSquare.mk _ _ _ _ la.hom)).natTrans.app M) ≫
        adB.counit.app (aZ.obj M) =
      la.hom.app (gA.obj M) ≫ aZ.map (adA.counit.app M) :=
    mateEquiv_counit adA adB (TwoSquare.mk _ _ _ _ la.hom) M
  have htb (M : ZB) :
      pC.map ((mateEquiv adB adC (TwoSquare.mk _ _ _ _ lb.hom)).natTrans.app M) ≫
        adC.counit.app (bZ.obj M) =
      lb.hom.app (gB.obj M) ≫ bZ.map (adB.counit.app M) :=
    mateEquiv_counit adB adC (TwoSquare.mk _ _ _ _ lb.hom) M
  apply (adC.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [ht]
  rw [show pC.map (gC.map (alZ.hom.app E)) ≫ adC.counit.app _ =
      adC.counit.app _ ≫ alZ.hom.app E from adC.counit.naturality _]
  rw [reassoc_of% htb (aZ.obj E)]
  rw [reassoc_of% lb.hom.naturality
    ((mateEquiv adA adB (TwoSquare.mk _ _ _ _ la.hom)).natTrans.app E)]
  rw [← bZ.map_comp_assoc, hta, bZ.map_comp]
  have hn := alZ.hom.naturality (adA.counit.app E)
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [hn]
  rw [← reassoc_of% hc (gA.obj E)]

/-- The specified counit mates commute with successive scalar extension, naturally in E.
Source: blueprint direct-image proof Step 4; Stacks Tags 07A7 and 0E47
(blueprint: lem-sp-proetale-direct-image-scalar-cocycle).

Proof:
1. The universal derived Hom comparison identifies the scalar adjunction with the
specified tensor-unit normalization. SuccessiveDerivedQuotient's representative
formula then identifies its adjunction composition isomorphism with the specified
scalarExtensionFunctor_composition, using the ordinary balanced tensor formula.
2. The coefficient restriction/pullback squares compose: their geometric mates and
restriction associators are identity on underlying sections. Transport this identity
to derived categories using exact-functor square pasting.
3. Take the coefficient-adjunction mates of that identity. Composition of mates and
the normalization in step 1 give the scalar/pullback coherence equation for the
actual directImageScalarPullbackIso.
4. Transpose the claimed equation through the target geometric adjunction. The
counit formula for mates, naturality of the scalar/pullback maps and naturality of
scalar associativity reduce both composites to step 3. No properness, boundedness
or coefficient flatness is used. -/
theorem proEtaleDirectImageScalarCocycle
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (_hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (_hB : ∃ n : ℕ, ∀ b : B, (ℓ ^ n) • b = 0)
    (_hC : ∃ n : ℕ, ∀ c : C, (ℓ ^ n) • c = 0)
    (φ : A →+* B) (ψ : B →+* C)
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) (E : Scheme.proEtaleDerivedCategory Z A) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((directImageConstantPush A q).obj E) ≫
      (directImageScalarComparison (ψ.comp φ) q).app E =
    (scalarExtensionFunctor ψ Y).map ((directImageScalarComparison φ q).app E) ≫
      (directImageScalarComparison ψ q).app ((scalarExtensionFunctor φ Z).obj E) ≫
      (directImageConstantPush C q).map
        ((scalarExtensionFunctor_composition φ ψ Z).hom.app E) := by
  let P (R : Type u) [CommRing R] := Scheme.proEtaleConstantRingDerivedPullback R q
  let G (R : Type u) [CommRing R] := directImageConstantPush R q
  have hc (N : Scheme.proEtaleDerivedCategory Y A) :
      (P C).map ((scalarExtensionFunctor_composition φ ψ Y).hom.app N) ≫
          (directImageScalarPullbackIso (ψ.comp φ) q).hom.app N =
        (directImageScalarPullbackIso ψ q).hom.app ((scalarExtensionFunctor φ Y).obj N) ≫
          (scalarExtensionFunctor ψ Z).map ((directImageScalarPullbackIso φ q).hom.app N) ≫
          (scalarExtensionFunctor_composition φ ψ Z).hom.app ((P A).obj N) := by
    let aa (T : Scheme.{u}) {R S : Type u} [CommRing R] [CommRing S]
        (c : R →+* S) :=
      proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) c)
    let r (T : Scheme.{u}) := pbcDerivedRestrictComp _ _ _
      (scalarExtensionFunctor_ringMap_comp φ ψ T)
    let ds {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S) :=
      TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (restriction_pullback_iso c q)).hom
    have hi {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S) :
        ((mateEquiv (aa Y c) (aa Z c)).symm (ds c)).natTrans =
          (directImageScalarPullbackIso c q).inv := by
      dsimp only [ds, aa, directImageScalarPullbackIso, proEtaleReductionPullbackIso,
        Iso.symm_inv, asIso_hom, proEtaleReductionPullbackInv]
      congr 2
      change (Functor.mapDerivedCategorySquareIso (restriction_pullback_iso c q)).hom = _
      simp [Functor.mapDerivedCategorySquareIso, restriction_pullback_iso,
        proEtaleRingRestrictionDerivedPullback,
        Functor.mapDerivedCategoryNatIso_symm]
      rfl
    have hm := scalar_mate_composition (aa Y φ) (aa Z φ) (aa Y ψ) (aa Z ψ)
      (aa Y (ψ.comp φ)) (aa Z (ψ.comp φ)) (ds φ) (ds ψ) (ds (ψ.comp φ))
      (r Y) (r Z) (derived_coefficient_square φ ψ q)
    have hn := congr_app (congrArg TwoSquare.natTrans hm) N
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] at hn
    rw [hi, hi, hi, ← scalar_associator_normalized, ← scalar_associator_normalized] at hn
    change ((scalarExtensionFunctor ψ Z).map
        ((directImageScalarPullbackIso φ q).inv.app N) ≫
      (directImageScalarPullbackIso ψ q).inv.app
        ((scalarExtensionFunctor φ Y).obj N)) ≫
        (P C).map ((scalarExtensionFunctor_composition φ ψ Y).hom.app N) =
      (scalarExtensionFunctor_composition φ ψ Z).hom.app ((P A).obj N) ≫
        (directImageScalarPullbackIso (ψ.comp φ) q).inv.app N at hn
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
      invertible_square
      ((directImageScalarPullbackIso ψ q).app ((scalarExtensionFunctor φ Y).obj N) ≪≫
        (scalarExtensionFunctor ψ Z).mapIso ((directImageScalarPullbackIso φ q).app N))
      ((directImageScalarPullbackIso (ψ.comp φ) q).app N)
      ((P C).map ((scalarExtensionFunctor_composition φ ψ Y).hom.app N))
      ((scalarExtensionFunctor_composition φ ψ Z).hom.app ((P A).obj N)) hn
  exact counit_cocycle (directImageConstantAdjunction A q)
    (directImageConstantAdjunction B q) (directImageConstantAdjunction C q)
    (scalarExtensionFunctor_composition φ ψ Y) (scalarExtensionFunctor_composition φ ψ Z)
    (directImageScalarPullbackIso φ q) (directImageScalarPullbackIso ψ q)
    (directImageScalarPullbackIso (ψ.comp φ) q) hc E

end AlgebraicGeometry.ProEtale
