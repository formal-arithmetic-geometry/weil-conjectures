/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarModels
import all WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension

/-! # The ordinary balanced scalar rectangle

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-ordinary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.podCompletedRingMap
  AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap
  WeilConjectures.completedScalarTensorSection WeilConjectures.integralOrdinaryTensorSection
  AlgebraicGeometry.Scheme.pbcTensorSection
  WeilConjectures.AdicQbarRealization.coefficientMap
  AlgebraicGeometry.Scheme.reductionChange
  WeilConjectures.completedCoefficientMap

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

private theorem tensor_hom_ext
    {W : Scheme.{u}} {A D : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : A ⟶ D) (M : pbcModules W A) {N : pbcModules W D}
    (f k : (pbcExtend a).obj M ⟶ N)
    (h : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (pbcTensorSection a M U 1 x) =
        k.val.app U (pbcTensorSection a M U 1 x)) : f = k := by
  apply ((pbcScalarAdjunction a).homEquiv M N).injective
  ext U x
  change f.val.app U (((pbcScalarAdjunction a).unit.app M).val.app U x) =
    k.val.app U (((pbcScalarAdjunction a).unit.app M).val.app U x)
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec M U x]
  exact h U x

private theorem associator_inv_unit
    {W : Scheme.{u}} {A D V : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : A ⟶ D) (d : D ⟶ V) (v : A ⟶ V) (h : a ≫ d = v)
    (M : pbcModules W A) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((Adjunction.leftAdjointCompIso (pbcScalarAdjunction a) (pbcScalarAdjunction d)
      (pbcScalarAdjunction v) (pbcRestrictComp a d v h)).inv.app M).val.app U
        (pbcTensorSection v M U 1 x) =
      pbcTensorSection d ((pbcExtend a).obj M) U 1
        (pbcTensorSection a M U 1 x) := by
  have hu := unit_conjugateEquiv
    ((pbcScalarAdjunction a).comp (pbcScalarAdjunction d)) (pbcScalarAdjunction v)
    (Adjunction.leftAdjointCompIso (pbcScalarAdjunction a) (pbcScalarAdjunction d)
      (pbcScalarAdjunction v) (pbcRestrictComp a d v h)).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  have hx := congrArg (fun f ↦ f.val.app U x) hu.symm
  simp only [Adjunction.comp_unit_app, Category.assoc, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hx
  change _ = ((pbcRestrictComp a d v h).hom.app _).val.app U
    (((pbcScalarAdjunction d).unit.app _).val.app U
      (((pbcScalarAdjunction a).unit.app M).val.app U x)) at hx
  erw [(pbcRestrictComp_exists a d v h).exists.choose_spec] at hx
  erw [(pbcScalarAdjunction_exists v).exists.choose_spec,
    (pbcScalarAdjunction_exists a).exists.choose_spec,
    (pbcScalarAdjunction_exists d).exists.choose_spec] at hx
  exact hx

private theorem tensor_map_unit
    {W : Scheme.{u}} {A D : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : A ⟶ D) {M N : pbcModules W A} (f : M ⟶ N)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcExtend a).map f).val.app U (pbcTensorSection a M U 1 x) =
      pbcTensorSection a N U 1 (f.val.app U x) := by
  have hu := congrArg (fun k ↦ k.val.app U x) ((pbcScalarAdjunction a).unit.naturality f)
  change (((pbcScalarAdjunction a).unit.app N).val.app U (f.val.app U x)) =
    ((pbcExtend a).map f).val.app U (((pbcScalarAdjunction a).unit.app M).val.app U x)
    at hu
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec,
    (pbcScalarAdjunction_exists a).exists.choose_spec] at hu
  exact hu.symm

private theorem scalarModel_inv_tensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) (M : integralTowerModules l E W)
    (U : W.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) :
    ((isomorphismScalarSheafModel l E L i W).inv.app M).val.app U
      (completedScalarTensorSection l E L i W M U a x) =
      integralOrdinaryTensorSection l E L i W M U a x := by
  have hs := (isomorphismScalarSheafModel_existsUnique l E L i W).exists.choose_spec
    M U a x
  have hc := congrArg (fun f ↦ f.val.app U
    (integralOrdinaryTensorSection l E L i W M U a x))
    ((isomorphismScalarSheafModel l E L i W).app M).hom_inv_id
  exact (congrArg (((isomorphismScalarSheafModel l E L i W).inv.app M).val.app U)
    hs.symm).trans hc

private theorem scalar_reindex_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (M : integralTowerModules l E Y) (U : X.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    ((completedScalarSheafReindex l E L i g).hom.app M).val.app U
      (completedScalarTensorSection l E L i X
        ((podCompletedModuleInverseImage l E g).obj M) U 1 x) =
      completedScalarTensorSection l E L i Y M
        ((proEtaleIsoPostcompose g).op.obj U) 1 x := by
  unfold completedScalarSheafReindex
  dsimp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, SheafOfModules.comp_val]
  try simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalarModel_inv_tensor, ordinaryTensorSection_map]
  erw [(completedReindexSheafModel_apply l E g M U x).1]
  have hb := (isomorphismScalarTensor_existsUnique l E L i g).exists.choose_spec
    M U.unop x 1
  have hone : (inverseImageCompletedCoefficientMap l L g).hom.app U 1 = 1 :=
    ((inverseImageCompletedCoefficientMap l L g).hom.app U).hom.map_one
  erw [hone] at hb
  erw [hb]
  erw [(completedReindexSheafModel_apply l L g _ U _).2]
  exact (isomorphismScalarSheafModel_existsUnique l E L i Y).exists.choose_spec
    M ((proEtaleIsoPostcompose g).op.obj U) 1 x

private theorem balance_inv_unit (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : Index l (PadicAlgCl l)) (I : IntegralReindex l X g B E)
    (M : integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y)
    (U : X.ProEtᵒᵖ) (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    (I.balance.inv.app M).val.app U
      (pbcTensorSection (coefficientMap l X R E)
        ((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
          g).obj M) U 1 x) =
      pbcTensorSection (coefficientMap l Y S E) M
        ((proEtaleIsoPostcompose g).op.obj U) 1 x := by
  have hs := I.sections M U 1 x
  have hone : B.iso.hom.hom.app U 1 = 1 := (B.iso.hom.hom.app U).hom.map_one
  erw [hone] at hs
  have hc := congrArg (fun f ↦ f.val.app U
    (pbcTensorSection (coefficientMap l Y S E) M
      ((proEtaleIsoPostcompose g).op.obj U) 1 x)) (I.balance.app M).hom_inv_id
  exact (congrArg ((I.balance.inv.app M).val.app U) hs.symm).trans hc

attribute [local irreducible] completedScalarSheafReindex
attribute [local semireducible] completedScalarTensorSection pbcTensorSection reductionChange

set_option maxHeartbeats 800000 in
-- Sectionwise equality transports require more elaborator steps, within the time limit.
/-- The scalar rectangle commutes on ordinary module sheaves.
Source: BS 6.8.14--6.8.15; the pure-tensor argument in step 2 of
lem-sf-adic-reindex-balanced-scalar.
(blueprint: lem-sf-adic-reindex-scalar-ordinary).

Proof in words: the ordinary scalar adjunction reduces equality to tensors
1 tensor x. The unit equation for the conjugate of the restriction-composition
isomorphism shows that the inverse X associator inserts a second tensor unit.
Naturality of the scalar adjunction unit moves the scalar reindexing inside that
tensor. Its five ordinary model factors preserve unit tensors, by their section
normalizations and the completed reindexing equality transport. The L balance
inverse preserves these tensors by its section normalization and inverse identity.
The Y associator collapses the two units by its inverse identity. The E balance
inverse gives exactly the same tensor on the other route. Injectivity of the
ordinary scalar adjunction finishes. This includes zero modules, empty site
objects, and identity embeddings without additional hypotheses. -/
theorem integralReindex_scalar_ordinary (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (IE : IntegralReindex l X g B E) (IL : IntegralReindex l X g B L)
    (M : integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let C := Coefficient.{u} l (PadicAlgCl l)
    let i := coefficientInclusion l (PadicAlgCl l) E L h
    let pullE := podCompletedModuleInverseImage l (C E) g
    let TY := completedOrdinaryScalarExtension l (C E) (C L) i Y
    let NXL := pbcExtend (coefficientMap l X R L)
    let H := modulePull l X g B
    let ax := nativeScalarSheafAssociator l X R E L h
    let ay := nativeScalarSheafAssociator l Y S E L h
    let b := completedScalarSheafReindex l (C E) (C L) i g
    ax.inv.app (pullE.obj M) ≫ NXL.map (b.hom.app M) ≫
      IL.balance.inv.app (TY.obj M) ≫ H.map (ay.hom.app M) =
        IE.balance.inv.app M  := by
  dsimp only
  refine tensor_hom_ext (coefficientMap l X R E)
    ((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g).obj M)
    _ _ ?_
  intro U x
  let CE := Coefficient.{u} l (PadicAlgCl l) E
  let CL := Coefficient.{u} l (PadicAlgCl l) L
  let i := coefficientInclusion l (PadicAlgCl l) E L h
  let P := (podCompletedModuleInverseImage l CE g).obj M
  have haX := associator_inv_unit (completedCoefficientMap l CE CL i X)
    (coefficientMap l X R L) (coefficientMap l X R E)
    (by unfold coefficientMap; exact R.coefficient_scalar E L h)
    P U x
  have hm := tensor_map_unit (coefficientMap l X R L)
    ((completedScalarSheafReindex l CE CL i g).hom.app M) U
    (completedScalarTensorSection l CE CL i X P U 1 x)
  have hb := scalar_reindex_unit l CE CL i g M U x
  have hl := balance_inv_unit l g R S B L IL
    ((completedOrdinaryScalarExtension l CE CL i Y).obj M) U
    (completedScalarTensorSection l CE CL i Y M
      ((proEtaleIsoPostcompose g).op.obj U) 1 x)
  have haY := associator_inv_unit (completedCoefficientMap l CE CL i Y)
    (coefficientMap l Y S L) (coefficientMap l Y S E)
    (by unfold coefficientMap; exact S.coefficient_scalar E L h)
    M ((proEtaleIsoPostcompose g).op.obj U) x
  have hc := congrArg (fun f ↦ f.val.app
    ((proEtaleIsoPostcompose g).op.obj U)
      (pbcTensorSection (coefficientMap l Y S E) M
        ((proEtaleIsoPostcompose g).op.obj U) 1 x))
    ((nativeScalarSheafAssociator l Y S E L h).app M).inv_hom_id
  have he := balance_inv_unit l g R S B E IE M U x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change _ = _ at haX hm hb hl haY hc he
  erw [haX, hm, hb, hl, he]
  exact (congrArg
    (((nativeScalarSheafAssociator l Y S E L h).hom.app M).val.app
      ((proEtaleIsoPostcompose g).op.obj U)) haY.symm).trans hc

end WeilConjectures.AdicQbarRealization
