/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all Sheaf.Paper.AdicCoefficientDatum

/-! # Ordinary quotient chain maps for arbitrary ring sheaves

Source: the tensor quotient and balancing construction, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-ordinary-quotient).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The normalized transition is the transpose of the final unit.
Source: ordinary tensor quotient, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-ordinary-quotient). -/
def quotientTransitionNat
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (R : B ⥤ A) (e : R ⋙ Rm ≅ Rn) :
    Lm ⟶ Ln ⋙ R where
  app M := (am.homEquiv _ _).symm (an.unit.app M ≫ e.inv.app (Ln.obj M))
  naturality {M N} f := by
    apply (am.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    simp only [Equiv.apply_symm_apply]
    have hn := e.inv.naturality (Ln.map f)
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    rw [← hn]
    have hu := an.unit.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ e.inv.app (Ln.obj N)) hu

/-- A tensor section defined by the normalized unit and scalar multiplication.
Source: the tensor unit, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-ordinary-quotient). -/
def quotientTensor {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} {φ : R ⟶ S}
    {L : pbcModules W R ⥤ pbcModules W S} (a : L ⊣ pbcRestrict φ)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (L.obj M).val.obj U :=
  s • @id ((L.obj M).val.obj U) ((a.unit.app M).val.app U x)

/-- The unit-normalized quotient map has its pure-tensor formula.
Source: ordinary adjunction and scalar linearity, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-ordinary-quotient). -/
theorem quotientTransitionNat_tensor
    (W : Scheme.{u}) {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (q : S ⟶ T) (χ : R ⟶ T) (hc : φ ≫ q = χ)
    (Lm : pbcModules W R ⥤ pbcModules W S) (Ln : pbcModules W R ⥤ pbcModules W T)
    (am : Lm ⊣ pbcRestrict φ) (an : Ln ⊣ pbcRestrict χ)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U)
    (x : M.val.obj U) :
    HEq (((quotientTransitionNat am an (pbcRestrict q)
      (pbcRestrictComp φ q χ hc)).app M).val.app U (quotientTensor am M U s x))
        (quotientTensor an M U (q.hom.app U s) x) := by
  let aq := pbcScalarAdjunction q
  let e := pbcRestrictComp φ q χ hc
  let α := quotientTransitionNat am an (pbcRestrict q) e
  let β := (Adjunction.leftAdjointCompIso am aq an e).hom
  apply heq_of_eq
  have hu : am.unit.app M ≫ (pbcRestrict φ).map (α.app M) ≫
      e.hom.app (Ln.obj M) = an.unit.app M := by
    change ((am.homEquiv _ _) (α.app M)) ≫ e.hom.app _ = _
    simp only [α, quotientTransitionNat, Equiv.apply_symm_apply,
      Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hx := congrArg (fun f ↦ f.val.app U x) hu
  change (e.hom.app _).val.app U
    ((α.app M).val.app U ((am.unit.app M).val.app U x)) =
      (an.unit.app M).val.app U x at hx
  have he := (pbcRestrictComp_exists
    φ q
    χ
    hc).exists.choose_spec
  erw [he] at hx
  change (α.app M).val.app U
    (s • @id ((Lm.obj M).val.obj U)
      ((am.unit.app M).val.app U x)) =
    (q.hom.app U s) • @id ((Ln.obj M).val.obj U)
      ((an.unit.app M).val.app U x)
  simp only [id_eq]
  rw [map_smul]
  exact congrArg (fun z : (Ln.obj M).val.obj U ↦
    (q.hom.app U s) • z) hx

/-- The canonical balancing isomorphism has its iterated pure-tensor formula.
Source: ordinary tensor associativity, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-ordinary-quotient). -/
theorem quotientBalancing_tensor
    (W : Scheme.{u}) {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (q : S ⟶ T) (χ : R ⟶ T) (hc : φ ≫ q = χ)
    (Lm : pbcModules W R ⥤ pbcModules W S) (Ln : pbcModules W R ⥤ pbcModules W T)
    (am : Lm ⊣ pbcRestrict φ) (an : Ln ⊣ pbcRestrict χ)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U)
    (t : T.obj.obj U) (x : M.val.obj U) :
    ((Adjunction.leftAdjointCompIso am (pbcScalarAdjunction q) an
      (pbcRestrictComp φ q χ hc)).hom.app M).val.app U
        (pbcTensorSection q (Lm.obj M) U t (quotientTensor am M U s x)) =
      quotientTensor an M U (t * q.hom.app U s) x := by
  let aq := pbcScalarAdjunction q
  let e := pbcRestrictComp φ q χ hc
  let α := quotientTransitionNat am an (pbcRestrict q) e
  let β := (Adjunction.leftAdjointCompIso am aq an e).hom
  have hβ (M : pbcModules W R) :
      (aq.homEquiv _ _).symm (α.app M) = β.app M := by
    simp only [α, quotientTransitionNat, β, Adjunction.leftAdjointCompIso_hom_app,
      Adjunction.homEquiv_counit, Functor.map_comp, Functor.comp_obj, Category.assoc]
  have ha (N : pbcModules W R) (V : W.ProEtᵒᵖ)
      (r : S.obj.obj V) (z : N.val.obj V) :=
    eq_of_heq (quotientTransitionNat_tensor W φ q χ hc Lm Ln am an N V r z)
  have hu : aq.unit.app (Lm.obj M) ≫
      (pbcRestrict q).map (β.app M) = α.app M := by
    change (aq.homEquiv _ _) (β.app M) = α.app M
    rw [← hβ, Equiv.apply_symm_apply]
  have hx := congrArg (fun f ↦ f.val.app U
    ((quotientTensor am M U) s x)) hu
  change (β.app M).val.app U ((aq.unit.app _).val.app U _) = _ at hx
  rw [show (aq.unit.app _).val.app U
      ((quotientTensor am M U) s x) =
      pbcTensorSection q (Lm.obj M) U 1
        ((quotientTensor am M U) s x) from
    (pbcScalarAdjunction_exists q).exists.choose_spec _ U _] at hx
  rw [show pbcTensorSection q (Lm.obj M) U t
      ((quotientTensor am M U) s x) =
      t • pbcTensorSection q (Lm.obj M) U 1
        ((quotientTensor am M U) s x) by
    simpa only [pbcTensorSection, reductionTensorSection, pbcExtend, reductionChange,
      mul_one] using (tensorSection_smul W q _ U t 1 _).symm]
  rw [map_smul, hx]
  erw [ha]
  simp only [quotientTensor, smul_smul]

end WeilConjectures
