/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData

/-! # Ordinary composition of balanced integral scalar reindexing

This square concerns ambient integral derived modules and extension of scalars only.
It contains neither common-stage realization comparisons nor completion-unit inverses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

attribute [local irreducible] coefficientMap pbcExtensionCounit
  integralCoefficientLinear completedIntegralCoefficientSheafUnrestricted pbcTensorSection

private theorem scalar_hom_ext {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (j : R ⟶ S)
    (M : pbcModules X R) {N : pbcModules X S}
    (f k : (pbcExtend j).obj M ⟶ N)
    (h : ∀ (W : X.ProEtᵒᵖ) (x : M.val.obj W),
      f.val.app W (pbcTensorSection j M W 1 x) =
        k.val.app W (pbcTensorSection j M W 1 x)) : f = k := by
  apply ((pbcScalarAdjunction j).homEquiv M N).injective
  ext W x
  change f.val.app W (((pbcScalarAdjunction j).unit.app M).val.app W x) =
    k.val.app W (((pbcScalarAdjunction j).unit.app M).val.app W x)
  erw [(pbcScalarAdjunction_exists j).exists.choose_spec M W x]
  exact h W x

private theorem scalar_map_one {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (j : R ⟶ S)
    {M N : pbcModules X R} (f : M ⟶ N) (W : X.ProEtᵒᵖ) (x : M.val.obj W) :
    ((pbcExtend j).map f).val.app W (pbcTensorSection j M W 1 x) =
      pbcTensorSection j N W 1 (f.val.app W x) := by
  have h := congrArg (fun k ↦ k.val.app W x) ((pbcScalarAdjunction j).unit.naturality f)
  change ((pbcScalarAdjunction j).unit.app N).val.app W (f.val.app W x) =
    ((pbcExtend j).map f).val.app W
      (((pbcScalarAdjunction j).unit.app M).val.app W x) at h
  erw [(pbcScalarAdjunction_exists j).exists.choose_spec,
    (pbcScalarAdjunction_exists j).exists.choose_spec] at h
  exact h.symm

private theorem balance_inv_one {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} {B : RingReindex l X g R S}
    {E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)}
    (I : IntegralReindex l X g B E)
    (M : integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)
    (W : X.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj W)) :
    (I.balance.inv.app M).val.app W
      (pbcTensorSection (coefficientMap l X R E)
        ((podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj M)
        W 1 x) =
      pbcTensorSection (coefficientMap l Y S E) M
        ((proEtaleIsoPostcompose g).op.obj W) 1 x := by
  have hs := I.sections M W 1 x
  have h1 : B.iso.hom.hom.app W 1 = 1 := map_one (B.iso.hom.hom.app W).hom
  rw [h1] at hs
  have hc := congrArg (fun f ↦ f.val.app W
    (pbcTensorSection (coefficientMap l Y S E) M
      ((proEtaleIsoPostcompose g).op.obj W) 1 x)) (I.balance.hom_inv_id_app M)
  exact (congrArg ((I.balance.inv.app M).val.app W) hs).symm.trans hc

private theorem tensor_one_heq {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (j : R ⟶ S)
    (M : pbcModules X R) {W W' : X.ProEtᵒᵖ} (h : W = W')
    {x : M.val.obj W} {y : M.val.obj W'} (hxy : HEq x y) :
    HEq (pbcTensorSection j M W 1 x) (pbcTensorSection j M W' 1 y) := by
  cases h
  cases hxy
  rfl

private theorem site_composition {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) [IsIso g] [IsIso h] (W : X.ProEtᵒᵖ) :
    ((proEtaleIsoPostcompose g ⋙ proEtaleIsoPostcompose h).op.obj W) =
      (proEtaleIsoPostcompose (g ≫ h)).op.obj W := by
  rcases W with ⟨⟨⟨A, B, f⟩, hf⟩⟩
  change (⟨⟨A, B, (f ≫ g) ≫ h⟩, _⟩ : Z.ProEtᵒᵖ) =
    ⟨⟨A, B, f ≫ (g ≫ h)⟩, _⟩
  simp only [Category.assoc]

set_option maxHeartbeats 600000 in
-- Sectionwise scalar extension involves several nested sheaf-module coercions.
private theorem ordinary_composition (C : FamilyCore l D) (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (hs : ∀ (M : modules l V.base.left (C.data V).realization)
      (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
      HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (M : integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left) :
    (C.integral T V (g ≪≫ h) E).balance.inv.app M ≫
      (C.moduleComp T U V g h).hom.app
        ((pbcExtend (coefficientMap l V.base.left (C.data V).realization E)).obj M) =
    (pbcExtend (coefficientMap l T.base.left (C.data T).realization E)).map
      ((podCompletedModuleComp l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
        h.hom g.hom).hom.app M) ≫
      (C.integral T U g E).balance.inv.app
        ((podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj M) ≫
      (modulePull l T.base.left g.hom (C.ring T U g)).map
        ((C.integral U V h E).balance.inv.app M) := by
  apply scalar_hom_ext
  intro W x
  have hx := (podCompletedModuleComp_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
    h.hom g.hom).exists.choose_spec M W.unop x
  let y := ((podCompletedModuleComp l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
    h.hom g.hom).hom.app M).val.app W x
  have hsite := site_composition g.hom h.hom W
  have ht := tensor_one_heq
    (coefficientMap l V.base.left (C.data V).realization E) M hsite hx
  change HEq (pbcTensorSection _ M _ 1 y) (pbcTensorSection _ M _ 1 x) at ht
  have h0 := balance_inv_one l (g ≪≫ h).hom
    (C.integral T V (g ≪≫ h) E) M W x
  have h1 := balance_inv_one l g.hom (C.integral T U g E)
    ((podCompletedModuleInverseImage l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj M) W y
  have h2 := balance_inv_one l h.hom (C.integral U V h E) M
    ((proEtaleIsoPostcompose g.hom).op.obj W) y
  have hm := scalar_map_one
    (coefficientMap l T.base.left (C.data T).realization E)
    ((podCompletedModuleComp l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
      h.hom g.hom).hom.app M) W x
  change ((C.moduleComp T U V g h).hom.app _).val.app W
      (((C.integral T V (g ≪≫ h) E).balance.inv.app M).val.app W
        (pbcTensorSection _ _ W 1 x)) =
    ((C.integral U V h E).balance.inv.app M).val.app
      ((proEtaleIsoPostcompose g.hom).op.obj W)
        (((C.integral T U g E).balance.inv.app _).val.app W
          (((pbcExtend (coefficientMap l T.base.left (C.data T).realization E)).map
            ((podCompletedModuleComp l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
              h.hom g.hom).hom.app M)).val.app W (pbcTensorSection _ _ W 1 x)))
  erw [hm, h0, h1, h2]
  exact eq_of_heq ((hs _ W _).trans ht.symm)

/-- The ordinary balanced scalar comparison respects the normalized compositors.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tags 03EL, 07A4 and 0941.
Proof: the normalized scalar adjunction determines maps out of scalar extension
on tensors 1 tensor x. Naturality of its unit computes scalar extension of the
completed compositor, and the sections equations compute the inverse balance maps.
The identity-on-sections compositor equations agree after the site associativity
transport, retained as HEq. This proves the inverse square. Cancel the inverse
balance isomorphisms to obtain the forward square displayed here.
(blueprint: lem-sf-adic-integral-scalar-ordinary-composition) -/
theorem integralScalarReindexing_balance_composition
    (C : FamilyCore l D) (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (hs : ∀ (M : modules l V.base.left (C.data V).realization)
      (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
      HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (M : integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left) :
    (C.integral T V (g ≪≫ h) E).balance.hom.app M ≫
      (pbcExtend (coefficientMap l T.base.left (C.data T).realization E)).map
        ((podCompletedModuleComp l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          h.hom g.hom).hom.app M) =
    (C.moduleComp T U V g h).hom.app
        ((pbcExtend (coefficientMap l V.base.left (C.data V).realization E)).obj M) ≫
      (modulePull l T.base.left g.hom (C.ring T U g)).map
        ((C.integral U V h E).balance.hom.app M) ≫
      (C.integral T U g E).balance.hom.app
        ((podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj M) := by
  apply (cancel_epi ((C.integral T V (g ≪≫ h) E).balance.inv.app M)).1
  rw [← Category.assoc _ ((C.moduleComp T U V g h).hom.app _),
    ordinary_composition l D C T U V g h hs E M]
  have hm :
      (modulePull l T.base.left g.hom (C.ring T U g)).map
          ((C.integral U V h E).balance.inv.app M) ≫
        (modulePull l T.base.left g.hom (C.ring T U g)).map
          ((C.integral U V h E).balance.hom.app M) = 𝟙 _ :=
    ((modulePull l T.base.left g.hom (C.ring T U g)).mapIso
      ((C.integral U V h E).balance.app M)).inv_hom_id
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hm]
  simp only [Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

end WeilConjectures.AdicQbarRealization
