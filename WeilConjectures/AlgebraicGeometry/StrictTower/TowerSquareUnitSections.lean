/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
/-! # Unit sections of the canonical compositor square
Source: Stacks, Tags 04J0 and 07A7
(blueprint: lem-cbc-tower-square-unit-sections).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] CategoryTheory.catToReflQuiver
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]
/-- The canonical module adjunction unit evaluated on a section.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-square-unit-sections). -/
def towerUnitSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules B Y) (V : Y.ProEt) (s : M.val.obj (op V)) :
    ((modulePullback B f).obj M).val.obj (op ((Scheme.proEtaleBaseChange f).obj V)) :=
  (((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)).unit.app M).val.app (op V)) s

private theorem comp_unit_sections {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules B Z) (V : Z.ProEt)
    (m : M.val.obj (op V)) :
    ((moduleGComp B f g).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange (f ≫ g)).obj V))
      (towerUnitSection B (f ≫ g) M V m) =
    ((modulePullback B f).obj ((modulePullback B g).obj M)).val.map
      ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
      (towerUnitSection B f ((modulePullback B g).obj M)
        ((Scheme.proEtaleBaseChange g).obj V) (towerUnitSection B g M V m)) := by
  let af := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)
  let ag := Scheme.proEtaleRingModuleAdjunction g (coefficients B Z)
    (coefficients B Y) (constantRingIso B g)
  let afg := Scheme.proEtaleRingModuleAdjunction (f ≫ g) (coefficients B Z)
    (coefficients B X) (constantRingIso B (f ≫ g))
  have h := unit_conjugateEquiv (ag.comp af) afg (moduleGComp B f g).hom M
  have hc : conjugateEquiv (ag.comp af) afg (moduleGComp B f g).hom =
      (moduleRComp B f g).hom :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv ag af afg _
  rw [hc, Adjunction.comp_unit_app] at h
  have hs := congrArg (fun t => t.val.app (op V) m) h
  have hn := (moduleRComp_existsUnique B f g).choose_spec.1
    ((modulePullback B f).obj ((modulePullback B g).obj M)) V
    (towerUnitSection B f ((modulePullback B g).obj M)
      ((Scheme.proEtaleBaseChange g).obj V) (towerUnitSection B g M V m))
  exact hs.symm.trans hn

private theorem restrict_iso_cancel {X : Scheme.{u}} (N : Modules B X)
    {V W : X.ProEt} (e : V ≅ W) (m : N.val.obj (op W)) :
    N.val.map e.inv.op (N.val.map e.hom.op m) = m := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.inv_hom_id, op_id]
  simp only [PresheafOfModules.map_id]
  rfl

private theorem comp_inv_unit_sections {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules B Z) (V : Z.ProEt)
    (m : M.val.obj (op V)) :
    ((moduleGComp B f g).inv.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj ((Scheme.proEtaleBaseChange g).obj V)))
      (towerUnitSection B f ((modulePullback B g).obj M)
        ((Scheme.proEtaleBaseChange g).obj V) (towerUnitSection B g M V m)) =
    ((modulePullback B (f ≫ g)).obj M).val.map
      ((MorphismProperty.Over.pullbackComp f g).inv.app V).op
      (towerUnitSection B (f ≫ g) M V m) := by
  let c := (moduleGComp B f g).app M
  let e := (MorphismProperty.Over.pullbackComp f g).app V
  have h := comp_unit_sections B f g M V m
  have hc := congrArg (fun t => t.val.app
      (op ((Scheme.proEtaleBaseChange (f ≫ g)).obj V))
      (towerUnitSection B (f ≫ g) M V m)) c.hom_inv_id
  change c.inv.val.app _ (c.hom.val.app _ (towerUnitSection B (f ≫ g) M V m)) =
    towerUnitSection B (f ≫ g) M V m at hc
  have h' := congrArg (fun t => c.inv.val.app
      (op ((Scheme.proEtaleBaseChange (f ≫ g)).obj V)) t) h
  change c.inv.val.app _ (c.hom.val.app _ (towerUnitSection B (f ≫ g) M V m)) = _ at h'
  rw [hc] at h'
  have he := PresheafOfModules.naturality_apply c.inv.val e.hom.op
    (towerUnitSection B f ((modulePullback B g).obj M)
      ((Scheme.proEtaleBaseChange g).obj V) (towerUnitSection B g M V m))
  have h'' := congrArg (fun t =>
    ((modulePullback B (f ≫ g)).obj M).val.map e.inv.op t) (h'.trans he)
  rw [restrict_iso_cancel] at h''
  exact h''.symm

private theorem transport_unit_sections {X Y : Scheme.{u}}
    (f h : X ⟶ Y) (w : f = h) (M : Modules B Y) (V : Y.ProEt)
    (m : M.val.obj (op V)) :
    ((eqToIso (congrArg (modulePullback B) w.symm)).inv.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V)) (towerUnitSection B f M V m) =
    ((modulePullback B h).obj M).val.map
      ((eqToIso (congrArg Scheme.proEtaleBaseChange w.symm)).inv.app V).op
      (towerUnitSection B h M V m) := by
  subst h
  simp only [eqToIso_refl, NatTrans.id_app, SheafOfModules.id_val,
    Iso.refl_inv, PresheafOfModules.id_app, PresheafOfModules.map_id, op_id]
  rfl

/-- The projection-preserving comparison between the two site pullback paths.
Source: Stacks, Tag 03CF (blueprint: lem-cbc-tower-square-unit-sections). -/
def towerSiteSquare {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) :
    Scheme.proEtaleBaseChange g ⋙ Scheme.proEtaleBaseChange j' ≅
      Scheme.proEtaleBaseChange j ⋙ Scheme.proEtaleBaseChange a :=
  (MorphismProperty.Over.pullbackComp j' g).symm ≪≫
    eqToIso (congrArg Scheme.proEtaleBaseChange w.symm) ≪≫
      MorphismProperty.Over.pullbackComp a j

private theorem section_chain {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    {N₀ N₁ N₂ N₃ : PresheafOfModules R}
    (α : N₀ ⟶ N₁) (β : N₁ ⟶ N₂) (γ : N₂ ⟶ N₃)
    {V₀ V₁ V₂ V₃ : Cᵒᵖ} (f : V₀ ⟶ V₁) (g : V₂ ⟶ V₀) (h : V₃ ⟶ V₂)
    (s₀ : N₀.obj V₁) (s₁ : N₁.obj V₀) (s₂ : N₂.obj V₂) (s₃ : N₃.obj V₃)
    (ha : α.app V₁ s₀ = N₁.map f s₁)
    (hb : β.app V₀ s₁ = N₂.map g s₂)
    (hc : γ.app V₂ s₂ = N₃.map h s₃) :
    γ.app V₁ (β.app V₁ (α.app V₁ s₀)) = N₃.map (h ≫ g ≫ f) s₃ := by
  rw [ha, PresheafOfModules.naturality_apply, hb,
    PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hc]
  simp only [PresheafOfModules.map_comp_apply]

private theorem section_square {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {N₀ N₁ N₂ N₃ : SheafOfModules R}
    (α : N₀ ⟶ N₁) (β : N₁ ⟶ N₂) (γ : N₂ ⟶ N₃) (δ : N₀ ⟶ N₃)
    (hd : δ = α ≫ β ≫ γ)
    {V₀ V₁ V₂ V₃ : Cᵒᵖ} (f : V₀ ⟶ V₁) (g : V₂ ⟶ V₀) (h : V₃ ⟶ V₂)
    (k : V₃ ⟶ V₁) (hk : k = h ≫ g ≫ f)
    (s₀ : N₀.val.obj V₁) (s₁ : N₁.val.obj V₀)
    (s₂ : N₂.val.obj V₂) (s₃ : N₃.val.obj V₃)
    (ha : α.val.app V₁ s₀ = N₁.val.map f s₁)
    (hb : β.val.app V₀ s₁ = N₂.val.map g s₂)
    (hc : γ.val.app V₂ s₂ = N₃.val.map h s₃) :
    δ.val.app V₁ s₀ = N₃.val.map k s₃ := by
  subst δ
  subst k
  exact section_chain α.val β.val γ.val f g h s₀ s₁ s₂ s₃ ha hb hc

attribute [local irreducible] moduleSquareG modulePullback moduleGComp moduleRComp
  Scheme.proEtaleRingModuleAdjunction constantRingIso towerUnitSection

private theorem moduleSquare_inv {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) (M : Modules B X) :
    (moduleSquareG B a j' j g w).inv.app M =
      (moduleGComp B a j).inv.app M ≫
        (eqToIso (congrArg (modulePullback B) w.symm)).inv.app M ≫
        (moduleGComp B j' g).hom.app M := by
  have h := congrArg (fun e => e.inv.app M) (moduleSquareG_eq B a j' j g w)
  simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc] using h

private theorem towerSiteSquare_inv {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) (V : X.ProEt) :
    ((towerSiteSquare a j' j g w).inv.app V).op =
      ((MorphismProperty.Over.pullbackComp j' g).hom.app V).op ≫
        ((eqToIso (congrArg Scheme.proEtaleBaseChange w.symm)).inv.app V).op ≫
        ((MorphismProperty.Over.pullbackComp a j).inv.app V).op := by
  simp only [towerSiteSquare, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    op_comp, Category.assoc]

attribute [local irreducible] towerSiteSquare

/-- Canonical inverse-image composition preserves iterated adjunction units.
Source: Stacks, Tags 04J0 and 07A7
(blueprint: lem-cbc-tower-square-unit-sections).
Proof: conjugate the inverse-image square under the composite module adjunctions.
The conjugate is the direct-image compositor for the upper path, followed by
transport along the square equation and the inverse compositor for the lower path.
The unit-conjugate identity equates the two iterated units. Evaluate on a test
object and a section. The three direct-image components act by restriction along
the fibre-product pasting maps; functoriality combines them into the displayed
site-square inverse. This proves the equation for every ring and every square. -/
theorem towerSquare_unit_sections {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) (M : Modules B X) (V : X.ProEt)
    (m : M.val.obj (op V)) :
    ((moduleSquareG B a j' j g w).inv.app M).val.app
      (op ((Scheme.proEtaleBaseChange a).obj ((Scheme.proEtaleBaseChange j).obj V)))
      (towerUnitSection B a ((modulePullback B j).obj M)
        ((Scheme.proEtaleBaseChange j).obj V) (towerUnitSection B j M V m)) =
    ((modulePullback B j').obj ((modulePullback B g).obj M)).val.map
      ((towerSiteSquare a j' j g w).inv.app V).op
      (towerUnitSection B j' ((modulePullback B g).obj M)
        ((Scheme.proEtaleBaseChange g).obj V) (towerUnitSection B g M V m)) := by
  exact section_square
    (N₀ := (modulePullback B a).obj ((modulePullback B j).obj M))
    (N₁ := (modulePullback B (a ≫ j)).obj M)
    (N₂ := (modulePullback B (j' ≫ g)).obj M)
    (N₃ := (modulePullback B j').obj ((modulePullback B g).obj M))
    (V₀ := op ((Scheme.proEtaleBaseChange (a ≫ j)).obj V))
    (V₁ := op ((Scheme.proEtaleBaseChange a).obj ((Scheme.proEtaleBaseChange j).obj V)))
    (V₂ := op ((Scheme.proEtaleBaseChange (j' ≫ g)).obj V))
    (V₃ := op ((Scheme.proEtaleBaseChange j').obj ((Scheme.proEtaleBaseChange g).obj V)))
    ((moduleGComp B a j).inv.app M)
    ((eqToIso (congrArg (modulePullback B) w.symm)).inv.app M)
    ((moduleGComp B j' g).hom.app M)
    ((moduleSquareG B a j' j g w).inv.app M)
    (moduleSquare_inv B a j' j g w M)
    (((MorphismProperty.Over.pullbackComp a j).inv.app V).op)
    (((eqToIso (congrArg Scheme.proEtaleBaseChange w.symm)).inv.app V).op)
    (((MorphismProperty.Over.pullbackComp j' g).hom.app V).op)
    (((towerSiteSquare a j' j g w).inv.app V).op)
    (towerSiteSquare_inv a j' j g w V)
    (towerUnitSection B a ((modulePullback B j).obj M)
      ((Scheme.proEtaleBaseChange j).obj V) (towerUnitSection B j M V m))
    (towerUnitSection B (a ≫ j) M V m)
    (towerUnitSection B (j' ≫ g) M V m)
    (towerUnitSection B j' ((modulePullback B g).obj M)
      ((Scheme.proEtaleBaseChange g).obj V) (towerUnitSection B g M V m))
    (comp_inv_unit_sections B a j M V m)
    (transport_unit_sections B (a ≫ j) (j' ≫ g) w M V m)
    (comp_unit_sections B j' g M V m)

end AlgebraicGeometry.ProEtale.StrictTower

attribute [instance] CategoryTheory.catToReflQuiver
