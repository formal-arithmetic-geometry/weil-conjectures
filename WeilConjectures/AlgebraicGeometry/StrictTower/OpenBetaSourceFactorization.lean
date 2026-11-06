/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerPullbackSquarePasting

/-!
# Source factorization of the normalized inverse open comparison

Source: Stacks, Tags 03DI, 07A7 and 0F7B; the source-factorization calculation in
step 8 of (blueprint: lem-cbc-proper-open-clopen-projector).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
attribute [local irreducible] G gComp gCompEq squareG towers_hasDerivedCategory

private theorem source_square_aux {C : Type*} [Category C]
    {P Q R S T U : C} (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ S)
    (d : S ⟶ R) (e : Q ⟶ T) (f : P ⟶ U) (g : U ⟶ T)
    [IsIso b] [IsIso c] (h₁ : a ≫ b = c ≫ d) (h₂ : a ≫ e = f ≫ g) :
    d ≫ inv b ≫ e = inv c ≫ f ≫ g := by
  have hd : d ≫ inv b = inv c ≫ a := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h₁,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hd, Category.assoc, h₂]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_source_square
    {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {a : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ a κ ε)
    {V P W A T : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (q : P ⟶ A) (i : A ⟶ T) (p : W ⟶ T)
    (h : (s ≫ b) ≫ p = (s ≫ q) ≫ i) (h₀ : q ≫ i = b ≫ p) (N : C T) :
    (κ s q (s ≫ q) rfl).hom.app ((L i).obj N) ≫
        (L s).map ((systemSquare κ q b i p h₀).inv.app N) =
      (systemSquare κ (s ≫ q) (s ≫ b) i p h.symm).inv.app N ≫
        (κ s b (s ≫ b) rfl).hom.app ((L p).obj N) := by
  have ha := NatTrans.congr_app (congrArg Iso.hom
    (S.assoc s q i (s ≫ q) (q ≫ i) ((s ≫ q) ≫ i)
      rfl rfl rfl (Category.assoc s q i).symm)) N
  have hb := NatTrans.congr_app (congrArg Iso.hom
    (S.assoc s b p (s ≫ b) (q ≫ i) ((s ≫ q) ≫ i)
      rfl h₀.symm h (Category.assoc s q i).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at ha hb
  have hh := source_square_aux _ _ _ _ _ _ _ ha hb
  simpa only [systemSquare, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, ← Functor.map_inv, NatIso.inv_hom_app, Category.assoc] using hh

private theorem transpose_conjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (d : R₂ ≅ R₁)
    (he : conjugateEquiv a b e.inv = d.inv)
    {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
    b.homEquiv X Y (e.inv.app X ≫ f) ≫ d.hom.app Y = a.homEquiv X Y f := by
  have h := unit_conjugateEquiv a b e.inv X
  rw [he] at h
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← h]
  simp only [Category.assoc]
  rw [← reassoc_of% (d.inv.naturality f)]
  simp only [Iso.inv_hom_id_app, Category.comp_id]

end AlgebraicGeometry.ProEtale.StrictTower
