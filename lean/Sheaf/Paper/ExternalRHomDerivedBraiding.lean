/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J7
-/
module
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Braiding compatibility of localization tensor constraints -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe w v u
set_option backward.isDefEq.respectTransparency false
private theorem braided_ofIso
    {C D : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [Category D] [MonoidalCategory D] [BraidedCategory D]
    (F G : C ⥤ D) [F.LaxMonoidal] (e : F ≅ G)
    (h : ∀ X Y, (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X =
      Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom) (X Y : C) :
    letI := Functor.LaxMonoidal.ofIso e
    (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X =
      Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom := by
  change (β_ (G.obj X) (G.obj Y)).hom ≫
      (e.inv.app Y ⊗ₘ e.inv.app X) ≫ Functor.LaxMonoidal.μ F Y X ≫ e.hom.app (Y ⊗ X) =
    ((e.inv.app X ⊗ₘ e.inv.app Y) ≫
      Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y)) ≫ G.map (β_ X Y).hom
  rw [← BraidedCategory.braiding_naturality_assoc, reassoc_of% (h X Y)]
  simp only [Category.assoc]
  rw [e.hom.naturality]

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
attribute [local instance] DerivedCategory.braidedCategory'
/-- The canonical localization braiding equation, kept abstract in its coefficient category.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-derived-braiding). -/
def AlgebraicGeometry.Etale.ExternalRHom.NativeBraidingAt
    (K L : CochainComplex C ℤ) : Prop :=
    (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q L K =
      Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫ DerivedCategory.Q.map (β_ K L).hom

/-- The localization tensor comparison respects the derived Koszul braiding.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-derived-braiding). -/
theorem AlgebraicGeometry.Etale.ExternalRHom.external_rhom_derived_braiding
    (K L : CochainComplex C ℤ) :
    AlgebraicGeometry.Etale.ExternalRHom.NativeBraidingAt C K L := by
  apply braided_ofIso
    ((HomotopyCategory.quotient C (.up ℤ)) ⋙ DerivedCategory.Qh)
    DerivedCategory.Q (DerivedCategory.quotientCompQhIso C)
  intro E H
  have hμ (K L : CochainComplex C ℤ) :
      Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) K L = 𝟙 _ := rfl
  dsimp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map]
  erw [hμ H E, hμ E H]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  exact DerivedMonoidal.braiding_hom_μ DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient _ _).obj E) ((HomotopyCategory.quotient _ _).obj H)

