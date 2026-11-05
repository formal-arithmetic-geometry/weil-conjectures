/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
import all WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

private abbrev schemeModulesDerived
    [d : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) : HasDerivedCategory.{w} Y.Modules := d Y

attribute [local instance] schemeModulesDerived

private theorem restriction_counit_glue
    {V : Type*} [Category V] {A B C D E F G H I J : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (e : D ⟶ E) (t : E ⟶ F)
    (f : B ⟶ G) (g : G ⟶ H) (i : H ⟶ I) (j : I ⟶ E)
    (v : A ⟶ G) (l : A ⟶ J) (m : J ⟶ H) (n : J ⟶ F) (d : D ≅ F)
    (hc : b ≫ c ≫ e = f ≫ g ≫ i ≫ j) (ha : a ≫ f = v)
    (hn : v ≫ g = l ≫ m) (hd : e ≫ t = d.hom) (ht : m ≫ i ≫ j ≫ t = n) :
    a ≫ b ≫ c = l ≫ n ≫ d.inv := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hd, reassoc_of% hc, reassoc_of% ha, reassoc_of% hn, ht]

private theorem counit_iso_inverse
    {V : Type*} [Category V] {A B C : V} (e : A ≅ B) (t : C ≅ A) (ε : B ⟶ C)
    (h : e.hom ≫ ε = t.inv) : ε ≫ t.hom = e.inv := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, h]
  simp only [Iso.inv_hom_id, Iso.hom_inv_id]

attribute [local implicit_reducible] Scheme.Modules TopCat.Sheaf

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] openRestrictionRepresentativeIso openRestrictedCompositionMap
  openRestrictedTensorDerivedIso openTensorRestrictionComplexIso openTensorRestrictionSquareIso
  openTensorRestrictionIso counit

end AlgebraicGeometry.SingleComplexBaseChange
