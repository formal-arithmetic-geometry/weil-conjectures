/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare

/-! # Chain-map transport for affine spectrum representatives

Source: Stacks Project, Tags 0DJ8 and 0D5S.
(blueprint: lem-pc-affine-spectrum-representative-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private theorem transport_representative
    {C₀ C₁ D₀ D₁ E : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
    (J : C₀ ⥤ D₀) (S : D₀ ⥤ D₁) (G : C₀ ⥤ C₁) (J' : C₁ ⥤ D₁)
    (Q : E ⥤ D₁) (α : J ⋙ S ≅ G ⋙ J')
    {P K : C₀} {N K' M : C₁} {p : D₀} {A B C : E}
    (eP : P ≅ K) (eN : N ≅ K') (e : p ≅ J.obj K) (e' : Q.obj C ≅ J'.obj K')
    (φ : G.obj K ⟶ K') (ej : J.obj P ⟶ p) (eg : G.obj P ⟶ M)
    (ej' : J'.obj N ⟶ Q.obj C) (ejg : J'.obj M ⟶ Q.obj B)
    (es : S.obj p ⟶ Q.obj A) (a : A ⟶ B) (t : B ⟶ C) (qt : M ⟶ N)
    (he : e.inv = J.map eP.inv ≫ ej) (he' : e'.inv = J'.map eN.inv ≫ ej')
    (hrep : eg ≫ qt ≫ eN.hom = G.map eP.hom ≫ φ)
    (hsq : S.map ej ≫ es ≫ Q.map a =
      α.hom.app P ≫ J'.map eg ≫ ejg)
    (hnat : ejg ≫ Q.map t = J'.map qt ≫ ej') :
    es ≫ Q.map (a ≫ t) ≫ e'.hom = S.map e.hom ≫ α.hom.app K ≫ J'.map φ := by
  have hφ : φ ≫ eN.inv = G.map eP.inv ≫ eg ≫ qt := by
    have h := congrArg (fun f ↦ G.map eP.inv ≫ f ≫ eN.inv) hrep
    have hc : G.map eP.inv ≫ G.map eP.hom = 𝟙 _ := by
      rw [← G.map_comp, Iso.inv_hom_id, G.map_id]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      reassoc_of% hc, Category.id_comp] using h.symm
  apply (cancel_mono e'.inv).mp
  apply (cancel_epi (S.map e.inv)).mp
  have hc : S.map e.inv ≫ S.map e.hom = 𝟙 _ := by
    rw [← S.map_comp, Iso.inv_hom_id, S.map_id]
  simp only [Q.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    reassoc_of% hc]
  rw [he, he', S.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hsq, hnat]
  have hn := α.hom.naturality eP.inv
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← J'.map_comp_assoc]
  rw [hφ]

private theorem remove_comparison_identities
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : D} {P : C} (f : A ⟶ F.obj P) (g : F.obj P ⟶ B) :
    f ≫ F.map (𝟙 P) ≫ g ≫ 𝟙 B = f ≫ g := by
  simp

end AlgebraicGeometry.SingleComplexBaseChange
