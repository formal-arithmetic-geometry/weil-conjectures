/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Exchange mate cubes for comparisons natural along isomorphisms -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory

/-- Transpose a family of arrows without imposing naturality on the family.
Source: tensor-free adjunction calculus, Stacks 0E47.
(blueprint: lem-sf-pointwise-exchange-mate-cube). -/
def pointwiseExchangeMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adjK : K ⊣ S)
    (θ : ∀ X : A, K.obj (G.obj X) ⟶ H.obj (F.obj X)) (E : B) :
    G.obj (R.obj E) ⟶ S.obj (H.obj E) :=
  adjK.homEquiv _ _ (θ (R.obj E) ≫ H.map (adj.counit.app E))

/-- Transposition preserves naturality along any class of arrows on which the
original comparison is natural. Here only invertible arrows are needed.
Source: adjunction counit naturality, Stacks 0E47.
(blueprint: lem-sf-pointwise-exchange-mate-cube). -/
theorem pointwiseExchangeMate_naturality_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adjK : K ⊣ S)
    (θ : ∀ X : A, K.obj (G.obj X) ⟶ H.obj (F.obj X))
    (hn : ∀ {X Y : A} (f : X ⟶ Y), IsIso f →
      K.map (G.map f) ≫ θ Y = θ X ≫ H.map (F.map f))
    {X Y : B} (f : X ⟶ Y) (hf : IsIso f) :
    G.map (R.map f) ≫ pointwiseExchangeMate adj adjK θ Y =
      pointwiseExchangeMate adj adjK θ X ≫ S.map (H.map f) := by
  have := hf
  rw [pointwiseExchangeMate, pointwiseExchangeMate,
    ← adjK.homEquiv_naturality_left, ← adjK.homEquiv_naturality_right]
  apply congrArg (adjK.homEquiv _ _)
  rw [← Category.assoc, hn (R.map f) (inferInstance)]
  simp only [Category.assoc, ← H.map_comp]
  have hc := adj.counit.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]

/-- A pointwise inverse comparison needs naturality only along the invertible
geometric mate in order to satisfy the exchange cube.
Source: Stacks 0E47; the counit proof of exchangeMate_cube.
(blueprint: lem-sf-pointwise-exchange-mate-cube).
Proof: transpose under the last adjunction. Its counit naturality and the two
comparison mate/counit equations reduce the first transpose to the left cube face.
Substitute the commuting cube, move the counit by naturality of the geometric
comparison, and use naturality of the second pointwise family along the invertible
geometric mate. The first comparison mate/counit equation then gives the other
transpose. Injectivity of the Hom equivalence proves equality. -/
theorem pointwiseExchangeMate_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : ∀ X : A, K.obj (G.obj X) ⟶ H.obj (F.obj X))
    (θ' : ∀ X : A', K'.obj (G'.obj X) ⟶ H'.obj (F'.obj X))
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ X) =
        θ' (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (hn : ∀ {X Y : A'} (f : X ⟶ Y), IsIso f →
      K'.map (G'.map f) ≫ θ' Y = θ' X ≫ H'.map (F'.map f))
    (E : B)
    (hi : IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E)) :
    c.map (pointwiseExchangeMate adj adjK θ E) ≫
        (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫
        G'.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E) ≫
        pointwiseExchangeMate adj' adjK' θ' (b.obj E) := by
  let e := pointwiseExchangeMate adj adjK θ
  let e' := pointwiseExchangeMate adj' adjK' θ'
  let mF := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).natTrans
  let mK := (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).natTrans
  have he : K.map (e E) ≫ adjK.counit.app (H.obj E) =
      θ (R.obj E) ≫ H.map (adj.counit.app E) :=
    (adjK.homEquiv _ _).symm_apply_apply _
  have he' : K'.map (e' (b.obj E)) ≫ adjK'.counit.app (H'.obj (b.obj E)) =
      θ' (R'.obj (b.obj E)) ≫ H'.map (adj'.counit.app (b.obj E)) :=
    (adjK'.homEquiv _ _).symm_apply_apply _
  have hmF := mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ pF.inv) E
  have hmK := mateEquiv_counit adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv) (H.obj E)
  change c.map (e E) ≫ mK.app (H.obj E) ≫ S'.map (pH.hom.app E) =
    pG.hom.app (R.obj E) ≫ G'.map (mF.app E) ≫ e' (b.obj E)
  apply (adjK'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change F'.map (mF.app E) ≫ adj'.counit.app (b.obj E) =
    pF.inv.app (R.obj E) ≫ b.map (adj.counit.app E) at hmF
  change K'.map (mK.app (H.obj E)) ≫ adjK'.counit.app (d.obj (H.obj E)) =
    pK.inv.app (S.obj (H.obj E)) ≫ d.map (adjK.counit.app (H.obj E)) at hmK
  have hnat := adjK'.counit.naturality (pH.hom.app E)
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  simp only [Functor.comp_obj] at *
  rw [hnat, ← Category.assoc (K'.map (mK.app (H.obj E))), hmK]
  have hp := pK.inv.naturality (e E)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hp
  rw [← Category.assoc, ← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← d.map_comp_assoc, he]
  simp only [Functor.map_comp, Category.assoc]
  have hh := congrArg (fun z ↦ K'.map (pG.hom.app (R.obj E)) ≫ z ≫
    d.map (H.map (adj.counit.app E)) ≫ pH.hom.app E) (hc (R.obj E))
  simp only [Category.assoc] at hh
  rw [← K'.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at hh
  have hp := pH.inv.naturality (adj.counit.app E)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hp
  rw [← Category.assoc (pH.inv.app _), ← hp] at hh
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  rw [hh]
  dsimp only [Functor.comp_obj] at *
  simp only [Category.comp_id]
  rw [he']
  have ht := hn (mF.app E) hi
  dsimp only [Functor.comp_obj] at ht
  rw [← Category.assoc (K'.map (G'.map (mF.app E))), ht]
  simp only [Category.assoc, ← H'.map_comp, hmF]

end CategoryTheory
