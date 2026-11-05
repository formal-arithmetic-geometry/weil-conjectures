/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.NatIso

/-! # Pasting projection-formula squares -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {C D E C' D' E' : Type*}
  [Category* C] [Category* D] [Category* E]
  [Category* C'] [Category* D'] [Category* E']
  {I : C ⥤ D} {G : D ⥤ E} {P : D ⥤ C} {Q : E ⥤ D} {F : E ⥤ C}
  {I' : C' ⥤ D'} {G' : D' ⥤ E'} {P' : D' ⥤ C'} {Q' : E' ⥤ D'} {F' : E' ⥤ C'}
  {NC : C ⥤ C'} {ND : D ⥤ D'} {NE : E ⥤ E'}
  {TC : C × C ⥤ C} {TD : D × D ⥤ D} {TE : E × E ⥤ E}
  {TC' : C' × C' ⥤ C'} {TD' : D' × D' ⥤ D'} {TE' : E' × E' ⥤ E'}

/-- Compatibility of a projection formula with three specified comparison isomorphisms. -/
def ProjectionForgetSquare (δ : I ⋙ ND ≅ NC ⋙ I') (κ : P ⋙ NC ≅ ND ⋙ P')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ TC') (tD : TD ⋙ ND ≅ ND.prod ND ⋙ TD')
    (p : I.prod (𝟭 D) ⋙ TD ⟶ (𝟭 C).prod P ⋙ TC ⋙ I)
    (p' : I'.prod (𝟭 D') ⋙ TD' ⟶ (𝟭 C').prod P' ⋙ TC' ⋙ I') : Prop :=
  ∀ M N, ND.map (p.app (M, N)) ≫ δ.hom.app (TC.obj (M, P.obj N)) ≫
      I'.map (tC.hom.app (M, P.obj N) ≫ TC'.map (Prod.mkHom (𝟙 _) (κ.hom.app N))) =
    tD.hom.app (I.obj M, N) ≫ TD'.map (Prod.mkHom (δ.hom.app M) (𝟙 _)) ≫
      p'.app (NC.obj M, ND.obj N)

/-- The open and proper projection-formula squares paste, with arbitrary specified
composition isomorphisms for pullback. -/
theorem projectionForgetSquare_paste
    (δI : I ⋙ ND ≅ NC ⋙ I') (δG : G ⋙ NE ≅ ND ⋙ G')
    (κP : P ⋙ NC ≅ ND ⋙ P') (κQ : Q ⋙ ND ≅ NE ⋙ Q')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ TC') (tD : TD ⋙ ND ≅ ND.prod ND ⋙ TD')
    (tE : TE ⋙ NE ≅ NE.prod NE ⋙ TE')
    (e : Q ⋙ P ≅ F) (e' : Q' ⋙ P' ≅ F')
    (pI : I.prod (𝟭 D) ⋙ TD ⟶ (𝟭 C).prod P ⋙ TC ⋙ I)
    (pG : G.prod (𝟭 E) ⋙ TE ⟶ (𝟭 D).prod Q ⋙ TD ⋙ G)
    (pI' : I'.prod (𝟭 D') ⋙ TD' ⟶ (𝟭 C').prod P' ⋙ TC' ⋙ I')
    (pG' : G'.prod (𝟭 E') ⋙ TE' ⟶ (𝟭 D').prod Q' ⋙ TD' ⋙ G')
    (hI : ProjectionForgetSquare δI κP tC tD pI pI')
    (hG : ProjectionForgetSquare δG κQ tD tE pG pG') (M : C) (N : E) :
    NE.map (pG.app (I.obj M, N) ≫
      G.map (pI.app (M, Q.obj N) ≫ I.map (TC.map (Prod.mkHom (𝟙 M) (e.hom.app N))))) ≫
      (δG.hom.app (I.obj (TC.obj (M, F.obj N))) ≫
        G'.map (δI.hom.app (TC.obj (M, F.obj N)))) ≫
      G'.map (I'.map (tC.hom.app (M, F.obj N) ≫
        TC'.map (Prod.mkHom (𝟙 _) (NC.map (e.inv.app N) ≫ κP.hom.app (Q.obj N) ≫
          P'.map (κQ.hom.app N) ≫ e'.hom.app (NE.obj N))))) =
    tE.hom.app (G.obj (I.obj M), N) ≫
      TE'.map (Prod.mkHom (δG.hom.app (I.obj M) ≫ G'.map (δI.hom.app M)) (𝟙 _)) ≫
      pG'.app (I'.obj (NC.obj M), NE.obj N) ≫
      G'.map (pI'.app (NC.obj M, Q'.obj (NE.obj N)) ≫
        I'.map (TC'.map (Prod.mkHom (𝟙 _) (e'.hom.app (NE.obj N))))) := by
  let x := TC.map (Prod.mkHom (𝟙 M) (e.hom.app N))
  let k := tC.hom.app (M, F.obj N) ≫ TC'.map
    (Prod.mkHom (𝟙 (NC.obj M)) (NC.map (e.inv.app N) ≫ κP.hom.app (Q.obj N) ≫
      P'.map (κQ.hom.app N) ≫ e'.hom.app (NE.obj N)))
  have ht : NC.map x ≫ k = tC.hom.app (M, P.obj (Q.obj N)) ≫
      TC'.map (Prod.mkHom (𝟙 _) (κP.hom.app (Q.obj N))) ≫
      TC'.map (Prod.mkHom (𝟙 _) (P'.map (κQ.hom.app N))) ≫
      TC'.map (Prod.mkHom (𝟙 _) (e'.hom.app (NE.obj N))) := by
    have hn := tC.hom.naturality (Prod.mkHom (𝟙 M) (e.hom.app N))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at hn
    dsimp only [x, k]
    rw [← Category.assoc, hn]
    simp only [Functor.map_id, Category.assoc, ← TC'.map_comp]
    congr 1
    apply congrArg TC'.map
    ext <;> simp [← NC.map_comp_assoc]
  have hnI := pI'.naturality (Prod.mkHom (𝟙 (NC.obj M)) (κQ.hom.app N))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj,
    Functor.id_map, Functor.id_obj] at hnI
  simp only [Functor.map_id] at hnI
  have hi : ND.map (pI.app (M, Q.obj N) ≫ I.map x) ≫
      δI.hom.app (TC.obj (M, F.obj N)) ≫ I'.map k =
    tD.hom.app (I.obj M, Q.obj N) ≫
      TD'.map (Prod.mkHom (𝟙 _) (κQ.hom.app N)) ≫
      TD'.map (Prod.mkHom (δI.hom.app M) (𝟙 _)) ≫
      pI'.app (NC.obj M, Q'.obj (NE.obj N)) ≫
      I'.map (TC'.map (Prod.mkHom (𝟙 _) (e'.hom.app (NE.obj N)))) := by
    have hnδ := δI.hom.naturality x
    dsimp only [Functor.comp_map] at hnδ
    rw [ND.map_comp, Category.assoc, reassoc_of% hnδ, ← I'.map_comp, ht]
    simp only [Functor.map_comp, Category.assoc]
    rw [← I'.map_comp_assoc, reassoc_of% (hI M (Q.obj N))]
    rw [← reassoc_of% hnI]
    have hs : TD'.map (Prod.mkHom (δI.hom.app M) (𝟙 (ND.obj (Q.obj N)))) ≫
        TD'.map (Prod.mkHom (𝟙 _) (κQ.hom.app N)) =
      TD'.map (Prod.mkHom (𝟙 _) (κQ.hom.app N)) ≫
        TD'.map (Prod.mkHom (δI.hom.app M) (𝟙 _)) := by
      simp only [← TD'.map_comp]
      congr 1
      ext <;> simp
    rw [reassoc_of% hs]
  have hnG := pG'.naturality (Prod.mkHom (δI.hom.app M) (𝟙 (NE.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj,
    Functor.id_map, Functor.id_obj] at hnG
  simp only [Functor.map_id] at hnG
  have hnδG := δG.hom.naturality (pI.app (M, Q.obj N) ≫ I.map x)
  dsimp only [Functor.comp_map] at hnδG
  change NE.map (pG.app (I.obj M, N) ≫ G.map (pI.app (M, Q.obj N) ≫ I.map x)) ≫
    (δG.hom.app _ ≫ G'.map (δI.hom.app _)) ≫ G'.map (I'.map k) = _
  simp only [NE.map_comp, Category.assoc]
  rw [reassoc_of% hnδG, ← G'.map_comp, ← G'.map_comp, hi]
  simp only [Functor.map_comp, Category.assoc]
  rw [← G'.map_comp_assoc, reassoc_of% (hG (I.obj M) N)]
  rw [← reassoc_of% hnG]
  simp only [← TE'.map_comp_assoc]
  congr 2
  · apply congrArg TE'.map
    ext <;> simp
  · simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
