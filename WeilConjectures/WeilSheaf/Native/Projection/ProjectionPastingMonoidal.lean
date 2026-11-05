/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.MonoidalProjectionForgetSquare

/-! # Pasting projection squares in monoidal notation -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C D E C' D' E' : Type*}
  [Category* C] [Category* D] [Category* E]
  [Category* C'] [Category* D'] [Category* E']
  [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
  {I : C ⥤ D} {G : D ⥤ E} {P : D ⥤ C} {Q : E ⥤ D} {F : E ⥤ C}
  {I' : C' ⥤ D'} {G' : D' ⥤ E'} {P' : D' ⥤ C'} {Q' : E' ⥤ D'} {F' : E' ⥤ C'}
  {NC : C ⥤ C'} {ND : D ⥤ D'} {NE : E ⥤ E'}
  {TC : C × C ⥤ C} {TD : D × D ⥤ D} {TE : E × E ⥤ E}

/-- Pasting projection squares, with tensor maps evaluated before specialization. -/
theorem projectionForgetSquare_paste_monoidal
    (δI : I ⋙ ND ≅ NC ⋙ I') (δG : G ⋙ NE ≅ ND ⋙ G')
    (κP : P ⋙ NC ≅ ND ⋙ P') (κQ : Q ⋙ ND ≅ NE ⋙ Q')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ tensor C')
    (tD : TD ⋙ ND ≅ ND.prod ND ⋙ tensor D')
    (tE : TE ⋙ NE ≅ NE.prod NE ⋙ tensor E')
    (e : Q ⋙ P ≅ F) (e' : Q' ⋙ P' ≅ F')
    (pI : I.prod (𝟭 D) ⋙ TD ⟶ (𝟭 C).prod P ⋙ TC ⋙ I)
    (pG : G.prod (𝟭 E) ⋙ TE ⟶ (𝟭 D).prod Q ⋙ TD ⋙ G)
    (pI' : I'.prod (𝟭 D') ⋙ tensor D' ⟶ (𝟭 C').prod P' ⋙ tensor C' ⋙ I')
    (pG' : G'.prod (𝟭 E') ⋙ tensor E' ⟶ (𝟭 D').prod Q' ⋙ tensor D' ⋙ G')
    (hI : ProjectionForgetSquare δI κP tC tD pI pI')
    (hG : ProjectionForgetSquare δG κQ tD tE pG pG') (M : C) (N : E) :
    NE.map (pG.app (I.obj M, N) ≫
      G.map (pI.app (M, Q.obj N) ≫ I.map (TC.map (Prod.mkHom (𝟙 M) (e.hom.app N))))) ≫
      (δG.hom.app (I.obj (TC.obj (M, F.obj N))) ≫
        G'.map (δI.hom.app (TC.obj (M, F.obj N)))) ≫
      G'.map (I'.map (tC.hom.app (M, F.obj N) ≫
        NC.obj M ◁ (NC.map (e.inv.app N) ≫ κP.hom.app (Q.obj N) ≫
          P'.map (κQ.hom.app N) ≫ e'.hom.app (NE.obj N)))) =
    tE.hom.app (G.obj (I.obj M), N) ≫
      (δG.hom.app (I.obj M) ≫ G'.map (δI.hom.app M)) ▷ NE.obj N ≫
      pG'.app (I'.obj (NC.obj M), NE.obj N) ≫
      G'.map (pI'.app (NC.obj M, Q'.obj (NE.obj N)) ≫
        I'.map (NC.obj M ◁ e'.hom.app (NE.obj N))) := by
  have h := projectionForgetSquare_paste δI δG κP κQ tC tD tE e e'
    pI pG pI' pG' hI hG M N
  dsimp at h ⊢
  simpa only [MonoidalCategory.tensorHom_def, id_whiskerRight, whiskerLeft_id,
    Category.id_comp, Category.comp_id] using h

end CategoryTheory
