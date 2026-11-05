/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPasting
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # Pasting projection-formula forget squares, in monoidal spelling

`projectionForgetSquare_paste_monoidal` restates `projectionForgetSquare_paste` for composite
data given by their components, with the target tensor functors the monoidal `tensor` and the
tensor maps written with whiskerings. All spelling conversions happen here, on abstract
functors, so that the concrete instance is an `exact`. -/

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

/-- The pasted open/proper forget square for composite projection data `pF`, `δF`, `κF`
specified by their components, in monoidal spelling. -/
theorem projectionForgetSquare_paste_monoidal
    (δI : I ⋙ ND ≅ NC ⋙ I') (δG : G ⋙ NE ≅ ND ⋙ G')
    (κP : P ⋙ NC ≅ ND ⋙ P') (κQ : Q ⋙ ND ≅ NE ⋙ Q')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ tensor C') (tD : TD ⋙ ND ≅ ND.prod ND ⋙ tensor D')
    (tE : TE ⋙ NE ≅ NE.prod NE ⋙ tensor E')
    (e : Q ⋙ P ≅ F) (e' : Q' ⋙ P' ≅ F')
    (pI : I.prod (𝟭 D) ⋙ TD ⟶ (𝟭 C).prod P ⋙ TC ⋙ I)
    (pG : G.prod (𝟭 E) ⋙ TE ⟶ (𝟭 D).prod Q ⋙ TD ⋙ G)
    (pI' : I'.prod (𝟭 D') ⋙ tensor D' ⟶ (𝟭 C').prod P' ⋙ tensor C' ⋙ I')
    (pG' : G'.prod (𝟭 E') ⋙ tensor E' ⟶ (𝟭 D').prod Q' ⋙ tensor D' ⋙ G')
    (hI : ProjectionForgetSquare δI κP tC tD pI pI')
    (hG : ProjectionForgetSquare δG κQ tD tE pG pG')
    (pF : (I ⋙ G).prod (𝟭 E) ⋙ TE ⟶ (𝟭 C).prod F ⋙ TC ⋙ (I ⋙ G))
    (δF : (I ⋙ G) ⋙ NE ≅ NC ⋙ (I' ⋙ G'))
    (κF : F ⋙ NC ≅ NE ⋙ F') (M : C) (N : E)
    (hpF : pF.app (M, N) = pG.app (I.obj M, N) ≫
      G.map (pI.app (M, Q.obj N) ≫ I.map (TC.map (Prod.mkHom (𝟙 M) (e.hom.app N)))))
    (hδF : ∀ X, δF.hom.app X = δG.hom.app (I.obj X) ≫ G'.map (δI.hom.app X))
    (hκF : κF.hom.app N = NC.map (e.inv.app N) ≫ κP.hom.app (Q.obj N) ≫
      P'.map (κQ.hom.app N) ≫ e'.hom.app (NE.obj N)) :
    NE.map (pF.app (M, N)) ≫ δF.hom.app (TC.obj (M, F.obj N)) ≫
        (I' ⋙ G').map (tC.hom.app (M, F.obj N) ≫ NC.obj M ◁ κF.hom.app N) =
      tE.hom.app (G.obj (I.obj M), N) ≫ δF.hom.app M ▷ NE.obj N ≫
        pG'.app (I'.obj (NC.obj M), NE.obj N) ≫
        G'.map (pI'.app (NC.obj M, Q'.obj (NE.obj N)) ≫
          I'.map (NC.obj M ◁ e'.hom.app (NE.obj N))) := by
  have h := projectionForgetSquare_paste δI δG κP κQ tC tD tE e e' pI pG pI' pG' hI hG M N
  rw [hpF, hκF]
  simp only [hδF]
  simp only [tensor_map, id_tensorHom, tensorHom_id, Functor.comp_map] at h ⊢
  exact h

end CategoryTheory
