/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPasting
public import WeilConjectures.WeilSheaf.Native.Projection.GeometricProjectionNaturality

/-! # Components of projection squares in monoidal categories -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C'] [MonoidalCategory D']
  {I : C ⥤ D} {P : D ⥤ C} {I' : C' ⥤ D'} {P' : D' ⥤ C'}
  {NC : C ⥤ C'} {ND : D ⥤ D'} {TC : C × C ⥤ C} {TD : D × D ⥤ D}

/-- Evaluate the tensor maps in a projection square while the categories are abstract. -/
lemma projectionForgetSquare_uncurried_app
    (δ : I ⋙ ND ≅ NC ⋙ I') (κ : P ⋙ NC ≅ ND ⋙ P')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ Functor.uncurry.obj (curriedTensor C'))
    (tD : TD ⋙ ND ≅ ND.prod ND ⋙ Functor.uncurry.obj (curriedTensor D'))
    (M : C) (N : D)
    (p : TD.obj (I.obj M, N) ⟶ I.obj (TC.obj (M, P.obj N)))
    (p' : I'.obj (NC.obj M) ⊗ ND.obj N ⟶ I'.obj (NC.obj M ⊗ P'.obj (ND.obj N)))
    (h : ND.map p ≫ δ.hom.app (TC.obj (M, P.obj N)) ≫
        I'.map (tC.hom.app (M, P.obj N) ≫
          (Functor.uncurry.obj (curriedTensor C')).map (Prod.mkHom (𝟙 _) (κ.hom.app N))) =
      tD.hom.app (I.obj M, N) ≫
        (Functor.uncurry.obj (curriedTensor D')).map (Prod.mkHom (δ.hom.app M) (𝟙 _)) ≫ p') :
    ND.map p ≫ δ.hom.app (TC.obj (M, P.obj N)) ≫
        I'.map (tC.hom.app (M, P.obj N) ≫ NC.obj M ◁ κ.hom.app N) =
      tD.hom.app (I.obj M, N) ≫ δ.hom.app M ▷ ND.obj N ≫ p' := by
  dsimp at h ⊢
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id] using h

end CategoryTheory

namespace CategoryTheory

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C'] [MonoidalCategory D']
  {I : C ⥤ D} {P : D ⥤ C} {I' : C' ⥤ D'} {P' : D' ⥤ C'}
  {NC : C ⥤ C'} {ND : D ⥤ D'} {TC : C × C ⥤ C} {TD : D × D ⥤ D}

/-- The uncurried projection square is its componentwise monoidal equation. -/
lemma projectionForgetSquare_uncurried_iff
    (δ : I ⋙ ND ≅ NC ⋙ I') (κ : P ⋙ NC ≅ ND ⋙ P')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ Functor.uncurry.obj (curriedTensor C'))
    (tD : TD ⋙ ND ≅ ND.prod ND ⋙ Functor.uncurry.obj (curriedTensor D'))
    (p : I.prod (𝟭 D) ⋙ TD ⟶ (𝟭 C).prod P ⋙ TC ⋙ I)
    (p' : I'.prod (𝟭 D') ⋙ Functor.uncurry.obj (curriedTensor D') ⟶
      (𝟭 C').prod P' ⋙ Functor.uncurry.obj (curriedTensor C') ⋙ I') :
    ProjectionForgetSquare δ κ tC tD p p' ↔
      ∀ M N, ND.map (p.app (M, N)) ≫ δ.hom.app (TC.obj (M, P.obj N)) ≫
          I'.map (tC.hom.app (M, P.obj N) ≫ NC.obj M ◁ κ.hom.app N) =
        tD.hom.app (I.obj M, N) ≫ δ.hom.app M ▷ ND.obj N ≫ p'.app (NC.obj M, ND.obj N) := by
  dsimp [ProjectionForgetSquare]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- The projection square for tensor bifunctors is its componentwise monoidal equation. -/
lemma projectionForgetSquare_monoidal_iff
    (δ : I ⋙ ND ≅ NC ⋙ I') (κ : P ⋙ NC ≅ ND ⋙ P')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ tensor C')
    (tD : TD ⋙ ND ≅ ND.prod ND ⋙ tensor D')
    (p : I.prod (𝟭 D) ⋙ TD ⟶ (𝟭 C).prod P ⋙ TC ⋙ I)
    (p' : I'.prod (𝟭 D') ⋙ tensor D' ⟶ (𝟭 C').prod P' ⋙ tensor C' ⋙ I') :
    ProjectionForgetSquare δ κ tC tD p p' ↔
      ∀ M N, ND.map (p.app (M, N)) ≫ δ.hom.app (TC.obj (M, P.obj N)) ≫
          I'.map (tC.hom.app (M, P.obj N) ≫ NC.obj M ◁ κ.hom.app N) =
        tD.hom.app (I.obj M, N) ≫ δ.hom.app M ▷ ND.obj N ≫ p'.app (NC.obj M, ND.obj N) := by
  dsimp [ProjectionForgetSquare]
  simp only [MonoidalCategory.tensorHom_def, id_whiskerRight, whiskerLeft_id,
    Category.id_comp, Category.comp_id]

end CategoryTheory
