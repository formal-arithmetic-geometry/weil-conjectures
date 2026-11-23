/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.CoproductsOfCopowers

/-! # A projection formula implies coproduct preservation
-/

@[expose] public section

universe s uC vC uD vD

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- If F preserves coproducts and the tensor unit, and G satisfies the projection
formula, then G preserves coproducts. -/
theorem preservesCoproducts_of_projectionFormula
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [MonoidalClosed C]
    [HasZeroMorphisms C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : D ⥤ C) (G : C ⥤ D) (I : Type s)
    [HasCoproductsOfShape I C] [HasCoproductsOfShape I D]
    [PreservesColimitsOfShape (Discrete I) F]
    (e : F.obj (𝟙_ D) ≅ 𝟙_ C)
    (p : G ⋙ curriedTensor D ≅
      (Functor.postcompose₂.obj G).obj
        ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj F).obj (curriedTensor C))) :
    PreservesColimitsOfShape (Discrete I) G := by
  apply preservesCoproducts_of_preservesCopowers G I
  intro M
  let Q := F ⋙ tensorLeft M
  have hp : tensorLeft (G.obj M) ≅ Q ⋙ G := p.app M
  have : PreservesColimitsOfShape (Discrete I) (Q ⋙ G) :=
    preservesColimitsOfShape_of_natIso hp
  let B : I → D := fun _ ↦ 𝟙_ D
  let c := Cofan.mk (∐ B) (Sigma.ι B)
  have hc : IsColimit c := coproductIsCoproduct B
  have : PreservesColimit (Discrete.functor B ⋙ Q) G :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves Q hc)
      (isColimitOfPreserves (Q ⋙ G) hc)
  let a : Q.obj (𝟙_ D) ≅ M := (tensorLeft M).mapIso e ≪≫ ρ_ M
  let b : Discrete.functor B ⋙ Q ≅ Discrete.functor (fun _ : I ↦ M) :=
    NatIso.ofComponents (fun _ ↦ a) (by
      rintro ⟨i⟩ ⟨j⟩ f
      obtain rfl := Discrete.eq_of_hom f
      simp)
  exact preservesColimit_of_iso_diagram G b

end CategoryTheory
