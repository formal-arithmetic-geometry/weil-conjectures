import Mathlib.CategoryTheory.Sites.Plus

/-!
# Functoriality of the plus construction

Source: Stacks Project, Sites, Lemma 00W5 (blueprint:
`lem-weil-pbc-site-plus-construction-functorial`).
-/

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace WeilConjectures

/-- The plus construction is functorial on presheaves, and its canonical map is
natural.  The identity and composition laws are included in the same statement.
(blueprint: lem-weil-pbc-site-plus-construction-functorial)
-/
theorem plus_construction_functorial
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    {F G H : Cᵒᵖ ⥤ Type u}
    [∀ (P : Cᵒᵖ ⥤ Type u) (X : C) (S : J.Cover X),
      HasMultiequalizer (S.index P)]
    [∀ (X : C), HasColimitsOfShape (J.Cover X)ᵒᵖ (Type u)]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    (φ ≫ J.toPlus G = J.toPlus F ≫ J.plusMap φ) ∧
      (J.plusMap (𝟙 F) = 𝟙 (J.plusObj F)) ∧
      (J.plusMap (φ ≫ ψ) = J.plusMap φ ≫ J.plusMap ψ) := by
  sorry

end WeilConjectures
