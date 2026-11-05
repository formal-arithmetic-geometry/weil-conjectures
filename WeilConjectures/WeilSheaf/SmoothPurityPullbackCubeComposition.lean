module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc

/-! # Composing reduction and reading cubes before choosing their categories -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D]

/-- Compose two pullback cubes in abstract categories. The naturality moves that
put the second coefficient functor outside the first cube are supplied separately. -/
theorem purity_compose_pullback_cubes (P : C ⥤ D)
    {A B C₀ D₀ E F : C} {X Y Z W : D}
    (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ D₀)
    (d : A ⟶ E) (e : E ⟶ F) (f : F ⟶ D₀)
    (p : X ⟶ Y) (q : Y ⟶ P.obj A)
    (r : X ⟶ Z) (s : Z ⟶ W) (t : W ⟶ P.obj E)
    (hred : a ≫ b ≫ c = d ≫ e ≫ f)
    (hread : p ≫ q ≫ P.map d = r ≫ s ≫ t) :
    p ≫ q ≫ P.map a ≫ P.map b ≫ P.map c =
      r ≫ s ≫ t ≫ P.map e ≫ P.map f := by
  rw [← P.map_comp_assoc b c, ← P.map_comp_assoc a (b ≫ c), hred]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hread]

end CategoryTheory.Functor
