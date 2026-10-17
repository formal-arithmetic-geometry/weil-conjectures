/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.CategoryTheory.Functor.Basic

/-! # Abstract assembly of a projection with five comparison factors -/

@[expose] public section
open CategoryTheory
namespace AlgebraicGeometry

/-- A transport equality and a five-factor object comparison paste through a
functor. This isolates associativity and functoriality from the dependent
cartesian comparison records. -/
theorem perfectOverlapTailProjectionAbstract
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P : D} {Q₀ Q₁ Q₂ Q₃ Q₄ Q₅ : C}
    (lhs : P ⟶ F.obj Q₅) (stage transport : P ⟶ F.obj Q₀)
    (sigma : Q₀ ⟶ Q₅)
    (d₁ : Q₀ ⟶ Q₁) (d₂ : Q₁ ⟶ Q₂) (d₃ : Q₂ ⟶ Q₃)
    (d₄ : Q₃ ⟶ Q₄) (d₅ : Q₄ ⟶ Q₅)
    (hprojection : lhs = transport ≫ F.map d₁ ≫ F.map d₂ ≫
      F.map d₃ ≫ F.map d₄ ≫ F.map d₅)
    (htransport : stage = transport)
    (hobject : sigma = d₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ d₅) :
    lhs = stage ≫ F.map sigma := by
  rw [htransport, hobject]
  simpa only [Functor.map_comp, Category.assoc] using hprojection

end AlgebraicGeometry
