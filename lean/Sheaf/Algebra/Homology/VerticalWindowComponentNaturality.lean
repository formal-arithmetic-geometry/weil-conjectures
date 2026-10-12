module

public import Sheaf.Algebra.Homology.VerticalWindowComponentIso

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical component identifications commute with maps of complexes.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2.
Proof: away from q both sides are maps from zero objects. At q, the upper
truncation cycles comparison commutes with cyclesMap, homologyπ commutes with
homologyMap, the inverse homology map of the lower truncation projection is
natural by naturality of that projection, and the extension homology comparison
is natural. Composing these four squares gives the required degree-q square.
(blueprint: lem-sp-vertical-window-component-naturality). -/
theorem verticalWindow_component_naturality (q : ℕ)
    {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (verticalWindow (C := C) (q : ℤ) (q + 1)).map f ≫
        (verticalWindowComponentIso q L).hom =
      (verticalWindowComponentIso q K).hom ≫
        (HomologicalComplex.single C (ComplexShape.up ℕ) q).map
          (HomologicalComplex.homologyMap f q) := by sorry

end HomologicalComplex₂
