module
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]
/-- Forward containment in the successor-boundaries image calculation.
Source: Stacks Project, Homology, Tag 012K.
(blueprint: new-filtered-complex-successor-boundaries-image-le).
The representative chase shows every pullback of an incoming page boundary is
represented by a successor boundary. -/
theorem filteredComplex_successor_boundaries_image_le
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq)
    (hf : f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) :
    (Subobject.pullback f).obj
      (imageSubobject (D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq)) ≤
      Subobject.mk (Subobject.ofLE _ _
        (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) (r + 1))) := by sorry
end CategoryTheory
