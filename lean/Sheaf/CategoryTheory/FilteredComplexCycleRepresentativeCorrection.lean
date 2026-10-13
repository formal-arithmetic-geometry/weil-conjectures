module

public import Sheaf.CategoryTheory.FilteredComplexPageDifferential

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A representative whose differential is a page boundary can be corrected to a
successor-cycle representative without changing its source graded class.
Source: Stacks Project, Homology, Tag 012K, displayed cycle and boundary formulas.
(blueprint: lem-sp-filtered-complex-cycle-representative-correction).

Proof. Write p = i.1 and n = i.1 + i.2. The relation gives j.1 = p+r and
j.1+j.2 = n+1. Since the target page is the cokernel of its boundary inclusion,
hy0 factors y through the target graded boundary subobject. Pull back the image
epimorphism defining this subobject, and the epimorphism onto the sum of the
unquotiented boundary subobject with F^(p+r+1). The equality of target graded
classes then says, after pulling back the graded quotient epimorphism's kernel,
that dt is a sum of an incoming boundary and a term in F^(p+r+1). Pull back the
image epimorphism from F^((p+r)-r+1) = F^(p+1) defining that incoming boundary.
On the resulting epic cover e of A, obtain a morphism b into F^(p+1) with
d(e t - b) in F^(p+r+1). Include b into F^p; this is possible since F is
antitone. Thus e t - b factors through the unquotiented (r+1)-cycle intersection.
Its graded projection factors through the image defining successor graded cycles,
giving z. The graded projection kills b, so z has exactly the same graded class
as e x, by hx. Each cover is a pullback of an image or cokernel epimorphism and
is epic in an abelian category; their finite composite e is epic. This proves
the displayed equality without projectivity or elementwise lifting. -/
theorem filteredComplex_cycle_representative_correction
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j)
    (A : C)
    (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
    (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
    (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
    (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C))
    (ht : t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫
      K.d (i.1 + i.2) (j.1 + j.2) = t' ≫ (F.step j.1).arrow.f (j.1 + j.2))
    (hx : x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
      t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2))
    (hy : y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
      t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2))
    (hy0 : y ≫ filteredComplexPageπ K F r j = 0) :
    ∃ (B : C) (e : B ⟶ A), Epi e ∧
      ∃ z : B ⟶ (F.complexCycles i.1 (i.1 + i.2) (r + 1) : C),
        z ≫ (F.complexCycles i.1 (i.1 + i.2) (r + 1)).arrow =
          e ≫ x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow := by
  sorry

end CategoryTheory
