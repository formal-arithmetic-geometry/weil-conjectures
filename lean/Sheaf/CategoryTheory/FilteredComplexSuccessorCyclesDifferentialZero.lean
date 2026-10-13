module

public import Sheaf.CategoryTheory.FilteredComplexPageDifferential

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The successor-cycle inclusion into the page is killed by the outgoing page differential.
Source: Stacks Project, Homology, Tag 012K, displayed cycle and differential formulas.
(blueprint: lem-sp-filtered-complex-successor-cycles-differential-zero).

Proof. Put p = pq.1, n = pq.1 + pq.2, and j = (p+r, pq.2-r+1).
Take the intersection R = F^p K^n ∩ d⁻¹(F^(p+r+1) K^(n+1)), regarded as a
subobject of F^p K^n. Its graded projection factors epimorphically onto
Z_(r+1): adding F^(p+1) before projection does not change its image because
the projection kills F^(p+1). Write x for this epimorphism and t for the
inclusion of R into F^p K^n. The differential of t factors through
F^(p+r+1) K^(n+1); compose that factorization with the inclusion into
F^(p+r) K^(n+1), obtaining t'. The cokernel equation for the target graded
projection shows that t' has zero graded class. Apply D.on_representatives
to t, t', the composite of x with the inclusion hZ, and the zero target
cycle. The source representative equation follows from the image
factorization and Subobject.ofLE_arrow; the differential equation follows
from the factorization of dt; the target representative equation is the
cokernel equation just established. It follows that x followed by the
composite in the conclusion is zero. Cancel the epimorphism x to conclude.
All constructions are finite subobject and cokernel constructions and
require neither elementwise lifts through an epimorphism nor boundedness. -/
theorem filteredComplex_successor_cycles_differential_zero
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r) :
    (Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) ≫
        D.page.d pq ((ComplexShape.up' (r, 1 - r)).next pq) = 0 := by
  sorry

end CategoryTheory
