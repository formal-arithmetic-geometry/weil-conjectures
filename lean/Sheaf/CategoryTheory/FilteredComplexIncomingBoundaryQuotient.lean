/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexPageDifferential

/-!
# Incoming differentials vanish modulo successor boundaries

Source: Stacks Project, Homology, Tag 012K, the displayed differential and boundary formulas.
(blueprint: new-filtered-complex-incoming-boundary-quotient).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Any map out of a page that kills successor boundaries kills the incoming differential.
Source: Stacks Project, Homology, Tag 012K, the displayed differential and boundary formulas.
(blueprint: new-filtered-complex-incoming-boundary-quotient).

Proof. Write pq = (p,q), n = p+q. The preceding bidegree is
(p-r,q+r-1), of total degree n-1. Pull back along epimorphisms to lift
an arbitrary source page class first to graded r-cycles and then to an
unquotiented r-cycle x in F^(p-r) K^(n-1). Such lifts cover the source:
the page projection is a cokernel, and graded r-cycles are the image of
unquotiented r-cycles under the graded projection. In the latter assertion,
the extra F^(p-r+1) summand in the definition maps to zero.
The differential dx lies in F^p K^n by the r-cycle condition. It also lies
in d(F^(p-r) K^(n-1)), so its graded class belongs to B_(r+1) at (p,q).
It lies in Z_r since d squared is zero. Lift its graded class to B_(r+1)
after another epimorphic pullback, if necessary. The equation
D.on_representatives identifies the page differential of the class of x
with the page class of dx. The hypothesis hq kills this class, by the
inclusion of B_(r+1) into Z_r. The composite in the conclusion therefore
vanishes after an epimorphic cover of the source; cancel that epimorphism.
Only finite pullbacks and image factorizations are used, so this argument
does not assume projective objects or a concrete underlying category. -/
theorem filteredComplex_incoming_boundary_quotient
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hB : F.complexBoundaries pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (Q : C) (q : filteredComplexPageObject K F r pq ⟶ Q)
    (hq : Subobject.ofLE _ _ hB ≫ filteredComplexPageπ K F r pq ≫ q = 0) :
    D.d ((ComplexShape.up' (r, 1 - r)).prev pq) pq ≫ q = 0 := by sorry

end CategoryTheory
