/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.CategoryTheory.FilteredCohomologyImage
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.Filtration

/-! # The stationary subquotient comparison at explicit filtration bounds

Source: Stacks Project, Tags 012Q and 0132.
(blueprint: lem-sp-filtered-stable-subquotient-at-bounds).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- At stationary outer steps the cycle/boundary quotient is the graded cohomology image.
Source: Stacks Project, Tags 012Q and 0132.
(blueprint: lem-sp-filtered-stable-subquotient-at-bounds).

Proof. Replace L^(p+r)K^(n+1) by zero in the cycle formula and replace
L^(p-r+1)K^(n-1) by the whole object in the boundary formula. Write A=L^pK^n,
A'=L^(p+1)K^n, Z=ker(d^n), and B=im(d^(n-1)). Then the cycles in A/A'
are ((A ∩ Z)+A')/A', and the boundaries are ((A ∩ B)+A')/A'. The boundary
inclusion is supplied (it follows from d²=0 and the two outer bounds).
The third isomorphism theorem identifies their quotient with
(A ∩ Z)/((A ∩ B)+(A' ∩ Z)): modularity gives
(A ∩ Z) ∩ ((A ∩ B)+A')=(A ∩ B)+(A' ∩ Z).
The image of H^n(L^pK) in H^n(K)=Z/B is the image of A ∩ Z in Z/B,
and the next image step is the image of A' ∩ Z. Their quotient has precisely
the same presentation. The abelian subquotient isomorphisms therefore identify
the stationary quotient with the cokernel defining the graded image filtration.
This uses only the two displayed outer bounds and r≥1; no uniform bound on
other degrees, chosen abutment, or spectral sequence is required. -/
theorem stableSubquotient_at_bounds
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r)
    (hupper : L.complexStep (p + r) (n + 1) = ⊥)
    (hlower : L.complexStep (p - r + 1) (n - 1) = ⊤)
    (hBZ : L.complexBoundaries p n r ≤ L.complexCycles p n r) :
    Nonempty (cokernel (Subobject.ofLE _ _ hBZ) ≅
      (L.cohomologyImage n).gradedPiece p) := by sorry

end CategoryTheory.DecreasingFiltration
