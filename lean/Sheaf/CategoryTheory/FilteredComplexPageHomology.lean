/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles

/-!
# Successor homology of a filtered-complex quotient page

Source: Stacks Project, Homology, Tag 012K, lemma-spectral-sequence-filtered-complex,
and the displayed cycle, boundary, and differential formulas preceding it.
(blueprint: lem-sp-filtered-complex-page-homology).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The homology of the representative differential is the next concrete quotient.
The next page's differential is not needed for this assertion.
Source: Stacks Project, Tag 012K, lemma-spectral-sequence-filtered-complex,
and the displayed cycle, boundary, and differential formulas preceding it.
(blueprint: lem-sp-filtered-complex-page-homology).

Proof. Work at (p,q), put n = p+q, and write R_s for
F^p K^n ∩ d⁻¹(F^(p+s) K^(n+1)) and T_s for
F^p K^n ∩ d(F^(p-s+1) K^(n-1)). The graded image of R_s is Z_s;
the graded image of T_s is B_s. In E_r = Z_r/B_r, the kernel of d_r
is Z_(r+1)/B_r. Indeed, if dx is an r-boundary in filtration degree
p+r modulo F^(p+r+1), locally lift its boundary expression as dy
with y in F^(p+1), and replace x by x-y. This does not change its
graded class and makes its differential lie in F^(p+r+1). Conversely
any such representative is killed by d_r. Here local lifting means
pulling back along an epimorphism, which suffices to compute image
subobjects in an arbitrary abelian category; no projectivity is used.
The image of the incoming d_r is B_(r+1)/B_r: its source has filtration
degree p-r, and its differential lies in F^p, exactly the condition
defining T_(r+1). The same image argument gives both containments.
The equation on representatives in D identifies these maps with its
differentials. Since d squared is zero, B_(r+1) lies in Z_(r+1).
Finally the abelian quotient-of-quotients isomorphism identifies
(Z_(r+1)/B_r)/(B_(r+1)/B_r) with Z_(r+1)/B_(r+1), the concrete
cokernel on the right. All image and quotient computations are
componentwise and use finite limits and cokernels only. -/
theorem filteredComplex_page_homology
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ) :
    Nonempty (D.page.homology pq ≅ filteredComplexPageObject K F (r + 1) pq) := by sorry

end CategoryTheory
