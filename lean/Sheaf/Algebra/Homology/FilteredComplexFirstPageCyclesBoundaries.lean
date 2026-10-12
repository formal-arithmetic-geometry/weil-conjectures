/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.Filtration

/-! # The first-page cycles and boundaries of a filtered complex

Source: Stacks Project, Homology, Tag 012K
(blueprint: lem-sp-filtered-complex-first-page-cycles-boundaries).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

/-- The page-one cycle and boundary formulas.
Source: Stacks Project, Tag 012K, displayed formulas and Lemma 12.24.2.
(blueprint: lem-sp-filtered-complex-first-page-cycles-boundaries)

Proof: Write m_n for the inclusion F^pK^n → K^n, l_n for the inclusion
F^{p+1}K^n → F^pK^n and q_n for the graded projection. Evaluation of the cokernel
sequence of complexes is a cokernel sequence, so q_n is epic and its kernel is
image l_n. The graded differential δ satisfies q_n ≫ δ = d_p ≫ q_{n+1}, where d_p
is the differential restricted to F^p. Pulling back ker δ along q_n therefore gives
the inverse image under d_p of image l_{n+1}. Under the mono m_n this is precisely
F^pK^n ∩ d⁻¹(F^{p+1}K^{n+1}). It contains F^{p+1}K^n since the steps are subcomplexes,
so the extra sum in complexCycles is redundant. The image under an epimorphism of
the pullback of a subobject is that subobject. Applying this to ker δ proves the
cycle formula.
For boundaries, q_{n-1} is epic, hence image δ = image(q_{n-1} ≫ δ) =
image(d_p ≫ q_n). Under m_n, image d_p is d(F^pK^{n-1}), which is contained in
F^pK^n by the subcomplex condition; thus the intersection in complexBoundaries at
r=1 is redundant. Pullback along the mono m_n recovers image d_p. Adding the
subobject F^{p+1} before applying q_n has no effect on its image, since q_n kills
that subobject. The resulting image is exactly image(d_p ≫ q_n) = image δ. -/
theorem filteredComplex_firstPage_cycles_boundaries (F : DecreasingFiltration K) :
    ∀ p n : ℤ,
      F.complexCycles p n 1 = kernelSubobject ((F.gradedPiece p).d n (n + 1)) ∧
      F.complexBoundaries p n 1 = imageSubobject ((F.gradedPiece p).d (n - 1) n) := by
  sorry

end CategoryTheory.DecreasingFiltration
