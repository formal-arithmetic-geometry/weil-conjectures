/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.Filtration

/-!
# Positive pages of a filtered complex

Source: Stacks Project, Homology, Tag 012K and Remark 12.18.2
(blueprint: lem-sp-filtered-complex-positive-pages).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The positive-page sequence, without its initial graded complex.
Source: Stacks Project, Homology, Tag 012K, proof of
`lemma-spectral-sequence-filtered-complex`, and `remark-differential-object-selfmap`.
(blueprint: lem-sp-filtered-complex-positive-pages).

Proof. Work in the abelian category of bigraded objects, using componentwise kernels
and cokernels; no infinite coproducts in C are required. Give
A(p,q) = F^(p+1) K^(p+1+q) its differential of degree (0,1).
The filtration inclusions give an injective map A -> A[-1,1] commuting with d.
The homology long exact sequence of its cokernel gives the shifted exact couple
of Remark 12.18.2. Derive this couple successively, beginning with its homology
term E1, to obtain complexes with differential of degree (r,1-r) and isomorphisms
H(E_r) = E_(r+1). The exact-couple calculation identifies the cycles with the image
of the inverse image of the r-fold inclusion under d, and the boundaries with the
image of the inverse image of dA under the (r-1)-fold inclusion. Componentwise these
are the subobjects complexCycles and complexBoundaries: the sums with F^(p+1)
ensure that both are subobjects of the graded quotient. The equation d squared = 0
puts boundaries inside cycles. Their quotient is the corresponding page object.
-/
theorem filteredComplex_positive_spectralSequence
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    ∃ E : CohomologicalSpectralSequence C 1,
      ∀ (p q r : ℤ) (hr : 1 ≤ r),
        ∃ hBZ : F.complexBoundaries p (p + q) r ≤ F.complexCycles p (p + q) r,
          Nonempty ((E.page r).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)) := by
  sorry

end CategoryTheory
