/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Stationary quotients for a degreewise finite filtered complex

Source: Stacks Project, Tags 012Q, 012W and 0132.
(blueprint: lem-sp-degreewise-filtered-stable-quotient).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The stationary cycle/boundary quotient is the graded image filtration on cohomology.
Only degreewise finiteness is needed; no spectral sequence is part of this statement.
Source: Stacks Project, Tags 012Q (stable subquotients),
012W (degreewise finite convergence) and 0132.
(blueprint: lem-sp-degreewise-filtered-stable-quotient).

Proof.
For each n define the p-th step on H^n(K) to be the image of H^n(L^pK) → H^n(K).
The factorization through L^pK of the inclusion of L^qK for p ≤ q gives
antitonicity. Pick bounds for degrees n-1,n,n+1. For p below all their lower
bounds the subcomplex inclusion is an isomorphism in these three degrees, so
its homology image is top. Above the upper bound in degree n its homology
image is zero. Thus the image filtration is finite.
Fix p,n. Choose t ≥ 1 so that L^(p+t)K^(n+1)=0 and
L^(p-t+1)K^(n-1)=K^(n-1). Antitonicity keeps these equalities true for every
r ≥ t. In the formulas for Z_r and B_r the outer steps can therefore be
replaced by zero and the whole object. The cycles are the images in gr^pK^n
of actual cycles in L^pK^n, while the boundaries are the images of actual
boundaries of K intersected with L^pK^n. The abelian subquotient isomorphism
identifies Z_r/B_r with the quotient of the image of H^n(L^pK) by the image
of H^n(L^(p+1)K). This is the graded piece of the image filtration.
For a family c_n:H^n(K) ≅ Y^n, take direct images of these steps along c_n.hom.
Their antitonicity is preserved by the direct-image functor. Since each c_n
is an isomorphism, direct image preserves top and bottom and identifies the
successive inclusion arrows up to isomorphism. Applying the cokernel functor
to these squares gives the graded-piece comparisons. This yields the exact
step formula, finiteness and stationary-quotient isomorphisms below. -/
theorem degreewiseFiltered_stable_quotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (L : DecreasingFiltration K)
    (hfinite : ∀ n : ℤ, ∃ lo hi : ℤ,
      L.complexStep lo n = ⊤ ∧ L.complexStep hi n = ⊥)
    (Y : ℤ → C) (c : ∀ n : ℤ, K.homology n ≅ Y n) :
    ∃ H : ∀ n : ℤ, DecreasingFiltration (Y n),
      (∀ n : ℤ, (H n).IsFinite) ∧
      (∀ p n : ℤ, (H n).step p =
        (Subobject.«exists» (c n).hom).obj
          (imageSubobject (HomologicalComplex.homologyMap (L.step p).arrow n))) ∧
      (∀ p n : ℤ, ∃ (t : ℤ) (ht : 1 ≤ t), ∀ (r : ℤ) (hr : t ≤ r),
        ∃ hBZ : L.complexBoundaries p n r ≤ L.complexCycles p n r,
          Nonempty (cokernel (Subobject.ofLE _ _ hBZ) ≅ (H n).gradedPiece p)) := by sorry

end CategoryTheory
