/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-! # The degreewise image of the total good-truncation inclusion

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

/-- The boundary kernel gives the image of the good-cut total on a nonempty cut diagonal.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-good-truncation-total-boundary-image).

Proof. In degree n the total is the finite direct sum of M^(p,n-p), 0<=p<=n.
The second filtration at n-q is its direct sum over p<=q. Inside it, the inverse
image of the next vertical step under the total differential is the kernel of
its composite with projection onto the remaining boundary summand at p=q+1.
All vertical differentials and horizontal differentials from p<q already land
in that next step. Thus this kernel retains the full terms with p<q and replaces
the boundary p=q term by its horizontal kernel. Evaluating the horizontal good
truncation gives exactly these terms. The finite direct-sum inclusions and kernel
lifts show both containments of the displayed subobjects. Terms with p>q in the
cut vanish, while omitted negative-index terms vanish by hM. The assumptions
0<=q<=n ensure that the boundary summand has a nonnegative
vertical index. At q=0 there are no retained strict columns, so the same kernel
calculation applies without a preceding direct-sum summand. -/
theorem good_truncation_total_boundary_image
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hM : ∀ p r : ℤ, p < 0 ∨ r < 0 → IsZero ((M.X p).X r))
    (q : ℤ) (hq : 0 ≤ q) (n : ℤ) (hqn : q ≤ n) :
    imageSubobject ((total.map (CochainComplex.ιTruncLE M q)
      (ComplexShape.up ℤ)).f n) =
      (M.secondFiltration n).step (n - q) ⊓
        (Subobject.pullback ((M.total (ComplexShape.up ℤ)).d n (n + 1))).obj
          ((M.secondFiltration (n + 1)).step (n - q + 1)) := by
  sorry

end HomologicalComplex₂
