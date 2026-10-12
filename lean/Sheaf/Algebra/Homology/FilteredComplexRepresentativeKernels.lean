/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # The kernel calculation on cycle representatives

Source: Stacks Project, Tag 012K, displayed cycle-boundary formulas.
(blueprint: lem-sp-filtered-complex-representative-kernels)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

/-- The two maps out of cycle representatives have the same kernel.
Source: Stacks Project, Tag 012K, displayed formulas for Z_r and B_r.
(blueprint: lem-sp-filtered-complex-representative-kernels)

Proof: The projection square identifies the image of a representative x in T with
its class modulo F^{p+1}. Its homology class vanishes exactly when this class is a
boundary, that is, locally on an epimorphic cover x = dy + f with y in F^{p-r+1}
and f in F^{p+1}. Since x and f belong to F^p, dy belongs to F^p as well. Thus the
kernel is the inverse image in R of the image in the graded piece of
(F^p intersect d(F^{p-r+1})) + F^{p+1}, which is B by definition. Conversely a
representative in that inverse image has precisely this decomposition and maps to
a boundary in T. The kernel of Z → Z/B is B, since B → Z is mono in an abelian
category. Pulling it back along z gives the same subobject of R. The epimorphic
covers here express the usual image and sum subobject universal properties, and
the two inclusions descend, so the calculation is valid without assuming C is a
concrete category. -/
theorem filteredComplex_representative_kernels (F : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r)
    (hBZ : F.complexBoundaries p n r ≤ F.complexCycles p n r)
    (ha : p - r + 1 ≤ p) (hb : p + 1 ≤ p + r) :
    let hs := (Int.le_add_one (show p ≤ p from le_rfl)).trans hb
    let ht := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
    let R := F.complexCycleRepresentatives p n r
    let Z := F.complexCycles p n r
    let B := F.complexBoundaries p n r
    let S := F.complexQuotient p (p + r) hs
    let T := F.complexQuotient (p - r + 1) (p + 1) ht
    ∀ (φ : S ⟶ T),
      F.complexQuotientπ p (p + r) hs ≫ φ =
        Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step ha) ≫
          F.complexQuotientπ (p - r + 1) (p + 1) ht →
      ∀ (z : (R : C) ⟶ (Z : C)) (g : (R : C) ⟶ S.cycles n),
        z ≫ Z.arrow = R.arrow ≫
          (F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n →
        g ≫ S.iCycles n = R.arrow ≫ (F.complexQuotientπ p (p + r) hs).f n →
        kernelSubobject (z ≫ cokernel.π (Subobject.ofLE B Z hBZ)) =
          kernelSubobject (g ≫ S.homologyπ n ≫ HomologicalComplex.homologyMap φ n) := by
  sorry

end CategoryTheory.DecreasingFiltration
