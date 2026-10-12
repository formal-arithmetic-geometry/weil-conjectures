/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.CategoryTheory.Filtration

/-! # The natural quotient-complex image comparison

Source: Stacks Project, Homology, Tag 012K
(blueprint: lem-sp-filtered-complex-quotient-image-comparison).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

/-- The natural image comparison for the cycle-boundary quotient.
Source: Stacks Project, Tag 012K, displayed cycle-boundary formulas, with the
quotient-complex calculation in step 3 of lem-sp-filtered-complex-ZB-description.
(blueprint: lem-sp-filtered-complex-quotient-image-comparison)

Proof: The inequalities p-r+1 ≤ p and p+1 ≤ p+r follow from r ≥ 1. The inclusion
F^p → F^{p-r+1}, followed by projection modulo F^{p+1}, kills F^{p+r}, and hence
factors through the cokernel S, giving φ with the required projection square.
Let R = F^p ∩ d⁻¹(F^{p+r}) inside F^p. Its projection to the graded piece factors
through Z by the image universal property, giving z. Its projection to S is killed
by the differential, so factors through the kernel S.cycles n, giving g.
The composite R → H(S) → H(T) has image image Hφ: R surjects onto the cycles of S,
and cycles surject onto H(S). Its kernel consists exactly of representatives dy+f
with y in F^{p-r+1} and f in F^{p+1}. Since the representative and f lie in F^p,
dy lies in F^p ∩ d(F^{p-r+1}); conversely these boundaries lie in R by d²=0.
The map R → Z → Z/B is epic and has the same kernel. The abelian first isomorphism
theorem therefore identifies Z/B with image Hφ. Taking this induced isomorphism,
rather than any isomorphism, gives the required equality on representatives. -/
theorem filteredComplex_quotient_image_comparison (F : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r)
    (hBZ : F.complexBoundaries p n r ≤ F.complexCycles p n r) :
    let Z := F.complexCycles p n r
    let B := F.complexBoundaries p n r
    ∃ (ha : p - r + 1 ≤ p) (hb : p + 1 ≤ p + r),
      let hs := (Int.le_add_one (show p ≤ p from le_rfl)).trans hb
      let ht := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
      let S := F.complexQuotient p (p + r) hs
      let T := F.complexQuotient (p - r + 1) (p + 1) ht
      ∃ φ : S ⟶ T,
        F.complexQuotientπ p (p + r) hs ≫ φ =
          Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step ha) ≫
            F.complexQuotientπ (p - r + 1) (p + 1) ht ∧
        let R := F.complexCycleRepresentatives p n r
        let Hφ := HomologicalComplex.homologyMap φ n
        ∃ (z : (R : C) ⟶ (Z : C)) (g : (R : C) ⟶ S.cycles n),
          z ≫ Z.arrow = R.arrow ≫
            (F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n ∧
          g ≫ S.iCycles n = R.arrow ≫ (F.complexQuotientπ p (p + r) hs).f n ∧
          ∃ e : cokernel (Subobject.ofLE B Z hBZ) ≅ image Hφ,
            z ≫ cokernel.π (Subobject.ofLE B Z hBZ) ≫ e.hom ≫ image.ι Hφ =
              g ≫ S.homologyπ n ≫ Hφ := by
  sorry

end CategoryTheory.DecreasingFiltration
