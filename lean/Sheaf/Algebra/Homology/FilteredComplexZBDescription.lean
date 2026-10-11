/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Cycles and boundaries of a filtered complex

Source: Stacks Project, Homology, Tag 012K, Lemma on the filtered-complex spectral sequence
and its displayed cycle-boundary formulas (blueprint: lem-sp-filtered-complex-ZB-description).
-/

universe vZ uZ

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- Cycles, boundaries, quotient-complex image description, first page and stabilization.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-ZB-description).

Proof: (1) Apply the graded differential-object construction of
`lem-sp-filtered-complex-associated-spectral-sequence-construction` to the bigraded object
with component `Fᵖ⁺¹Kᵖ⁺¹⁺q` and shift inclusion into `FᵖKᵖ⁺¹⁺q`. This gives the spectral
sequence with differential of bidegree `(r, 1-r)` and initial page `grᵖKᵖ⁺q`.
(2) Unwind its kernels and images to obtain the displayed cycle and boundary subobjects.
The square-zero differential sends every boundary to zero, so `Bᵣ ≤ Zᵣ`; the page is their
quotient. These steps use the construction node and `def-sp-filtration`.
(3) A representative in `Fᵖ ∩ d⁻¹(Fᵖ⁺ʳ)` is a cocycle modulo `Fᵖ⁺ʳ` and also modulo
`Fᵖ⁺¹` since `r ≥ 1`. Its target cohomology class vanishes precisely when it is `dy + f`
with `y ∈ Fᵖ⁻ʳ⁺¹` and `f ∈ Fᵖ⁺¹`. Then `dy = x-f` lies in `Fᵖ ∩ d(Fᵖ⁻ʳ⁺¹)`.
Conversely such a boundary is a cycle because `d²=0`. Thus the image has exactly the kernel
of the projection onto `Zᵣ/Bᵣ`. The induced isomorphism is specified below on these
representatives, so it is the natural comparison, rather than an arbitrary object
isomorphism. This uses `def-sp-abelian` and `def-sp-filtration`.
(4) For `r=1`, the conditions become the kernel and image of the graded differential,
giving the homology of the graded complex. For fixed `p,q`, finiteness of the filtration
(`def-sp-filtration`), hence in degrees `p+q+1` and `p+q-1`, makes the two filtration
tails respectively zero and the whole object for large `r`; hence both subobjects, and
consequently their quotient pages, stabilize. -/
theorem filteredComplex_ZB_description
    {C : Type uZ} [Category.{vZ} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (hF : F.IsFinite) :
    ∃ E : CohomologicalSpectralSequence C 0,
      (∀ p n : ℤ,
        F.complexCycles p n 1 = kernelSubobject ((F.gradedPiece p).d n (n + 1)) ∧
        F.complexBoundaries p n 1 = imageSubobject ((F.gradedPiece p).d (n - 1) n)) ∧
      (∀ p q : ℤ,
        Nonempty ((E.page 1).X (p, q) ≅ (F.gradedPiece p).homology (p + q))) ∧
      (∀ (p q r : ℤ) (hr : 1 ≤ r),
        let n := p + q
        let Z := F.complexCycles p n r
        let B := F.complexBoundaries p n r
        ∃ hBZ : B ≤ Z,
          Nonempty ((E.page r (le_trans (show 0 ≤ 1 from zero_le_one) hr)).X (p, q) ≅
            cokernel (Subobject.ofLE B Z hBZ)) ∧
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
                    g ≫ S.homologyπ n ≫ Hφ) ∧
      (∀ p q : ℤ, ∃ (R : ℤ) (hR : 1 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
        F.complexCycles p (p + q) r = F.complexCycles p (p + q) R ∧
        F.complexBoundaries p (p + q) r = F.complexBoundaries p (p + q) R ∧
        Nonempty
          ((E.page r (le_trans (le_trans (show 0 ≤ 1 from zero_le_one) hR) hr)).X (p, q) ≅
            (E.page R (le_trans (show 0 ≤ 1 from zero_le_one) hR)).X (p, q))) := by
  sorry

end CategoryTheory.DecreasingFiltration
