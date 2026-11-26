/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulConormalComparisonMap
import WeilConjectures.RingTheory.KoszulConormalComparisonQuasiIso

/-!
# Existence of the determinant-normalized dual Koszul comparison

For a Koszul-regular sequence generating `I`, there is a determinant-normalized
quasi-isomorphism from the dual Koszul complex to the normal determinant in degree `r`.

## Implementation details

With `c_i` the conormal basis, `e_top` the ordered top wedge and `s = (-1)^(r(r-1)/2)`, the top
component sends `x` to `s · (x(e_top) mod I) · ∧ c_i^*`; all other components vanish. The
preceding dual differential has top evaluation in `I`, so this is a cochain map. The
complementary-wedge equivalences identify the dual complex with the Koszul complex up to
signs, so Koszul-regularity gives exactness away from `r`, and the top cokernel is `A/I`.

## References

* [Stacks, Tag 0BQZ]
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- There is a determinant-normalized quasi-isomorphism from the dual Koszul complex
to the normal determinant in degree `r`. -/
theorem exists_koszul_conormal_comparison
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ φ : koszulDualComplex A r f ⟶
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
          (koszulNormalDeterminant A I r),
      IsKoszulConormalComparison A I r f hf φ ∧ QuasiIso φ := by
  obtain ⟨φ, hφ⟩ := exists_koszul_conormal_comparison_map A I r f hreg hf
  exact ⟨φ, hφ, koszul_conormal_comparison_is_quasiIso A I r f hreg hf φ hφ⟩

end ExteriorAlgebra
