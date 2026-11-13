/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Base change of a first order thickening

## References

* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
* [Stacks Project, Tag 01JU](https://stacks.math.columbia.edu/tag/01JU)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Base change of a first order thickening is a first order thickening, with ideal
`i.ker.comap p`. The two projections commute with `p` and `i`, giving a morphism of
thickenings (Stacks, Tags 09ZU, 01JU (1), and 04EX (5)). -/
theorem IsFirstOrderThickening.baseChange {W W' Z' : Scheme.{u}}
    (i : W ⟶ W') (p : Z' ⟶ W') (hi : IsFirstOrderThickening i) :
    IsFirstOrderThickening (pullback.fst p i) ∧
      (pullback.fst p i).ker = i.ker.comap p ∧
      (i.ker.comap p) ^ 2 = ⊥ ∧
      pullback.fst p i ≫ p = pullback.snd p i ≫ i := by
  let : IsClosedImmersion i := hi.1
  have hker := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i p
  have hsq : (i.ker.comap p) ^ 2 = ⊥ := by
    rw [← Scheme.IdealSheafData.comap_pow, hi.2, Scheme.IdealSheafData.comap_bot]
  exact ⟨⟨inferInstance, by rw [hker]; exact hsq⟩, hker, hsq, pullback.condition⟩

end AlgebraicGeometry
