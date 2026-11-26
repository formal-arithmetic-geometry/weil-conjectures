/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Tensor Koszul homology for a complementary regular quotient

If the images of a sequence `g` in `A ⧸ J` form a regular sequence, the tensor Koszul complex
`K_•(g) ⊗[A] (A ⧸ J)` has no positive homology.

## Implementation details

The images of `g` are weakly regular on `A ⧸ J` exactly when `g` is weakly regular on it as an
`A`-module (`isWeaklyRegular_map_algebraMap_iff`), and weakly regular sequences are
Koszul-regular (`isKoszulRegularOn_of_isWeaklyRegular`).

## References

* [Stacks, Tag 0B1I]
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory

/-- The tensor Koszul complex on a sequence whose images form a regular sequence in a
quotient has no positive homology. -/
theorem regularLocal_complementary_tensor_homology_vanishing
    (A : Type u) [CommRing A] (r : ℕ) (J : Ideal A) (g : Fin r → A)
    [IsRegularLocalRing (A ⧸ J)]
    (hreg : RingTheory.Sequence.IsRegular (A ⧸ J)
      (List.ofFn (fun i ↦ Ideal.Quotient.mk J (g i)))) :
    ∀ n : ℕ, 0 < n →
      IsZero ((ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J)).homology n) := by
  intro n hn
  have hweak : RingTheory.Sequence.IsWeaklyRegular (A ⧸ J) (List.ofFn g) := by
    rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (A ⧸ J) (A ⧸ J)]
    simpa [List.map_ofFn, Function.comp_def] using hreg.toIsWeaklyRegular
  exact RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular (A ⧸ J) g hweak n
    (Nat.pos_iff_ne_zero.mp hn)

end RingTheory
