/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex

/-!
# Koszul-regular and H₁-regular sequences

This file defines Koszul-regular and H₁-regular sequences, absolutely and relative to a module.

## Implementation details

The Koszul complex is indexed by `ℕ`, so vanishing in all nonzero integer degrees means
vanishing in all nonzero natural degrees. Homology is Mathlib's kernel-modulo-image homology,
and `IsZero` expresses that it vanishes without choosing an equality to a zero object.

## References

* [Stacks, Tag 062E]
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RingTheory.Sequence

/-- `M`-Koszul-regularity: all nonzero homology of `K_•(f) ⊗[R] M` vanishes.
The tensor complex is the degreewise tensor construction, with differentials `d ⊗ id_M`. -/
def IsKoszulRegularOn {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) : Prop :=
  ∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplexTensor R r f M).homology i)

/-- `M`-H₁-regularity: the first homology of `K_•(f) ⊗[R] M` vanishes. -/
def IsH1RegularOn {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) : Prop :=
  IsZero ((ExteriorAlgebra.koszulComplexTensor R r f M).homology 1)

/-- Koszul-regularity: all nonzero homology of `K_•(f)` vanishes. -/
def IsKoszulRegular {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) : Prop :=
  ∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplex R r f).homology i)

/-- H₁-regularity: the first homology of `K_•(f)` vanishes. -/
def IsH1Regular {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) : Prop :=
  IsZero ((ExteriorAlgebra.koszulComplex R r f).homology 1)

end RingTheory.Sequence
