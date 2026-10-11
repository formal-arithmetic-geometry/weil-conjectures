/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Quasi-finiteness at a prime over an intermediate ring

Source: Stacks Project, Algebra, Lemma 10.122.10 (Tag 0C6H)
(blueprint: lem-weil-pbc-quasi-finite-at-prime-permanence).
-/

universe u v w

namespace Algebra

/-- (blueprint: lem-weil-pbc-quasi-finite-at-prime-permanence) If `A → B → C` is a
commutative ring tower, `C` is of finite type over `A`, and `A → C` is quasi-finite at
`r`, then `B → C` is quasi-finite at `r` (Stacks Project, Algebra, Tag 0C6H).

Proof: First, finite algebra generators over `A` also generate over `B`
(`def-weil-pbc-finite-type-algebra`). Put `q = r ∩ B` and `p = r ∩ A`. The induced
residue-field map `κ(p) → κ(q)` gives a ring map between the fibre rings
`κ(p) ⊗[A] C → κ(q) ⊗[B] C`, compatible with their maps from `C`
(`def-weil-pbc-localization-at-prime`). By `lem-weil-pbc-fibre-ring-primes-bijection`,
the inverse image under the spectrum map of the singleton corresponding to `r` in the
first fibre is exactly the singleton corresponding to `r` in the second fibre: both
are characterized by contraction to `r` in `C`. The spectrum map is continuous
(`def-weil-affine-spectrum`), so openness of the first singleton implies openness of
the second (`def-weil-pbc-ring-map-quasi-finite-at-prime`). The finite-type proof needed
in the conclusion is supplied by Mathlib's finite-type permanence theorem. -/
theorem IsQuasiFiniteAtPrime.of_restrictScalars
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [FiniteType A C] (r : PrimeSpectrum C) (hr : IsQuasiFiniteAtPrime A C r) :
    @IsQuasiFiniteAtPrime B C _ _ _
      (FiniteType.of_restrictScalars_finiteType A B C) r := by
  sorry

end Algebra
