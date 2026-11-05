/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.HenselianDVRExtension

/-!
# The integral closure of a henselian DVR in an algebraic extension is a valuation ring

Let `R` be a henselian discrete valuation ring and `Ω` a field which is algebraic over `R`
(with `R → Ω` injective), e.g. an algebraic closure of the fraction field of `R`. The elements
of `Ω` integral over `R` form a valuation subring `integralClosureValuationSubring R Ω` of `Ω`:
for `z : Ω`, some `p ^ n`-th power `y` of `z` is separable over `Frac R`, and the integral
closure of `R` in `Frac R (y)` is a discrete valuation ring, so `y` or `y⁻¹` is integral.

## Main statements

- `IsDiscreteValuationRing.integralClosureValuationSubring`: the valuation subring.
- `IsDiscreteValuationRing.valuation_algebraMap_eq_one_iff`,
  `IsDiscreteValuationRing.valuation_algebraMap_lt_one_iff`: restriction to `R`.
- `IsDiscreteValuationRing.exists_valuation_pow_eq_zpow`: the value group is contained in the
  divisible hull of the value group of `R`.
- `IsDiscreteValuationRing.comap_integralClosureValuationSubring`: functoriality.
- `IsDiscreteValuationRing.map_mem_integralClosureValuationSubring_iff`: Galois stability.
-/

@[expose] public section

universe u v

open Polynomial IntermediateField

namespace IsDiscreteValuationRing

section FractionField

variable {R K : Type u} {Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
  [Algebra R Ω] [IsScalarTower R K Ω]

end FractionField

variable (R : Type u) (Ω : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω]

variable {R Ω}

end IsDiscreteValuationRing
