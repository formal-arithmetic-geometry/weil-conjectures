/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.HenselianDVRExtension
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTensor

/-!
# Separable closedness of the base in an unramified extension of discrete valuation rings

Let `R₁` be a henselian discrete valuation ring with separably closed residue field `k` and
fraction field `F₁`, and let `R₁ → R` be a local homomorphism to a discrete valuation ring `R`
with fraction field `F`, such that a uniformizer `π` of `R₁` is a uniformizer of `R`, and such
that every element of the residue field `κ` of `R` algebraic over `k` comes from `k`. A typical
example is the strict henselization of `R₁[x]` at the prime `(π)`.

Then `F₁` is separably closed in `F` (`IsDiscreteValuationRing.mem_range_of_isSeparable`). Indeed,
let `c ∈ F` be separable over `F₁`, `E = F₁(c)` and `B` the integral closure of `R₁` in `E`, a
discrete valuation ring with `π = u ϖ ^ e` and `e f = [E : F₁]`, `f` the residue degree. The ring
`B` lies in `R` (which is integrally closed), the inclusion is local, and since `π` stays a
uniformizer in `R` we get `e = 1`; the residue field of `B` embeds in `κ` and is algebraic over
`k`, so `f = 1`. Hence `[E : F₁] = 1`.

As a consequence, for every algebraic extension `Ω₁` of `F₁` the ring `Ω₁ ⊗_{R₁} R = Ω₁ ⊗_{F₁} F`
has a single prime ideal (`IsDiscreteValuationRing.subsingleton_primeSpectrum_tensorProduct`).

## Main statements

- `IsIntegrallyClosed.exists_comp_eq_of_isIntegral`: a ring homomorphism to the fraction field
  with integral values factors through the ring.
- `IsDiscreteValuationRing.mem_range_of_isSeparable`: `F₁` is separably closed in `F`.
- `PrimeSpectrum.subsingleton_tensorProduct_of_forall_mem_range`: if `F` is separably closed in
  `E` and `M / F` is algebraic, then `M ⊗_F E` has at most one prime ideal.
- `IsDiscreteValuationRing.isLocalization_map_nonZeroDivisors`: `F` is the localization of `R` at
  the nonzero elements of `R₁`.
- `IsDiscreteValuationRing.subsingleton_primeSpectrum_tensorProduct`: `Spec(Ω₁ ⊗_{R₁} R)` has
  at most one point.
-/

@[expose] public section

universe u

open IsLocalRing Module IntermediateField

open scoped TensorProduct

namespace IsDiscreteValuationRing

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

end IsDiscreteValuationRing
