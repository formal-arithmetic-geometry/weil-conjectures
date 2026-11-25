/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalOfFormallySmoothAdic

/-!
# Smooth algebras over fields have regular local rings

Every localization at a prime of a smooth algebra over a field is a regular local ring.

## Implementation details

`A` is Noetherian, and formal smoothness over `k` passes to `A_q` and makes it formally smooth
for the maximal-ideal-adic topology; then `Algebra.isRegularLocalRing_of_formallySmoothAdic`
(Stacks 07EI) applies.

## References

* [Stacks, Tag 00TT]
* [Stacks, Tag 07EI]
-/

@[expose] public section

universe u v

namespace Algebra

/-- If `A` is a smooth algebra over a field, every localization at a prime ideal
is a regular local ring. -/
theorem smooth_over_field_regular_local
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  apply isRegularLocalRing_of_formallySmoothAdic k (Localization.AtPrime q)
  intro D _ _ J hJ g _
  exact FormallySmooth.comp_surjective k (Localization.AtPrime q) J hJ g

end Algebra
