/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.Submodule

/-!
# Noetherian fibre rings

The fibre ring `p.Fiber B = κ(p) ⊗[A] B` of a Noetherian algebra is Noetherian.

## Implementation details

The fibre is a quotient of the localization `Bₚ` of `B` at the image of `A ∖ p`, which is
Noetherian since `B` is.

## References

* [Stacks, Tag 00E6], [Stacks, Tag 00FN]
-/

@[expose] public section

universe u v

namespace Ideal

/-- The fibre ring of a Noetherian algebra at any prime of the base is Noetherian. -/
theorem isNoetherianRing_fiber
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] (p : Ideal A) [p.IsPrime] :
    IsNoetherianRing (p.Fiber B) := by
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let S := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  have : IsNoetherianRing S := inferInstance
  exact isNoetherianRing_of_ringEquiv _ (Fiber.algEquivQuotient (S := B) p).symm.toRingEquiv

end Ideal
