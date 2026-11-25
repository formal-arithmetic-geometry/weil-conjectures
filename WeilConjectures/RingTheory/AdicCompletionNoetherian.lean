/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.PowerSeriesOntoCompletion
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of adic completion

We show that the adic completion of a Noetherian ring with respect to any ideal is Noetherian.

## Implementation details

The completion is a quotient of a multivariate power series ring over `A`, via substituting
generators of the ideal for the variables, and such power series rings are Noetherian.

## References

* Stacks Project, Lemma 10.97.6 (Tag 0316), second proof.
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- The completion of a Noetherian commutative ring with respect to any ideal is Noetherian. -/
theorem isNoetherianRing {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    IsNoetherianRing (AdicCompletion I A) := by
  obtain ⟨n, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨Φ, _, hΦ, _, _⟩ :=
    MvPowerSeries.exists_surjective_toAdicCompletion n f I hf.symm
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) A) _ Φ hΦ

end AdicCompletion
