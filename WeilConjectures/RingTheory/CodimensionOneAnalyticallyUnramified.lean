/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Colon
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.FlatAssociatedPrimeDVR
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# DVR localizations of the completion at associated primes

If `R` is Noetherian local, `R_p` is a DVR and `p` is analytically unramified, then the
completion of `R` localized at any associated prime of `R^/pR^` is a DVR.

## Implementation details

Let `C` be the localization of the completion at `q = Ann(z)`. Since `R^/pR^` is the completion
of `R/p`, it is reduced, which gives `qC = pC`. Flatness of the completion shows that elements
outside `p` map outside `q`; choosing `x ∈ p` generating `pR_p`, one gets `qC = xC` with `x` a
nonzerodivisor in `C`. Krull's intersection theorem then shows that `C` is a domain with nonzero
principal maximal ideal, hence a DVR.

## References

* [Stacks, Tag 032Z]
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- If `R` is Noetherian local, `R_p` is a DVR, and `p` is analytically unramified, then the
completion localized at any associated prime of its quotient by the extended ideal `p` is a DVR.
The colon of the zero submodule by `{z}` is exactly the annihilator of `z` (without taking a
radical). -/
theorem isDiscreteValuationRing_atPrime_of_isAnalyticallyUnramified
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)] (hp : p.IsAnalyticallyUnramified)
    (q : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) [q.IsPrime]
    (hq : ∃ z : AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
        p.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)),
      q = (⊥ : Submodule (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
          p.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))).colon {z}) :
    ∃ (_ : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have : IsNoetherianRing A := AdicCompletion.isNoetherianRing _
  obtain ⟨_, _, _, _, _, _, e, _⟩ :=
    exists_local_completion_quotient R (R ⧸ p) (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  have : IsReduced
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk p))
        (R ⧸ p)) := hp.2
  have : IsReduced (A ⧸ p.map (algebraMap R A)) := by
    have h := isReduced_of_injective e e.injective
    rw [Ideal.mk_ker] at h
    exact h
  exact isDiscreteValuationRing_atPrime_of_flat_reduced_quotient R A p q hq

end AdicCompletion
