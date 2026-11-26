/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.PolynomialCompleteLocalFibreReduction
import WeilConjectures.RingTheory.PolynomialCompleteLocalGenericFibre
import WeilConjectures.RingTheory.PolynomialCompleteLocalNonzeroFibreCharZero
import WeilConjectures.RingTheory.PolynomialFormalFiber

/-!
# Formal fibres of polynomial rings over complete local rings

For a complete local Noetherian ring `S` and a maximal ideal `Q` of `S[x]` over the maximal ideal
of `S`, the completion map of `S[x]_Q` is regular.

## Implementation details

With `T = S[x]_Q` and `C` its completion, `T → C` is flat with Noetherian fibres, so it suffices
to show that each fibre over a prime `r` is geometrically regular. Passing to `A = S / (r ∩ S)`
reduces to a complete local domain, which is finite over a regular complete local subring `A₀`;
quasi-finite ascent reduces to `A₀[x]`, whose completion is regular. The generic fibre is a
localization of it; a nonzero fibre in characteristic zero is a regular hypersurface by a
derivation argument; in characteristic `p` the auxiliary G-ring lemmas apply.

## References

* [Stacks, Tag 07PV] (paragraphs 2–5 of the proof)
-/

@[expose] public section

universe u

namespace Polynomial

/-- For a complete local Noetherian ring `S` and a maximal ideal `Q` of `S[x]` over the maximal
ideal of `S`, the completion map of `S[x]_Q` is regular. -/
theorem isRegular_algebraMap_adicCompletion_localization
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (Q : Ideal (Polynomial S)) [Q.IsMaximal]
    (hQ : Q.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S) :
    RingHom.IsRegular
      (algebraMap (Localization.AtPrime Q)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q))) := by
  classical
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  intro s hs
  obtain ⟨A, hA, hdom, hnoeth, hlocal, hcomplete, q, r, hqmax, hrprime,
    hq, hrq, hrA, htransfer⟩ := exists_completeLocalDomain_fibre_reduction S Q hQ s
  let := hA
  let := hdom
  let := hnoeth
  let := hlocal
  let := hcomplete
  let := hqmax
  let := hrprime
  apply htransfer
  by_cases hr : r = ⊥
  · subst r
    exact completeLocalGenericFibre A q hq
  · rcases CharP.exists' (Localization.AtPrime (⊥ : Ideal A)) with hzero | ⟨p, hp, hchar⟩
    · let := hzero
      exact completeLocalNonzeroFibreCharZero A q hq r hrq hr hrA
    · let := hchar
      exact (formalFiber_isGeometricallyRegular A p hp.out q hq r hrq hr hrA).2

end Polynomial
