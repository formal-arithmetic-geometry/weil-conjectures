/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.SmoothNormalRing

/-!
# Normality ascends along etale ring maps

An étale algebra over a normal ring is normal.

## Implementation details

Normality of a ring is written out as in
`CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit`: every localization at a
prime ideal is an integrally closed domain. Étale ring maps are smooth, and normality ascends
along smooth ring maps.

## References

* Stacks Project, Tags 0309, 00GV (normal rings)
* Stacks Project, Algebra, Lemma Tag 033C, applied as in More on Algebra, Lemma Tag 06DI
* Stacks Project, Tag 02GJ
-/

@[expose] public section

universe uA uB

namespace RingHom

/-- An etale algebra over a normal ring is normal: if `f : A →+* B` is etale and every
localization of `A` at a prime is an integrally closed domain, then so is every
localization of `B` at a prime. -/
theorem Etale.isNormalRing {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.Etale)
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  exact ((etale_iff_formallyUnramified_and_smooth f).mp hf).2.isNormalRing hA

end RingHom
