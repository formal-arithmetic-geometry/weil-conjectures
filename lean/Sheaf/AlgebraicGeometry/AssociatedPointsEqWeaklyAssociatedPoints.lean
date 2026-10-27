/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.RingTheory.WeaklyAssociated
import Mathlib.RingTheory.Ideal.MinimalPrime.Colon

/-!
# Associated and weakly associated points of the structure sheaf

Source: Stacks Project, Divisors, Lemma 31.5.8 (Tag 05AR)
(blueprint: lem-sc-ass-weakass-locally-noetherian).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- On a locally Noetherian scheme, the associated points of the structure sheaf equal its
weakly associated points. Association means that the maximal ideal of the stalk is an
annihilator, and weak association means that it is minimal over an annihilator.
Source: Stacks Project, Divisors, Lemma 31.5.8 (Tag 05AR)
(blueprint: lem-sc-ass-weakass-locally-noetherian).

Proof:
1. The stalk at every point is Noetherian, by the Mathlib instance for locally Noetherian
   schemes.
2. A prime ideal equal to an element's annihilator is minimal over that annihilator,
   giving association implies weak association.
3. Conversely, apply `Submodule.exists_eq_colon_of_mem_minimalPrimes` to the zero submodule
   of the stalk ring. Over a Noetherian ring this realizes every prime minimal over an
   element's annihilator as the annihilator of another element. Set extensionality finishes. -/
theorem associatedPoints_eq_weaklyAssociatedPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    {x : X | ∃ a : X.presheaf.stalk x,
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        (⊥ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)).colon {a}} =
      {x : X | IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        Ideal.WeakAss (X.presheaf.stalk x)} := by
  ext x
  change (∃ a : X.presheaf.stalk x, _ = (⊥ : Submodule _ _).colon {a}) ↔
    ∃ a : X.presheaf.stalk x, _ ∈ ((⊥ : Submodule _ _).colon {a}).minimalPrimes
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · rintro ⟨a, ha⟩
    exact Submodule.exists_eq_colon_of_mem_minimalPrimes ha

end AlgebraicGeometry.Scheme
