/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-!
# Weakly étale covers of strictly henselian local rings split

A strictly henselian local ring `R` is w-contractible: its spectrum is w-local with a single
closed point, its localization at the maximal ideal is `R` itself, and the space of connected
components of `Spec R` is a point. Hence every faithfully flat ind-étale `R`-algebra has a
retraction, and so does every faithfully flat weakly étale `R`-algebra, which becomes ind-étale
over `R` after a faithfully flat ind-étale extension (Stacks 097Z).

The power series ring `k⟦X⟧` over a separably closed field is strictly henselian, being
complete for its maximal ideal `(X)`.

## Main statements

- `IsStrictlyHenselianLocalRing.isWContractibleRing`
- `IsStrictlyHenselianLocalRing.exists_retraction_of_weaklyEtale`
- `PowerSeries.isStrictlyHenselianLocalRing`
-/

@[expose] public section

universe u

/-- A strictly henselian local ring is w-contractible. -/
theorem IsStrictlyHenselianLocalRing.isWContractibleRing (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R] : IsWContractibleRing R := by
  sorry

/-- A faithfully flat weakly étale algebra over a strictly henselian local ring has a
retraction. -/
theorem IsStrictlyHenselianLocalRing.exists_retraction_of_weaklyEtale {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [IsStrictlyHenselianLocalRing R]
    [Algebra.WeaklyEtale R S] [Module.FaithfullyFlat R S] :
    ∃ f : S →+* R, f.comp (algebraMap R S) = RingHom.id R := by
  sorry

/-- The power series ring over a separably closed field is a strictly henselian local ring. -/
instance PowerSeries.isStrictlyHenselianLocalRing (k : Type u) [Field k] [IsSepClosed k] :
    IsStrictlyHenselianLocalRing (PowerSeries k) := by
  sorry
