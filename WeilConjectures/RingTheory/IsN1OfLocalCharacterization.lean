/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.LocalNormalIntermediateAlgebra
import WeilConjectures.RingTheory.PatchLocalNormalIntermediateAlgebras
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# A local criterion for N-1 domains

A Noetherian domain `A` is N-1 if some nonzero principal localization is normal and every
localization at a maximal ideal is N-1.

## Implementation details

For each finite intermediate ring `A ⊆ B ⊆ A'` of the normalization, the image `Z_B` in
`Spec A` of the non-normal locus of `B` is closed. The N-1 property at each maximal ideal `m`
gives such a `B` with `m ∉ Z_B`; quasi-compactness gives finitely many `Bᵢ` with
`⋂ Z_{Bᵢ} = ∅`, and the ring they generate is a finite normal domain, hence equal to `A'`.

## References

* [Stacks, Tag 0333]
-/

@[expose] public section

universe u v

/-- A Noetherian domain is N-1 if some nonzero principal localization is normal and every
maximal localization is N-1. -/
theorem isN1_of_local_characterization (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hAway : ∃ f : A, f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hMaximal : ∀ (m : Ideal A) [m.IsMaximal],
      IsN1 (Localization.AtPrime m) (FractionRing (Localization.AtPrime m))) :
    IsN1 A K := by
  obtain ⟨B, hB, hfinite, hnormal⟩ :=
    exists_finite_locally_normal_intermediate_algebra A K hAway
      (fun m _ ↦ exists_local_normal_intermediate_algebra A K m (hMaximal m))
  have : IsIntegrallyClosed B :=
    IsIntegrallyClosed.of_localization_maximal (fun q _ _ ↦ hnormal q)
  have hclosure : integralClosure A K = B := by
    apply le_antisymm ?_ hB
    intro x hx
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed B›
      (((mem_integralClosure_iff A K).mp hx).tower_top (A := B))
    exact hy ▸ y.property
  change Module.Finite A (integralClosure A K)
  rw [hclosure]
  exact hfinite
