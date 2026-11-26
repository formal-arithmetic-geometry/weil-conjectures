/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.FlatAlgebraPowerBasis

/-!
# Fixed bases for strict henselization quotients

For a strict henselization `C` of a Noetherian local ring `A` with maximal ideal `n`, lifts to
`C` of a basis of `C ⧸ nC` over `A ⧸ n` give bases of `C ⧸ (nC)^r` over `A ⧸ n^r` for every
`r ≥ 1`.

## Implementation details

Since `C` is faithfully flat over `A`, it is flat, and the nilpotent local basis criterion
over `A ⧸ n^r` applies to the fixed lifts. There is no need to identify `C ⧸ nC` with `K`.

## References

* [Stacks, Tag 07QM], part (4)
* [Stacks, Tag 06LJ], proof of (c)
* [Stacks, Tag 051F]
* [Stacks, Tag 00HI]
-/

@[expose] public section

universe u

namespace Algebra

/-- Fixed residue-field lifts are bases of every positive-power quotient. -/
theorem strictHenselization_quotient_bases
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    ∃ (X : Type u) (x : X → C)
      (e : ∀ (r : ℕ), 1 ≤ r →
        (X →₀ A ⧸ (IsLocalRing.maximalIdeal A) ^ r) ≃ₗ[A]
          C ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r),
      (∀ (r : ℕ) (hr : 1 ≤ r) (i : X),
        e r hr (Finsupp.single i 1) =
          Ideal.Quotient.mk (((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r)
            (x i)) := by
  classical
  obtain ⟨p, hp, a, hsep, ι, ⟨hc⟩, hι⟩ := hC.triples_presentation A K C
  let := a
  have := hsep
  have hflat := AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat
    (CommRingCat.of A) p hp K _ hc (CommRingCat.ofHom (algebraMap A C)) hι
  have : Module.Flat A C := RingHom.flat_algebraMap_iff.mp hflat.flat
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let b := Module.Free.chooseBasis (A ⧸ IsLocalRing.maximalIdeal A)
    (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C))
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (b i)
  have hb := fun r hr ↦ flatAlgebra_power_basis A C b x hx r hr
  choose B hB using hb
  let e := fun r hr ↦ ((B r hr).repr.symm.restrictScalars A).trans
    (Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (algebraMap A C) (IsLocalRing.maximalIdeal A) r)).toLinearEquiv
  refine ⟨_, x, e, ?_⟩
  intro r hr i
  change Ideal.quotientEquivAlgOfEq A
    (Ideal.map_pow (algebraMap A C) (IsLocalRing.maximalIdeal A) r)
    ((B r hr).repr.symm (Finsupp.single i 1)) = _
  rw [Module.Basis.repr_symm_single_one, hB r hr i]
  rfl

end Algebra
