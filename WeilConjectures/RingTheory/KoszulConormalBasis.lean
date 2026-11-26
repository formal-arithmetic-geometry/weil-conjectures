/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.KoszulConormalVectorBasisData

/-!
# Conormal basis of a Koszul-regular sequence

The classes of a Koszul-regular sequence `f₁, …, f_r` generating `I` form a basis of the
conormal module `I/I²` over `A/I`.

## Implementation details

Vanishing of `H_1` makes `∧² A^r → A^r → I → 0` exact. Tensoring with `A/I` kills the first
map, since every coefficient of the second Koszul differential lies in `I`, so
`(A/I)^r ≃ I/I²`.

## References

* [Stacks, Tags 062I, 0CEM]
-/

@[expose] public section

universe u

namespace ExteriorAlgebra

/-- The generating conormal classes of a Koszul-regular sequence form a basis. -/
theorem exists_koszul_conormal_basis
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ b : Module.Basis (Fin r) (A ⧸ I) I.Cotangent,
      ∀ i, b i = koszulConormalVector A I r f hf (Finsupp.single i 1) := by
  obtain ⟨hli, hsp⟩ := koszulConormalVector_linearIndependent_and_span A I r f hreg hf
  let b := Module.Basis.mk hli hsp
  refine ⟨b, ?_⟩
  intro i
  exact Module.Basis.mk_apply hli hsp i

end ExteriorAlgebra
