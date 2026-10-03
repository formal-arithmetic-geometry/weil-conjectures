/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Spectra of finitely generated algebras over a field

The spectrum of a finitely generated algebra over a field is a Noetherian space: descending chains
of closed subsets stabilize, and there are finitely many irreducible components.

## Main results

- `PrimeSpectrum.finite_irreducibleComponents_of_finiteType`

## Blueprint

- `lem-wf-affine-noetherian-components`: affine schemes of finite type are Noetherian with
  finitely many irreducible components.
-/

@[expose] public section

namespace PrimeSpectrum

/-- Blueprint `lem-wf-affine-noetherian-components`: the spectrum of a finitely generated algebra
`A` over a field `k` is a Noetherian space with finitely many irreducible components.

The ring `A` is Noetherian by the Hilbert basis theorem (`Algebra.FiniteType.isNoetherianRing`),
so `Spec A` is a Noetherian space (`PrimeSpectrum.instNoetherianSpace`), and a Noetherian space
has finitely many irreducible components. -/
theorem finite_irreducibleComponents_of_finiteType (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    TopologicalSpace.NoetherianSpace (PrimeSpectrum A) ∧
      (irreducibleComponents (PrimeSpectrum A)).Finite := by
  have := Algebra.FiniteType.isNoetherianRing k A
  exact ⟨inferInstance, TopologicalSpace.NoetherianSpace.finite_irreducibleComponents⟩

end PrimeSpectrum
