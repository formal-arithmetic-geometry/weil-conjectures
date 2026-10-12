/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Ring maps quasi-finite at a prime

A ring map `R → S` is quasi-finite at a prime `𝔮` of `S` if the prime of the fibre ring
`κ(𝔭) ⊗[R] S` (`𝔭 = 𝔮 ∩ R`) corresponding to `𝔮` is an isolated point of its spectrum
(Stacks, Algebra, Definition 00PJ).

Mathlib's `Algebra.QuasiFiniteAt` is defined differently (through the localization `S_𝔮`); the two
agree for maps of finite type.
-/

@[expose] public section

namespace Algebra

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The point of `Spec(κ(𝔭) ⊗[R] S)` corresponding to a prime `𝔮` of `S` lying over `𝔭`. -/
noncomputable def fiberPoint (q : PrimeSpectrum S) :
    PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber S) :=
  PrimeSpectrum.preimageEquivFiber R S _ ⟨q, rfl⟩

/-- `R → S` is *quasi-finite at the prime `𝔮`* if the point of `Spec(κ(𝔭) ⊗[R] S)` corresponding
to `𝔮` is isolated, i.e. `{𝔮̄}` is open. (Stacks writes the fibre ring as `S ⊗_R κ(𝔭)`; it is
canonically isomorphic to `κ(𝔭) ⊗[R] S`.)
(blueprint: `def-weil-pbc-ring-map-quasi-finite-at-prime`) -/
def IsQuasiFiniteAtPrime (q : Ideal S) [q.IsPrime] : Prop :=
  IsOpen ({fiberPoint R ⟨q, ‹_›⟩} : Set (PrimeSpectrum _))

end Algebra
