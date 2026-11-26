/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.FlatPointNoetherianModel
import WeilConjectures.RingTheory.FlatLocalizedModuleBaseChange
import WeilConjectures.Mathlib.RingTheory.Flat.Localization

/-!
# Openness of the flat locus of a finitely presented module

For a finitely presented algebra `S` over `R` and a finitely presented `S`-module `M`, the set of
primes `q` of `S` with `M_q` flat over `R` is open.

## Implementation details

Write `(R, S, M)` as a directed limit of finite-type models over `ℤ` (Tag 00R1). For `q` in the
flat locus, eventual flatness of colimits (Tag 00R6) gives a Noetherian model flat at the
contracted prime; the Noetherian flat-locus neighborhood there pulls back to a basic open
`D(g)` around `q` contained in the flat locus. The scalar tower identifies the `R`-action with
restriction along `algebraMap R S`.

## References

* [Stacks, Tag 00RC]
* [Stacks, Tag 00R1]
* [Stacks, Tag 00R6]
-/

@[expose] public section

universe u v w

namespace Module

/-- For a finitely presented algebra `S` over `R` and a finitely presented `S`-module `M`, the
primes `q` where `M_q` is flat over `R` form an open subset of the Zariski spectrum of `S`. -/
theorem isOpen_setOf_flat_localizedModule {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q (hq : Module.Flat R _)
  obtain ⟨A, B, N, hA, hB, hAB, hAR, hBS, hAS, hABS, hARS,
    hN, hAN, hBN, hABN, hnoeth, hft, hfin, hpush, ⟨e⟩, hflat⟩ :=
    exists_noetherian_model_flat_at_prime q hq
  let p : Ideal B := q.asIdeal.comap (algebraMap B S)
  have hp : p.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨g, hg, hneighborhood⟩ :=
    Flat.exists_notMem_forall_flat_localizedModule (R := A) (M := N) p hflat
  refine ⟨PrimeSpectrum.basicOpen (algebraMap B S g), ?_,
    PrimeSpectrum.isOpen_basicOpen, hg⟩
  intro r hr
  exact Flat.localizedModule_of_isPushout e r
    (hneighborhood (r.asIdeal.comap (algebraMap B S)) hr)

end Module
