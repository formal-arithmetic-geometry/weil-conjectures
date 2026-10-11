/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The affine nonvanishing locus of a section of an invertible module

Source: Stacks Project, Properties, Lemma 01PV (`properties-lemma-affine-cap-s-open`),
algebra argument in the proof (blueprint: lem-sc-affine-cap-section-open-algebra).
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace AlgebraicGeometry

/-- Source: Stacks Project, Lemma 01PV, algebra argument in the proof
(blueprint: lem-sc-affine-cap-section-open-algebra).
For an invertible module `N`, the spectrum of `Sym_R(N)/(ι(s)-1)` identifies with the open
locus of primes `p` where `s ∉ pN`. The base ring is lifted to the common universe
by `ULift`; primes are transported along its canonical ring equivalence.

Proof: (1) Choose a finite standard-open trivializing cover of `N`, with basis `eᵢ`, and
write `s = aᵢ eᵢ`. The locus on each chart is `D(aᵢ)`.
(2) By `lem-weil-pbc-localization-quotient-commute`,
`lem-weil-pbc-symmetric-algebra-base-change`, and
`lem-weil-pbc-symmetric-algebra-free-module-polynomial`, the quotient on that chart is
`R_fᵢ[t]/(aᵢ t - 1)`.
(3) By `lem-weil-pbc-fibre-product-affine-spectra`, this is the chartwise base change of
our spectrum map. By `lem-weil-pbc-localization-away-polynomial-quotient` and
`lem-weil-pbc-principal-localization-open-immersion`, it is the open immersion onto `D(aᵢ)`.
(4) The cover is fpqc by `def-weil-pbc-fpqc-covering`; hence
`lem-galois-fpqc-descend-open-immersion` makes the spectrum map an open immersion.
Its image is the asserted locus, as checked on every chart. By `def-weil-open-immersion`,
it identifies the affine source with that open subscheme. -/
theorem affine_cap_section_open_algebra (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (_hN : ∀ p : PrimeSpectrum R, Module.rankAtStalk N p = 1) (s : N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      ((algebraMap R (SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1})).comp
        (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom))) ∧
    Set.range (Spec.map (CommRingCat.ofHom
      ((algebraMap R (SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1})).comp
        (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom))) =
      {p : PrimeSpectrum (ULift.{v} R) |
        s ∉ (p.asIdeal.comap ULift.ringEquiv.symm.toRingHom) • (⊤ : Submodule R N)} := by
  sorry

end AlgebraicGeometry
