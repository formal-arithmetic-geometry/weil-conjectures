/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideals covering the spectrum of a reduced ring

Source: Stacks Project, Varieties Remark 09NW (varieties-remark-conductor)
(blueprint: lem-sc-reduced-ideals-zero-intersection).
-/

@[expose] public section

universe u

namespace Ideal

/-- Ideals whose vanishing loci cover the spectrum of a reduced ring have zero intersection.
Reduction modulo `J` identifies `I` with its image ideal `IB` in `B = A ⧸ J`, as an
`A`-module. The equation on the equivalence specifies the canonical map, rather than an
unspecified isomorphism. Its usual quotient description is `I / (I ∩ J)`.

Source: Stacks Project, Varieties Remark 09NW (varieties-remark-conductor)
(blueprint: lem-sc-reduced-ideals-zero-intersection).

Proof:
1. The zero locus of `I ⊓ J` is the union of the two zero loci, hence the whole spectrum
(lem-weil-pbc-zero-locus-ideal-intersection).
2. Every element of `I ⊓ J` therefore belongs to every prime ideal and is nilpotent
(lem-weil-pbc-zero-locus-eq-iff-radical-eq). Reducedness makes it zero.
3. The restriction of the quotient map to `I` surjects onto `IB = (I + J)/J` and has kernel
`I ∩ J = 0`. It is consequently an `A`-linear isomorphism, and the first isomorphism theorem
identifies `IB` with `I/(I ∩ J)`. -/
theorem reduced_ideals_zero_intersection
    {A : Type u} [CommRing A] [IsReduced A] (I J : Ideal A)
    (hcover : PrimeSpectrum.zeroLocus (I : Set A) ∪ PrimeSpectrum.zeroLocus (J : Set A) =
      (Set.univ : Set (AlgebraicGeometry.Spec (CommRingCat.of A)))) :
    I ⊓ J = ⊥ ∧
      ∃ e : I ≃ₗ[A] (Ideal.map (Ideal.Quotient.mk J) I),
        ∀ x : I, (e x : A ⧸ J) = Ideal.Quotient.mk J (x : A) := by
  sorry

end Ideal
