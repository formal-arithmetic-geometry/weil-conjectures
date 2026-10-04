/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-!
# Strictly henselian local rings via sections of étale algebras

A local ring `R` such that every étale `R`-algebra `B` has, through every prime of `B` over the
closed point, an `R`-algebra section `B →ₐ[R] R`, is henselian with separably closed residue
field. Both statements are tested on standard étale algebras `R[X][1/f']/(f)` for a monic `f`:
a section sends `X` to a root of `f`.

## Main results

- `HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq`: such a local ring is henselian.
- `IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq`: such a local
  ring has separably closed residue field.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A local ring `R` is henselian if every prime `q` lying over the maximal ideal of an étale
`R`-algebra `B` is the preimage of the maximal ideal under an `R`-algebra map `B →ₐ[R] R`. -/
theorem HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    HenselianLocalRing R :=
  sorry

/-- A local ring `R` has separably closed residue field if every prime `q` lying over the
maximal ideal of an étale `R`-algebra `B` is the preimage of the maximal ideal under an
`R`-algebra map `B →ₐ[R] R`. -/
theorem IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    IsSepClosed (ResidueField R) :=
  sorry
