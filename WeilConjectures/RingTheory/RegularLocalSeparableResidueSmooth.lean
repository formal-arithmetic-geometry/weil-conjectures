/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import WeilConjectures.RingTheory.SmoothAtPrimeOfDifferentialsDimensionBound
import WeilConjectures.RingTheory.RegularLocalFibreFinrank

/-!
# Regularity with separable residue field characterizes smoothness over a field

For a finite type algebra over a field and a prime with separable residue field, smoothness at
the prime is equivalent to regularity of the local ring.

## Implementation details

The local ring is Noetherian with finitely generated separable residue field. The
Jacobi–Zariski sequence is short exact on cotangent spaces by separability, and its dimension
count (regular-local cotangent criterion, transcendence degree of separably generated fields,
localization of differentials) compares `dim_K (K ⊗ Ω[S/k])` with the dimension of `Spec S` at
`q`, with equality exactly when the local ring is regular. The dimension criteria for smoothness
give both implications.

## References

* [Stacks, Tag 00TV]
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite type algebra over a field, smoothness at a prime is equivalent to
regularity of the local ring when the residue field is separable over the base. -/
theorem regularLocal_iff_smoothAtPrime
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField) :
    Algebra.IsSmoothAtPrime k ⟨q, inferInstance⟩ ↔
      IsRegularLocalRing (Localization.AtPrime q) := by
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  rw [regularLocal_iff_fibre_finrank_eq_dimension k S q hsep]
  constructor
  · intro hsm
    exact (finiteDimensional_and_finrank_kaehlerDifferential_eq_of_isSmoothAtPrime q' hsm).2
  · intro heq
    exact isSmoothAtPrime_of_finrank_kaehlerDifferential_le q' heq.le

end Algebra
