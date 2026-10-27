module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generic reducedness of flat coefficient models

Source: Stacks Project, algebra.tex, Tags 00HS and 030V, combined generic-local consequence
(blueprint: lem-per-flat-model-generic-reducedness).
-/

@[expose] public section

universe uR uD uB uk

open scoped TensorProduct

namespace Algebra

/-- Generic reducedness of a flat finite type coefficient model persists under an injective
base change between finitely generated rational domains, if it holds over a containing field.
Generic reducedness is expressed at each minimal prime, allowing the zero algebra.

Source: Stacks Project, algebra.tex, Tags 00HS and 030V, combined generic-local consequence
(blueprint: lem-per-flat-model-generic-reducedness).

Proof: Put K = Frac(R) and L = Frac(D). The injections induce embeddings K → k and K → L.
The tensor pushout universal property (lem-weil-pbc-algebra-tensor-pushout-universal-property)
identifies k ⊗[K] (K ⊗[R] B) with k ⊗[R] B, and likewise over L, by multiplying the first
two factors; their inverses insert 1 in the middle factor. The field-extension equivalence
(lem-per-field-extension-generic-reducedness), first for K → k and then for K → L, shows
that C = L ⊗[R] B is generically reduced. Flat base change
(lem-weil-pbc-flat-module-base-change) makes T = D ⊗[R] B flat over D. For a minimal prime
q of T, flat going down (lem-sc-flat-going-down) lifts the zero prime of D to a prime below
q; minimality forces equality. Thus q contracts to zero. Localizing at the nonzero elements
of D identifies C with that localization of T (lem-weil-pbc-localization-tensor-over-base).
The localization spectrum correspondence (lem-weil-pbc-localization-spectrum-embedding)
identifies q with a minimal prime q' of C. Two-stage localization gives T_q ≃ C_q': the
map sends (t/s)/(u/v) to tv/(su), and its inverse sends t/u to (t/1)/(u/1).
Consequently T_q is reduced. This holds at every minimal prime; the zero ring has none. -/
theorem genericallyReduced_tensorProduct_of_flat
    (R : Type uR) (D : Type uD) (B : Type uB) (k : Type uk)
    [CommRing R] [IsDomain R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    [CommRing D] [IsDomain D] [Algebra ℚ D] [Algebra.FiniteType ℚ D]
    [Algebra R D] [IsScalarTower ℚ R D]
    [CommRing B] [Algebra R B] [Module.Flat R B]
    [Field k] [CharZero k] [Algebra ℚ k] [Algebra R k] [IsScalarTower ℚ R k]
    (hRD : Function.Injective (algebraMap R D))
    (hRB : (algebraMap R B).FiniteType)
    (hRk : Function.Injective (algebraMap R k))
    (hk : ∀ p : PrimeSpectrum (k ⊗[R] B),
      p.asIdeal ∈ minimalPrimes (k ⊗[R] B) → IsReduced (Localization.AtPrime p.asIdeal)) :
    ∀ p : PrimeSpectrum (D ⊗[R] B),
      p.asIdeal ∈ minimalPrimes (D ⊗[R] B) → IsReduced (Localization.AtPrime p.asIdeal) := by
  sorry

end Algebra
