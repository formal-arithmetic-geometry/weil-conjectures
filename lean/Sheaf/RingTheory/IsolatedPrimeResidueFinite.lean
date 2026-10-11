/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Isolated primes in finite type algebras have finite residue fields

Source: Stacks Project, Algebra, Lemma 00PJ (algebra-lemma-isolated-point,
line 30106), implication (1) => (6)
(blueprint: lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite).
-/

universe u v

/-- An isolated prime of a finite type algebra over a field is maximal and has finite residue field.

Source: Stacks Project, Algebra, Lemma 00PJ (algebra-lemma-isolated-point,
line 30106), implication (1) => (6), using Lemmas 00G1 and 00G3 and Theorem 00FV
(blueprint: lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite).

Proof:
1. Write the complement of `{p}` as `V(I)` and choose `f ∈ I` outside `p`.
   By `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`, the finite type
   algebra is Jacobson, so some maximal ideal `m` contains `p` but not `f`.
   Then `m` lies outside `V(I)`, hence in `{p}`; therefore `p = m` is maximal.
   This is the closed-point density argument of Stacks 00G3 used in 00PJ.
2. By `def-weil-pbc-localization-at-prime`, the residue field is `B_p / p B_p`.
   For `s ∉ p`, its class in the field `B / p` has an inverse represented by `t ∈ B`.
   Thus `st - 1 ∈ p`, so `b/s` and `bt/1` have the same residue class. Consequently
   `B → κ(p)` is surjective. Images of a finite set of algebra generators of `B`
   generate `κ(p)` over `k` (`def-weil-pbc-finite-type-algebra`), so this field is a
   finite type `k`-algebra with the composite structure `k → B → κ(p)`.
3. Apply `lem-weil-pbc-zariski-lemma` (Stacks 00FV) to this finite type field algebra.
   Its dimension over `k` is finite, giving the finite field extension of
   `def-pc-field-extension` with the specified composite structure.
-/
theorem isolatedPrime_finiteType_residueField
    {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (p : PrimeSpectrum B)
    (hp : IsOpen ({p} : Set (PrimeSpectrum B))) :
    p.asIdeal.IsMaximal ∧ Module.Finite k p.asIdeal.ResidueField := by
  sorry
