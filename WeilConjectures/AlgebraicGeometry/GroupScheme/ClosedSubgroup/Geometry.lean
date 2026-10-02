/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup

/-!
# The identity component of a closed subgroup of `GL_n`

Let `G = V(I)` be the closed subgroup scheme of `GL_n` over an algebraically closed field `k` cut
out by a Hopf ideal `I`, and let `G° = V(identityComponent I)` be its reduced identity component.
This file states the structure of `G°`: it is irreducible, normal in `G` (on `R`-points for every
`k`-algebra `R`) and of finite index in `G(k)`; `V(I)` has finitely many connected components,
and they are the cosets `g G°` of the identity component. Finally, a closed subgroup of a
connected group of the same dimension is the whole group.

## Main results

- `Matrix.GeneralLinearGroup.isPrime_identityComponent`: `G°` is irreducible.
- `Matrix.GeneralLinearGroup.normal_zeroLocus_identityComponent`: `G°` is normal in `G`.
- `Matrix.GeneralLinearGroup.finiteIndex_zeroLocus_identityComponent`: `G°(k)` has finite index
  in `G(k)`.
- `Matrix.GeneralLinearGroup.toPrimeSpectrum_mem_connectedComponentIn_iff`: the connected
  components of `G` are the cosets of `G°`.
- `Matrix.GeneralLinearGroup.eq_of_ringKrullDim_eq`: a closed subgroup of a connected group of
  the same dimension is the whole group.

## Blueprint

- `sk-p-geometry`: structure of the identity component and the dimension criterion.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k] [IsAlgClosed k]
  (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The identity component `G°` of a closed subgroup `G = V(I)` of `GL_n` is irreducible: its
ideal is prime. (blueprint: `sk-p-geometry`) -/
theorem isPrime_identityComponent : (identityComponent I).IsPrime := by
  sorry

/-- The identity component `G°` of a closed subgroup `G = V(I)` of `GL_n` is a normal subgroup
scheme: `G°(R)` is normal in `G(R)` for every `k`-algebra `R`. (blueprint: `sk-p-geometry`) -/
instance normal_zeroLocus_identityComponent (R : Type*) [CommRing R] [Algebra k R] :
    ((zeroLocus (identityComponent I) R).subgroupOf (zeroLocus I R)).Normal := by
  sorry

/-- The identity component `G°` of a closed subgroup `G = V(I)` of `GL_n` has finite index in `G`.
(blueprint: `sk-p-geometry`) -/
theorem finiteIndex_zeroLocus_identityComponent :
    ((zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)).FiniteIndex := by
  sorry

/-- A closed subgroup `G = V(I)` of `GL_n` has finitely many connected components.
(blueprint: `sk-p-geometry`) -/
theorem finite_connectedComponents_zeroLocus :
    Finite (_root_.ConnectedComponents
      (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))) := by
  sorry

/-- The connected components of a closed subgroup `G = V(I)` of `GL_n` are the cosets of the
identity component: a point `x` of `G` lies in the connected component of `g ∈ G` if and only if
`g⁻¹ * x ∈ G°`. (blueprint: `sk-p-geometry`) -/
theorem toPrimeSpectrum_mem_connectedComponentIn_iff {g x : GL n k} (hg : g ∈ zeroLocus I k)
    (hx : x ∈ zeroLocus I k) :
    toPrimeSpectrum x ∈ connectedComponentIn
        (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum g) ↔
      g⁻¹ * x ∈ zeroLocus (identityComponent I) k := by
  sorry

/-- A reduced closed subgroup `V(J)` of a connected reduced closed subgroup `V(I)` of `GL_n` of
the same dimension is all of `V(I)`. (blueprint: `sk-p-geometry`) -/
theorem eq_of_ringKrullDim_eq {J : Ideal (CoordinateRing n k)} (hIJ : I ≤ J) [I.IsPrime]
    [J.IsHopfIdeal k] (hJ : J.IsRadical)
    (h : ringKrullDim (CoordinateRing n k ⧸ J) = ringKrullDim (CoordinateRing n k ⧸ I)) :
    J = I := by
  sorry

end Matrix.GeneralLinearGroup
