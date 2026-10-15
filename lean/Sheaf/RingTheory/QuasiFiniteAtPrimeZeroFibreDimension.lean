/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete

/-!
# Quasi-finiteness at a prime and zero dimension of the fibre at that point

Source: Stacks Project, Morphisms, Tag 0397, second proof, and Properties, Tag 0H7C
(blueprint: lem-weil-pbc-ring-quasifinite-zero-fibre-dimension).
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite-type ring map, quasi-finiteness at a prime is equivalent to dimension zero
at the corresponding point of the fibre spectrum. The fibre is written `κ(p) ⊗[R] T`,
canonically isomorphic to `T ⊗[R] κ(p)` by tensor commutation. Its spectrum is the underlying
space of `Spec` of the fibre ring, and `preimageHomeomorphFiber` supplies the unique fibre
prime contracting to `q`.

Source: Stacks Project, Morphisms, Tag 0397, second proof; Properties, Tag 0H7C
(blueprint: lem-weil-pbc-ring-quasifinite-zero-fibre-dimension).

Proof:
1. Finite algebra generators of `T` over `R` give generators of the fibre over `κ(p)`:
   every tensor is a sum of pure tensors, and polynomials in the generators base change.
2. By `lem-wf-affine-noetherian-components`, the fibre ring is Noetherian and its spectrum
   has descending chain condition on closed subsets.
3. Its single affine chart gives local Noetherianity (`pqf-def-locnoeth`). The descending
   chain condition gives quasi-compactness (`def-weil-pbc-quasi-compact-scheme`), so this
   affine fibre is a Noetherian scheme.
4. If quasi-finiteness holds, the singleton of the fibre prime is open by
   `def-weil-pbc-ring-map-quasi-finite-at-prime`. Its Krull dimension is zero, while every
   neighbourhood is nonempty and has nonnegative dimension, so the minimum is zero
   (`def-kun-topological-dimension-at-point`, `def-kun-topological-krull-dimension`).
5. Conversely, a zero minimum is attained by an open neighbourhood of dimension zero.
   It is Noetherian by `lem-weil-pbc-noetherian-open-subscheme-noetherian`, hence discrete
   by `lem-sc-zero-dim-noetherian-finite-discrete`. The singleton is open in this open
   neighbourhood, hence in the fibre spectrum.
6. This openness is exactly the recorded definition of quasi-finiteness at `q`, proving
   the converse and the equivalence. -/
theorem isQuasiFiniteAtPrime_iff_topologicalKrullDimAt_eq_zero
    (R : Type u) (T : Type v) [CommRing R] [CommRing T]
    [Algebra R T] [Algebra.FiniteType R T] (q : PrimeSpectrum T) :
    IsQuasiFiniteAtPrime R T q ↔
      topologicalKrullDimAt
        (PrimeSpectrum.preimageHomeomorphFiber R T (q.comap (algebraMap R T))
          ⟨q, rfl⟩) = 0 := by
  sorry

end Algebra
