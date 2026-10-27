module

public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.GradedAlgebra.Radical
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dimension at the vertex of a standard graded algebra

Source: Stacks Project, Algebra, Tag 00P6, lemma-dimension-graded, assertion (1)
and the first equality paragraph of its proof
(blueprint: lem-sfb-standard-graded-vertex-dimension).
-/

@[expose] public section

universe u v

namespace GradedAlgebra.IsStandard

/-- The irrelevant ideal of a standard graded algebra with degree-zero field is maximal,
and localization there preserves Krull dimension.

Source: Stacks Project, Algebra, Tag 00P6, lemma-dimension-graded, assertion (1)
and the first equality paragraph of its proof
(blueprint: lem-sfb-standard-graded-vertex-dimension).

The nontriviality assumption expresses the injectivity of the scalar field in `S`:
`grade_zero_eq_one` identifies degree zero with its image, hence with the field.

Proof:
1. Projection to degree zero is a surjective ring map to the scalar field with kernel
   the irrelevant ideal. Its field quotient proves maximality. The finite degree-one
   generators supplied by def-pc-standard-graded-algebra also make `S` finite type.
2. By lem-sfb-prime-homogeneous-core, the homogeneous core of a minimal prime is prime
   and contained in it, hence equals it. Its degree-zero elements lie in the scalar
   field and must vanish, since every nonzero scalar is a unit. Thus every minimal
   prime is contained in the irrelevant ideal.
3. Apply lem-weil-pbc-dimension-at-point-components at the irrelevant maximal ideal.
   Local dimension is the attained maximum of the dimensions of all minimal-prime
   quotients, since all minimal primes lie below this ideal. The minimum formula over
   maximal ideals above it has only this maximal ideal, so its localization has the
   same dimension, say `n`.
4. At any other point the same component formula involves a subfamily, hence gives
   local dimension at most `n`. By lem-weil-pbc-dimension-supremum-local-dimensions,
   global dimension is at most `n`, and the vertex attains it. Finally
   lem-weil-pbc-spec-topological-krull-dimension-ring identifies this with ring dimension.
-/
theorem exists_isMaximal_irrelevant_ringKrullDim_eq
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Nontrivial S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] [IsStandard 𝒜] :
    ∃ (_ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal),
      ringKrullDim (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) =
        ringKrullDim S := by
  sorry

end GradedAlgebra.IsStandard
