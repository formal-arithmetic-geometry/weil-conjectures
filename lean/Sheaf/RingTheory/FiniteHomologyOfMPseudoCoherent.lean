/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker K1
-/
module

public import Sheaf.RingTheory.MPseudoCoherent

/-!
# Finite top cohomology of an m-pseudo-coherent complex

Source: Stacks Project, More on Algebra, Lemma 15.66.3 (1), Tag 064S
(blueprint: lem-sc-finite-cohomology).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An `m`-pseudo-coherent complex with zero cohomology above `m` has finite type
cohomology in degree `m`. Rings are commutative with identity, including the zero ring,
as in the Stacks conventions (Tag 00AQ).
Source: Stacks Project, More on Algebra, Tag 064S (1)
(blueprint: lem-sc-finite-cohomology).

Proof:
1. Choose the bounded finite-free witness `E` mapping to `Q.obj K` supplied by
   `IsMPseudoCoherent`. Finite free modules are finite projective. The isomorphisms on
   cohomology above `m` and the vanishing hypothesis give zero cohomology of `E` above `m`.
2. If the top nonzero term of `E` is in degree `b > m`, vanishing of its top cohomology
   makes the differential to `E.X b` surjective. Projectivity splits it, so the
   preceding term is a direct sum of its kernel and `E.X b`. Cancel the resulting
   contractible two-term summand. The remaining terms are finite projective (they need
   not be free). Repeat until all terms above `m` vanish. If all terms vanish, or the
   top degree is below `m`, degree-`m` cohomology is zero. Otherwise it is a quotient
   of the finite module in degree `m`, hence is finite.
3. The witness map surjects on degree-`m` cohomology of `K`. A quotient of a finite
   module is finite. All three steps are the elementary steps of Tag 064S (1). -/
theorem finite_homology_of_isMPseudoCoherent {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : IsMPseudoCoherent m (Q.obj K))
    (hvan : ∀ i : ℤ, m < i →
      IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj K))) :
    Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj (Q.obj K)) := by
  sorry

end DerivedCategory
