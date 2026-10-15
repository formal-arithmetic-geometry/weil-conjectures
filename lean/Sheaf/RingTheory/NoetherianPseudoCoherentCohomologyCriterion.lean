/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.RingTheory.FiniteFreeResolution

/-!
# The Noetherian cohomology criterion for pseudo-coherence

Source: Stacks Project, More on Algebra, Tag 066E,
lemma-Noetherian-pseudo-coherent, clause (2)
(blueprint: lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Over a commutative Noetherian ring, pseudo-coherence is equivalent to bounded-above,
finite cohomology. No lower cohomology bound or Tor-dimension assumption is imposed.

Source: Stacks Project, More on Algebra, Tag 066E,
lemma-Noetherian-pseudo-coherent, clause (2)
(blueprint: lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion).

Proof plan:
1. Unpack `def-pc-ring-pseudo-coherent-complex`: choose a bounded-above finite-free
   complex `E` and an isomorphism from `Q.obj E` to `K`. Above its term bound, its
   cohomology, and hence that of `K`, vanishes.
2. Each cycle module is a submodule of a finite free module. By
   `lem-weil-pbc-noetherian-submodule-finite`, it is finitely generated. Project its
   generators to the quotient by the boundaries and then transport them through the
   cohomology isomorphism to obtain finite generation of every cohomology module of `K`.
3. Conversely, resolve each finite cohomology module by finite free modules using
   `lem-weil-pbc-finite-free-resolution-noetherian`. Put resolution term `j` in degree
   `-j`, with zero positive terms. The augmentation is a cochain map to the module in
   degree zero: exactness gives zero negative cohomology, the required module in degree
   zero, and zero positive cohomology. It is therefore a quasi-isomorphism, exhibiting
   the degree-zero cohomology module as pseudo-coherent.
4. Apply `lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent` with the given
   upper bound and the pseudo-coherent cohomology modules from step 3. This proves that
   `K` is pseudo-coherent (the pseudo-coherent clause of Tag 066B used in Tag 066E). -/
theorem isPseudoCoherent_iff_boundedAbove_finite_homology
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    IsPseudoCoherent K ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat R) i).obj K)) ∧
        ∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat R) i).obj K) := by
  sorry

end DerivedCategory
