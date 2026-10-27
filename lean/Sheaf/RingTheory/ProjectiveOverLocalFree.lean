/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Projection
import Sheaf.LinearAlgebra.CountablyGeneratedFreenessCriterion
import Sheaf.RingTheory.ProjectiveCountableDecomposition
import Sheaf.SecTraceFormula.ProjectiveElementFreeSummand

/-!
# Projective modules over local rings are free in arbitrary rank

Source: Stacks Project, Algebra, Tag 0593, theorem-projective-free-over-local-ring.
(blueprint: lem-trf-projective-over-local-free)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- Every projective module over a commutative local ring is free, without a finite-generation
hypothesis. Source: Stacks Project, Algebra, Tag 0593.
(blueprint: lem-trf-projective-over-local-free)

Proof:
1. By `lem-trf-projective-countable-decomposition` (Tag 058Y), express `P` as a direct sum
   of countably generated projective modules `Pᵢ`, with an arbitrary summand index set.
2. For any decomposition `Pᵢ = N ⊕ F` with `F` finite free, `N` is projective: compose
   the split inclusion and projection for `N` in `Pᵢ` with split maps exhibiting `Pᵢ`
   as a direct summand of a free module. The composite retraction is the identity on `N`.
   By `lem-trf-projective-element-free-summand` (Tag 0592), each element of `N` lies in
   a free direct summand of `N`. This verifies the complementary-summand hypothesis.
3. Apply `lem-trf-countably-generated-freeness-criterion` (Tag 0591) to each `Pᵢ` using
   countable generation from step 1 and the complementary-summand property from step 2.
   Thus each `Pᵢ` has a basis.
4. The disjoint union of these bases is a basis of the direct sum: every vector has
   finitely many nonzero coordinates, each with a finite unique basis expansion.
   Comparing coordinates proves uniqueness. Transport this basis to `P` along the
   isomorphism of step 1. An empty summand index set gives the empty basis of zero.

`Module.Free R P` means existence of a basis indexed by a possibly empty or infinite type;
its coordinate isomorphism is `P ≃ₗ[R] (B →₀ R)`, whose inverse is the stated direct-sum
isomorphism. -/
theorem free_of_projective_of_isLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P] :
    Module.Free R P := by
  obtain ⟨I, Q, _, _, hprojective, hcountable, ⟨e⟩⟩ :=
    exists_directSum_countablyGenerated_projective R P
  have : ∀ i, Module.Free R (Q i) := by
    intro i
    have : Module.Projective R (Q i) := hprojective i
    apply free_of_countable_generators_of_free_summands (hcountable i)
    intro N F hNF _ x
    have : Module.Projective R N :=
      Projective.of_split N.subtype (N.projectionOnto F hNF)
        (Submodule.projectionOnto_comp_subtype hNF)
    exact projective_element_mem_free_summand x
  exact Module.Free.of_equiv e

end Module
