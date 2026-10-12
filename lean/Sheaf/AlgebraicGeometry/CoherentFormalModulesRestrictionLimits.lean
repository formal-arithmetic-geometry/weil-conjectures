/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
import Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel

/-! # Restriction preserves finite limits and colimits of formal modules

Source: Stacks Project, Lemma 087X (2), final sentence of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The explicit termwise restriction functor preserves finite limits and colimits.
Source: Stacks Project, Lemma 087X, construction (a)--(d) and the last sentence
of its proof; step 2 of lem-weil-pbc-coherent-formal-modules-local-exactness.
(blueprint: lem-weil-pbc-coherent-formal-modules-restriction-limits)

Proof: Cokernels are termwise cokernels by coherentFormalModule_abelian, and
module restriction, a left adjoint, preserves them. For kernels use the stabilized
kernel construction coherentFormalModule_kernel. Sectionwise kernels, locally
computed image sheaves and ideal products commute with restriction. Cokernel
preservation gives the same assertion for the quotient levels. A stabilization
bound on X is still valid on U. If a different bound is used on U, a common larger
bound identifies the eventual systems and their maps, so restriction carries the
kernel fork to a limiting fork. Finite direct sums restrict termwise: addition and
zero maps restrict, and the biproduct identities remain valid. Thus restriction
preserves finite products and kernels, and finite coproducts and cokernels. In
abelian categories these give preservation of all finite limits and colimits. -/
theorem coherentFormalModules_restriction_limits {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    [IsNoetherian U.toScheme] :
    PreservesFiniteLimits (coherentFormalModulesRestriction I U) ∧
      PreservesFiniteColimits (coherentFormalModulesRestriction I U) := by sorry

end AlgebraicGeometry
