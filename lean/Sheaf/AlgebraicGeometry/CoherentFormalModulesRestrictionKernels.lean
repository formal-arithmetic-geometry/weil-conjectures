/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel

/-! # Open restriction preserves formal kernels

Source: Stacks Project, Lemma 087X, claims (a)--(d) and final sentence.
(blueprint: lem-weil-pbc-coherent-formal-modules-restriction-kernels).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restriction preserves kernels in the formal category, without assuming abelianness.
Source: Stacks Project, Lemma 087X, claims (a)--(d) and final sentence.
(blueprint: lem-weil-pbc-coherent-formal-modules-restriction-kernels).

Proof: Use the stabilized kernel supplied by coherentFormalModule_kernel. Open
restriction of module sheaves preserves their kernels, images and cokernels.
It also commutes with ideal powers and ideal products, checked on affine sections.
Consequently the restricted stabilized-image system has the same stabilization
bound, and its quotient levels are the restrictions of the original quotient
levels. The transition and inclusion equations restrict with them. These are
the stabilized-kernel construction on the open subscheme. Its universal property
follows by the same factorization argument: a map killed by the restricted arrow
factors through the stabilized images using the epi transitions of its source,
then through their ideal quotients. Artin--Rees makes the higher-level kernels of
the inclusion transition to zero, giving uniqueness. Hence the restricted fork
is limiting. Any limiting fork on X is uniquely isomorphic to this constructed
fork; restrict that isomorphism to prove preservation of every limiting fork.
No assertion that the formal kernel is the termwise kernel is used. -/
theorem coherentFormalModules_restriction_preservesKernel {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    [IsNoetherian U.toScheme] {F G : CoherentFormalModule X I} (α : F ⟶ G) :
    PreservesLimit (parallelPair α 0) (coherentFormalModulesRestriction I U) := by
  sorry

end AlgebraicGeometry
