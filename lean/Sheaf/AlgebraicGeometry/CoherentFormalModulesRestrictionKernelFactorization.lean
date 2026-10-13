/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel

/-! # Factorization through a restricted formal kernel

Source: Stacks Project, Lemma 087X (lemma-inverse-systems-abelian), construction
(a)--(d) and the final sentence of its proof.
(blueprint: lem-weil-pbc-formal-restriction-kernel-factorization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism killed by a restricted formal-module morphism factors through
its restricted kernel arrow. This concerns kernels only, with no cokernel or finite
product preservation assertion.

Source: Stacks Project, Lemma 087X (lemma-inverse-systems-abelian), construction
(a)--(d) and the final sentence of its proof; step 2 of
lem-weil-pbc-coherent-formal-modules-restriction-limits.
(blueprint: lem-weil-pbc-formal-restriction-kernel-factorization).

Proof:
1. Apply coherentFormalModule_kernel to alpha. It gives a bound c, the stabilized
   image system S, the quotient system K, and the arrow iota with its universal
   property. The given limiting fork is uniquely isomorphic to this kernel fork,
   compatibly with its arrow into F, so it suffices to use this construction.
2. Ordinary module restriction to an open commutes with kernels (sectionwise),
   images (sheafification of the presheaf image), and ideal multiplication images
   (the same finite sums of products of sections). It preserves cokernels as a
   left adjoint. Thus S restricted to U has the same image descriptions with the
   same c, and restriction of every quotient defining K identifies with the
   quotient for the comapped ideal. These identifications commute with quotient
   projections, inclusions, and transition maps by their universal properties.
3. For a formal module T on U and gamma killed by restricted alpha, its component
   at level m+c factors through that level's kernel. The epi transition of T to
   level m forces gamma at level m to factor through the stabilized image S_m|U.
   Compose the factorization at level n+c with the quotient to K_n|U. The
   composite kills the (n+1)-st ideal-power product, so descends through the
   quotient T_(n+c)/I^(n+1)T_(n+c), identified with T_n. Cancel quotient projections
   and the monic image inclusions to check compatibility with transitions. These
   maps give delta, with delta composed with restricted iota equal to gamma.
4. Transport this factorization along the restricted kernel-fork isomorphism
   from step 1. Only existence is asserted here; uniqueness is proved separately
   using the zero transition on the levelwise kernel of the constructed arrow.

No extension of T to X is used, and no termwise injectivity of a formal kernel
arrow is assumed. The argument also covers empty U, zero alpha, I=0, and I=O_X. -/
theorem coherentFormalModules_restriction_kernel_factorization {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    [IsNoetherian U.toScheme] {F G : CoherentFormalModule X I} (α : F ⟶ G)
    (c : KernelFork α) (hc : IsLimit c)
    (T : CoherentFormalModule U.toScheme (I.comap U.ι))
    (γ : T ⟶ (coherentFormalModulesRestriction I U).obj F)
    (hγ : γ ≫ (coherentFormalModulesRestriction I U).map α = 0) :
    ∃ δ : T ⟶ (coherentFormalModulesRestriction I U).obj c.pt,
      δ ≫ (coherentFormalModulesRestriction I U).map c.ι = γ := by sorry

end AlgebraicGeometry
