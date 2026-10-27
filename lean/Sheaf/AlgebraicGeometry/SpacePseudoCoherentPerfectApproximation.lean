/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Perfect approximations of pseudo-coherent complexes on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tags 08HP, 08HI, 08HJ and 08JL
(blueprint: lem-sfb-space-pseudocoherent-perfect-approximation).

The fixed small affine etale ringed model represents the original module topos.
Quasi-separatedness is absolute, allowing an arbitrary base scheme. Surjectivity
means an epimorphism of module sheaves, rather than surjectivity on all sections.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Pretriangulated

namespace AlgebraicGeometry.AlgebraicSpace

/-- A pseudo-coherent object has quasi-coherent cohomology and perfect approximations.
Source: Stacks Project, Tag 08HP, `theorem-approximation`, with full support in
Tags 08HI and 08HJ; Tag 08JL, `lemma-pseudo-coherent`
(blueprint: lem-sfb-space-pseudocoherent-perfect-approximation).

Proof:
1. On the affine etale charts, the bounded-above finite-free models have quasi-coherent
   cohomology by kernel/cokernel closure (lem-sfb-space-qcoh-kernels-colimits) and
   the chart criterion (lem-sfb-space-derived-etale-chart-calculus). This is 08JL.
   The same argument gives quasi-coherent cohomology for perfect objects. Brutal
   truncation of the free models makes E b-pseudo-coherent for every integer b.
2. For an affine etale chart Y, transport the scheme supported-approximation theorem
   (lem-sfb-affine-supported-perfect-approximation) across the derived etale/Zariski
   equivalence (lem-sfb-derived-etale-zariski-equivalence). Pseudo-coherence and
   perfectness descend by lem-sfb-etale-pseudocoherence-descent and
   lem-sfb-etale-detects-perfect. Exact faithful restriction preserves and reflects
   vanishing on the complement, so the same support and approximation degree work.
   This proves the affine case of def-sfb-space-supported-perfect-approximation.
3. Apply lem-sfb-space-qcqs-distinguished-square-induction. In each square its overlap
   is quasi-compact, so lem-sfb-space-supported-approximation-square-step supplies
   the induction step. Thus the supported approximation property holds on X (08HP).
4. In that property take the closed subset to be all of |X|, with empty complement.
   For its witness r and any a, E is (a-r)-pseudo-coherent by step 1 and the support
   condition is vacuous. Obtain a perfect P and u : P → E with isomorphisms above a
   and an epimorphism at a. Step 1 gives quasi-coherent cohomology for P.
5. Complete u to a distinguished triangle using TR1. Its cohomology exact sequence
   (lem-sf-derived-homology-long-exact) expresses each cohomology of the cone as an
   extension of a cokernel by a kernel. Kernel/cokernel closure and
   lem-sfb-space-qcoh-extension-closed give quasi-coherent cohomology for the cone.
   No Noetherian, separatedness, finite-type or base-ring condition is used. -/
theorem exists_perfect_approximation
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated)
    (E : X.DerivedModules) (hE : X.IsPseudoCoherent E) :
    X.derivedQCohProperty E ∧
      ∀ a : ℤ, ∃ (P C : X.DerivedQCoh) (u : P.obj ⟶ E)
        (v : E ⟶ C.obj) (δ : C.obj ⟶ P.obj⟦(1 : ℤ)⟧),
        Triangle.mk u v δ ∈ distTriang X.DerivedModules ∧
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
          X.smallStructureSheaf P.obj ∧
        (∀ i : ℤ, a < i → IsIso ((DerivedCategory.homologyFunctor X.SmallModules i).map u)) ∧
        Epi ((DerivedCategory.homologyFunctor X.SmallModules a).map u) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
