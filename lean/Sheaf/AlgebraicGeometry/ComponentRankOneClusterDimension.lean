/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex
public import Sheaf.AlgebraicGeometry.NodalIdealScalarGluing
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch
import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
import Sheaf.TraceFormula.NodalSubcurveBoundary
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

/-! # Rank-one component restrictions of subcanonical clusters

Source: Franciosi--Tenni, On Clifford's theorem for singular curves, Lemma 3.6(i),(ii),
pp.240--242, specialized to B = X = X_red and the first degree lower bound
(blueprint: lem-sfb-component-rank-one-cluster-dimension).

The restriction map first includes the ideal twist into the dualizing module and
then pulls that module back to the reduced component. Its image is expressed as the
span of its range; the map is linear, so this is its actual image subspace.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Rank-one restrictions give the dimension and residual degree of the cluster.
Source: Franciosi--Tenni, Lemma 3.6(i),(ii), pp.240--242, B = X = X_red
(blueprint: lem-sfb-component-rank-one-cluster-dimension).

Proof plan:
1. Projectivity implies properness (lem-kun-projective-implies-proper). The nodal
   normalization model makes the curve Noetherian with finitely many components.
   The finite-type coherence criterion, closed-immersion cohomology, and coherent
   kernel/cokernel closure apply to all the ideal twists and subcurve modules.
   Nodal Serre duality gives invertible omega and chi(omega) = -chi(O_X).
   Choose a subcanonical section s. The rank-one restrictions express every section
   on each component as a unique scalar multiple of s. Generic-point detection for
   the reduced-curve dualizing module makes these coefficients injective.
2. Apply lem-sfb-nodal-ideal-scalar-gluing. Its constrained nodes define a finite
   graph on the components. Sections correspond exactly to coefficient vectors
   constant on its connected blocks A_j. The indicator vectors form a basis, with
   m blocks and dim V = m. Self-nodes add no relation.
3. By def-sfb-subcanonical-splitting-index, supported sections are spanned by the
   indicators whose entire block is in the support. The graph partition is
   admissible, and every admissible partition is coarser. For nonempty S this
   gives r(S) = m - 1.
4. The component-stalk calculus and lem-trf-closed-union-pushout give the restriction
   and difference exact sequence for a binary component union. The nodal boundary
   is a finite reduced set of rational nodes. Closed cohomology, Euler additivity,
   and the zero-dimensional Euler formula give chi(E) - chi(O_X) = e for
   E = direct sum of the pushed-forward O_A_j, where e counts interblock nodes.
   Connectedness of X gives a connected block graph, hence e >= m - 1.
5. Multiplication by the block indicators embeds E into I_S tensor omega. The
   dualizing generic-point detection and the reduced component-stalk calculus
   give injectivity; its coherent cokernel Q has zero-dimensional support. Thus
   chi(Q) >= 0. The ideal-twist exact sequence and Euler additivity give
   2 p_a - 2 - length(S) = e + chi(Q) >= m - 1, proving the degree bound.
6. If S is empty, its index is zero by convention. Serre duality applied to each
   pushed-forward O_A_j gives h1(O_A_j) = 1. The proper reduced connected global
   functions theorem and dimension-one vanishing give chi(O_A_j) = 0, hence
   chi(O_X) = -e and m = p_a = e + 1. If m > 1, two-connectedness gives at least
   two boundary nodes per block, so e >= m, a contradiction. Hence m = 1.
-/
theorem component_rank_one_cluster_dimension
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (hTwoConnected : ∀ (A B : Scheme.{u}) (a : A ⟶ X) (b : B ⟶ X),
      IsClosedImmersion a → IsClosedImmersion b → IsReduced A → IsReduced B →
      Nonempty A → Nonempty B →
      (∃ P Q : Set (Set X), P ⊆ irreducibleComponents X ∧ Q ⊆ irreducibleComponents X ∧
        Disjoint P Q ∧ P ∪ Q = irreducibleComponents X ∧
        Set.range a = ⋃₀ P ∧ Set.range b = ⋃₀ Q) →
      2 ≤ Module.finrank k (scalarCohomology
        (CategoryTheory.Limits.pullback.fst a b ≫ a ≫ X ↘ Spec (.of k))
        (unit (CategoryTheory.Limits.pullback a b)) 0))
    (S : Scheme.{u}) (i : S ⟶ X) [IsClosedImmersion i]
    (D : SubcanonicalClusterData k X S i)
    (hSsub : IsSubcanonicalCluster i D.dualizing)
    (hRankOne : ∀ C : irreducibleComponents X,
      Module.finrank k (Submodule.span k
        (M := scalarObj (NodalIdealScalarGluing.componentι C ≫ X ↘ Spec (.of k))
          ((tensorPullback (NodalIdealScalarGluing.componentι C)).obj D.dualizing) (op ⊤))
        (Set.range
          (fun s : scalarObj (X ↘ Spec (.of k)) (subcanonicalModule i D.dualizing) (op ⊤) ↦
            tensorPullbackTopSection (NodalIdealScalarGluing.componentι C) D.dualizing
              ((subcanonicalModuleInclusion i D.dualizing).val.app (op ⊤) s)))) = 1) :
    Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
      (subcanonicalModule i D.dualizing) 0) = subcanonicalSplittingIndex D + 1 ∧
    (0 < subcanonicalSplittingIndex D →
      (subcanonicalSplittingIndex D : ℤ) ≤
        2 * (1 - eulerChar k (unit X)) - 2 -
          (Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) : ℤ)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
