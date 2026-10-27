/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.StackTopologyOpenSubstacks
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.FiniteFlatAffineGroupoidModuli
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Uniform topological moduli for finite-diagonal Deligne--Mumford stacks

Source: Stacks Project, More on Morphisms of Stacks, Tags 0DUT and 0DUG;
Morphisms of Stacks, Tag 0CI7
(blueprint: lem-sfb-keel-mori-uniform-topological-moduli).

Unique factorization is the bijectivity of precomposition with the actual projection.
All point maps and topologies are the existing field-object quotient constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A finite-diagonal DM stack over a field has a uniform categorical algebraic-space
moduli map which is a universal homeomorphism, including the identity test.
Source: Stacks Project, Tags 0DUT, 0DUG and 0CI7
(blueprint: lem-sfb-keel-mori-uniform-topological-moduli).

Proof:
1. The inertia is the 2-base change of the relative diagonal along itself: an object
is two objects with two isomorphisms, and using the first leaves an automorphism.
Thus every scheme test of inertia is finite by the finite-diagonal hypothesis.
2. Apply lem-sfb-keel-mori-finite-inertia-quotient over Spec k. Obtain a categorical
map c to an algebraic space M and the asserted universal homeomorphism. Categorical
uniqueness identifies any two choices of M, and hence their cartesian local models.
3. By lem-sfb-finite-inertia-etale-affine-charts, choose inertia-preserving separated
etale charts X_i with finite locally free affine groupoid presentations. Pulling back
an etale atlas of X, refining by scheme charts, and composing shows X_i is DM, using
lem-sfb-stack-chartwise-smooth-etale-calculus. Finite inertia pulls back to X_i.
The maps c_i supplied by lem-sfb-finite-flat-affine-groupoid-moduli are uniform
categorical. By lem-sfb-keel-mori-stabilizer-preserving-etale they induce separated
etale M_i to M and X_i equivalent to X times_M M_i. Surjectivity on points of c and
of the chart family shows that the M_i cover M.
4. For flat B to M, set B_i = B times_M M_i. These cover B by
lem-trf-space-fibre-products-etale-covers, and B_i to M_i is flat by the chart calculus.
Associating 2-fibre products identifies the restriction of X times_M B with
X_i times_{M_i} B_i, retaining the projections: on objects keep the same triple and
its comparisons, and on arrows keep the same isomorphism. Uniform categoricity of
c_i factors any map to an algebraic space Y uniquely through B_i.
5. On B_i times_B B_j, both candidate maps have the same composite with the projection
from the restricted stack. This overlap is flat over M_i: its map to B_i is etale,
hence flat, and B_i to M_i is flat. The injective part of the uniform categorical
bijection for c_i forces equality of the two candidate maps on the overlap.
6. Glue these maps by the algebraic-space sheaf condition, refining each scheme test
by etale scheme charts. Sheaf uniqueness proves compatibility with all restrictions,
the factorization equality on the stack, and uniqueness of the resulting map B to Y.
This proves the uniform property, including identity base change. The homeomorphism
clause is inherited from step 2; its identity test gives the homeomorphism for c.
-/
theorem keelMori_uniform_topological_moduli (k : Type u) [Field k]
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (hX : IsDeligneMumfordModuliStack X) (hdiag : HasFiniteModuliDiagonal X) :
    ∃ (M : AlgebraicSpace (Spec (.of k))) (c : BasedFunctor X (discreteModuli M.obj.obj)),
      (∀ (B : AlgebraicSpace (Spec (.of k))) (b : B ⟶ M),
        AlgebraicSpace.MapIsFlat b → ∀ Y : AlgebraicSpace (Spec (.of k)),
          Function.Bijective (fun h : B.obj.obj ⟶ Y.obj.obj ↦
            (moduliTwoFiberFst (discreteModuliMap b.hom.hom) c).comp
              (discreteModuliMap h))) ∧
      (∀ (Z : BasedCategory.{max u v₁ v₂, max (u + 1) w₁ w₂}
          (Over (Spec (.of k)))) (g : BasedFunctor Z (discreteModuli M.obj.obj)),
        IsDeligneMumfordModuliStack Z →
          IsHomeomorph (moduliPointMap (moduliTwoFiberFst g c))) ∧
      IsHomeomorph (moduliPointMap c) := by
  sorry

end CategoryTheory
