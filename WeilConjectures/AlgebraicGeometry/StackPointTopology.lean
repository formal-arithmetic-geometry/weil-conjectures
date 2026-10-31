/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.Topology.Homeomorph.Defs
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Continuity and smooth-atlas quotient topology for algebraic stacks

Source: Stacks Project, stacks-properties.tex, Tags 04XG, 04XI and 04XL
(blueprint: lem-sfb-stack-point-topology).

No separation, quasi-compactness, finite-type or Deligne--Mumford hypothesis is imposed.
The comparisons with spaces are specified on every field representative, so they are
canonical identifications rather than arbitrary homeomorphisms of point sets.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- Every smooth surjective scheme atlas gives the same quotient topology, all stack
morphisms are continuous, and the scheme and algebraic-space identifications preserve
exactly their usual topologies.
Source: Stacks Project, Tags 04XG, 04XI and 04XL
(blueprint: lem-sfb-stack-point-topology).

Proof, following the five steps of the DAG node:
1. Whiskering preserves field-extension isomorphisms, so `moduliPointMap` is well defined.
The field-extension lifting clause of lem-sfb-stack-chartwise-smooth-etale-calculus
makes each atlas point-surjective. By lem-weil-pbc-morphism-from-spec-field, a field
map to a scheme factors through the residue field of its image; this identifies
scheme points with field classes (def-a1-algebraic-space-point-classes).
2. For two atlases U and V of F, their fibre product is an algebraic space by
lem-sfb-stack-diagonal-space-source-representability and def-trf-scheme-algebraic-space.
Both projections are smooth and surjective by
lem-sfb-stack-chartwise-smooth-etale-calculus. They are continuous by
lem-a1-space-point-open-calculus and open by lem-sfb-flat-lfp-space-universally-open.
3. A continuous open surjection reflects open subsets. The two inverse images of a
stack subset agree on the fibre product, so the two atlas quotient topologies coincide.
Their supremum in def-sfb-stack-point-topological-space is therefore this same topology.
Taking complements gives the closed-set criterion.
4. For a morphism F to G, take atlases U of F and V of G. The algebraic space
U ×_G V has a smooth surjective projection to U and a continuous projection to V,
by the same three calculus nodes. The equality of inverse images on this fibre product,
followed by reflection of openness along its projection to U, proves continuity.
5. For a space the discrete fibre groupoids identify isomorphisms with equality of
field representatives. A smooth surjective atlas is continuous, open and surjective
for the existing space topology (def-a1-space-point-topology and the same calculus
nodes), hence a quotient map. The representative-preserving bijection is a homeomorphism.
For a scheme, its identity atlas and the residue-field classification in step 1 identify
the stack topology with the Zariski topology. Empty atlases are included. -/
theorem stack_point_topology {S : Scheme.{u}} :
    (∀ (F : BasedCategory.{v₁, w₁} (Over S)), IsAlgebraicModuliStack F →
      ∀ (U : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj U)) F),
        IsSmoothModuliAtlas F U p →
          Function.Surjective (moduliSchemePointMap p) ∧
            ∀ D : Set (ModuliPoints F),
              IsClosed D ↔ IsClosed (moduliSchemePointMap p ⁻¹' D)) ∧
    (∀ (F : BasedCategory.{v₁, w₁} (Over S))
        (G : BasedCategory.{v₂, w₂} (Over S)),
      IsAlgebraicModuliStack F → IsAlgebraicModuliStack G →
        ∀ a : BasedFunctor F G, Continuous (moduliPointMap a)) ∧
    (∀ A : AlgebraicSpace S,
      ∃ e : AlgebraicSpace.Point A.obj.obj ≃ₜ ModuliPoints (discreteModuli A.obj.obj),
        ∀ x : AlgebraicSpace.PointRepresentative A.obj.obj,
          e (Quot.mk _ x) = Quot.mk _ (moduliSpaceFieldObject x)) ∧
    (∀ U : Over S,
      ∃ e : U.left ≃ₜ ModuliPoints (discreteModuli (yoneda.obj U)),
        ∀ x : U.left, e x = moduliSchemePointMap (BasedFunctor.id _) x) := by
  sorry

end CategoryTheory
