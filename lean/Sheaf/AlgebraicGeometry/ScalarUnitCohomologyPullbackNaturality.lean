/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
import Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic

/-! # Pullback compatibility of the explicit unit comparison

Source: Stacks Project, Tag 01F7.
(blueprint: new-sc-scalar-unit-pullback-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open Modules

/-- The explicit comparison map, rather than an arbitrary family of equivalences,
intertwines the two structure-sheaf pullback operations.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial and
cohomology-equation-choice; Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: new-sc-scalar-unit-pullback-naturality).

Proof: Compute module cohomology using injective unit-module resolutions. Forget these
resolutions to abelian sheaves; they are acyclic for sections by Tag 03FD. Evaluation at 1
identifies the module Hom complex with its sections complex. The defining cocycle formula
for moduleExtEquiv, followed by forgetting and precomposition with the integer-unit class,
identifies scalarUnitAbelianComparison with this same sections-complex comparison.
For a morphism a, lift the adjoint structure-sheaf map through resolutions as in Tag 01F7;
if its pushforward resolution is not injective, first resolve that pushforward too, and
invert the resulting quasi-isomorphism on sections. Restriction to k-scalars does not
change the additive sections. The scalar inverse-image Ext map followed by the tensor
coefficient map computes the map induced by this lift. The adjunction equation for
tensorPullbackObjUnitToUnit identifies the coefficient map with the structure-sheaf map.
After forgetting scalars, the inverse-image Ext map and the integer constant-sheaf
comparison defining structureSheafCohomologyPullback compute the same lift. Hence both
sides are the same class in the target sections complex. Independence of the lift up to
homotopy gives the equality for every x. For zero cohomology, including the empty scheme
and affine schemes, the equality specializes to equality of the unique zero class. -/
theorem scalar_unit_cohomology_pullback_naturality (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1) :
    scalarUnitAbelianComparison Y
      (scalarCohomologyMap g (tensorPullbackObjUnitToUnit a) 1
        (scalarCohomologyPullback f g a h (SheafOfModules.unit X.ringCatSheaf) 1 x)) =
      structureSheafCohomologyPullback a 1 (scalarUnitAbelianComparison X x) := by
  sorry

end AlgebraicGeometry.Scheme
