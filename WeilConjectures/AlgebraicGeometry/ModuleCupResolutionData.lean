/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Acyclic resolution data for module cup products

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cup-resolution-data).
The characterization uses resolutions with a sectionwise bilinear chain pairing.
It determines the derived cup product; Godement resolutions supply such pairings.
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

end
end AlgebraicGeometry.Scheme.Modules
