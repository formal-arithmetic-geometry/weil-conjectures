/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Incoming kernel and image acyclicity for integer complexes

Source: Stacks Project, Tags 015B and 08C2, conditions (3)(b) and (3)(c).
(blueprint: lem-sc-integer-section-acyclic-incoming-kernel-image).
-/

@[expose] public section

universe u v w
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
