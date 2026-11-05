/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Comparing basic-open sections with sections of the restricted scheme

Source: Stacks Project, Tags 08D2 and 08BS; restriction of scalars for section modules.
(blueprint: lem-sc-principal-open-sections-restriction-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry
