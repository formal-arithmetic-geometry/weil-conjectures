/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.GroupTheory.PGroup
import WeilConjectures.ConstructibleSheaf.LisseModuleTrivializingTorsor
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import Mathlib.GroupTheory.Sylow

/-!
# A Sylow cover trivializing finitely many lisse sheaves up to an `ℓ`-group

Source: Stacks Project, Tags 0A3R, 0DV5 and 0DV6.
(blueprint: det-tf-restriction-zero-covers, sk-lem-curve-sylow-trace)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

end AlgebraicGeometry
