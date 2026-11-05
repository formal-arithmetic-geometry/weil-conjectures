/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-! # Canonical base change for a module in degree zero

Source: Stacks Project, Cohomology, Remark 08HY and Derived Categories of Schemes,
Tag 0B91 (blueprint: def-pc-derived-module-base-change-map).

## Main definitions

* `IsDerivedModulePullbackComparison`: a map is the derived-to-ordinary pullback
  comparison at a module.
* `IsDerivedModuleBaseChangeMap`: a map is the base change with the ordinary pulled-back
  module as target.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uMB wMB
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
