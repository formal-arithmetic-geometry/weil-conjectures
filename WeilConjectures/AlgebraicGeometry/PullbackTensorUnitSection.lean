/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

@[expose] public section
set_option autoImplicit false
set_option linter.style.longLine false
universe u
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] presheafMonoidalCategory sheafificationMonoidal
  forgetToPresheafOfModulesLaxMonoidal

end AlgebraicGeometry.Scheme.Modules
