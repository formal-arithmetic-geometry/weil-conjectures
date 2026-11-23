/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionConstruction

/-!
# Projection squares for restriction to isomorphic coefficient stages

The records contain only compact-support geometry. They contain no exceptional
right adjoints, their evaluations, or their coefficient comparisons.

## References

* W. Zheng, *Six operations and Lefschetz--Verdier formula for Deligne--Mumford stacks*,
  Construction 4.1, Construction 5.15, Lemma 5.22
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

end AlgebraicGeometry
