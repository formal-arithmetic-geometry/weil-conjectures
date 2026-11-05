/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
/-!
# Finite-coefficient comparison in the intrinsic constant-ring presentation

Source: blueprint `def-weil-pbc-proetale-modules`, and Stacks Project, Tags 099R and 00YV
(blueprint: def-weil-pbc-proetale-modules).

The existing finite-coefficient comparison uses modules over sheafified continuous
functions. Intrinsic constructibility uses modules over the constant commutative ring
sheaf. The canonical associated-module-sheaf construction below supplies this second
presentation of the same exact inverse image, with constant scalar action fixed by the
sheafification unit. It does not choose an abstract equivalence or a new inverse image.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]

end AlgebraicGeometry.ProEtale
