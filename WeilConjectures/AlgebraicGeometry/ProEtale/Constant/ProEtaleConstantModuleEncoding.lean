/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding

/-!
# Restricting a constant ring sheaf to its constant scalars

Source: Stacks Project, Tags 093I and 03CY.
(blueprint: lem-weil-pbc-proetale-constant-module-encoding).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (B : Type u) [CommRing B]

end AlgebraicGeometry.Scheme
