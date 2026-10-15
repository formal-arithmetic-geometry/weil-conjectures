/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import Mathlib.Data.ZMod.Basic

/-!
# Injective acyclicity for prime-field sheaves

Source: Stacks Project, Tag 0A4B, property (2)
(blueprint: def-weil-pbc-injective-acyclicity-property).
-/

@[expose] public section

universe u_ia

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/- The coefficient-aware prime acyclicity definitions are provided by
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty`. -/

end AlgebraicGeometry.Etale
