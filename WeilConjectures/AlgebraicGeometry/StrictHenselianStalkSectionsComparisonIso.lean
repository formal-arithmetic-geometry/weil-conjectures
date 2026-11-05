/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsDescentEquality
import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsDescentSections

/-! # Degree-zero continuity for the specified inverse image -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

