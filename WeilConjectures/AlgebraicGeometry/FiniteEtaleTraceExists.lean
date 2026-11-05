/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsExistence
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsUniqueness

/-!
# Existence and uniqueness of the finite étale trace

Source: Stacks Project, Section 03SH, following Definition 03SE
(blueprint: lem-weil-pbc-finite-etale-trace-exists).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
