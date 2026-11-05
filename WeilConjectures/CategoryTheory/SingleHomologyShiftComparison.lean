/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
/-!
# Canonical single-complex shift comparisons

These comparisons isolate the source and unit transport calculations used by
`rightDerivedFunctorPlusUnit_canonical_single_shift`.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

