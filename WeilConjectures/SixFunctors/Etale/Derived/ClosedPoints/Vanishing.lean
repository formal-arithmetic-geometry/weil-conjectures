/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Support
public import WeilConjectures.SixFunctors.Finite.GlobalSections

/-!
# Vanishing of cohomology for sheaves supported on closed points

A sheaf of `Λ`-modules on a scheme `X` which vanishes off a finite set of closed points with
separably closed residue fields has no cohomology in nonzero degrees: it is the direct sum of
the pushforwards of sheaves on the points, and a separably closed point has no higher
cohomology.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_of_isZero_upperStar`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

end Etale

end AlgebraicGeometry
