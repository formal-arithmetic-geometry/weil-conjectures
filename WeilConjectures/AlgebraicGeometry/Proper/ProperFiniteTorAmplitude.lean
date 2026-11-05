/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperBoundedConstructible
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# Proper direct image preserves finite Tor amplitude

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-tor.md`
(blueprint: det-ctf-finite-proper-tor); Stacks Project, Tags 0F0G and 0F12.

Membership in `Dctf` with a specified Tor interval is expressed by bounded
constructibility together with `hasTorAmplitudeIn` for that interval. This already
includes finite Tor amplitude, both in the hypothesis and in the conclusion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
