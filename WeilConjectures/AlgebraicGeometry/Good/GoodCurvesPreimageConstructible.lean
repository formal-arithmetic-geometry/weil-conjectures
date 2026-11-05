/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesPreimageBoundary

/-!
# Constructibility on the open part of a good-curves compactification

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, proof after
replacing the dense open by its inverse image under the finite good-curves cover.
(blueprint: lem-weil-pbc-good-curves-preimage-constructible)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
