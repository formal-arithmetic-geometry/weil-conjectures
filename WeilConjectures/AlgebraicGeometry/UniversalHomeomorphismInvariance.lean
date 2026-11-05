/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleSetPullbackSheafEquivalence
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismIdentity
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismComposition
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismPullback
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

set_option linter.style.haveILetI false

/-!
# Universal-homeomorphism invariance, with functorial compatibility

Source: Stacks Project, Tags 04DZ and 03SI; blueprint
`sec-curve-estimates/lem-sc-arbitrary-curve-cd` (blueprint:
thm-weil-pbc-universal-homeomorphism-invariance).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
