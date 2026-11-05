/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import all WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget

/-!
# Direct sums and finite cohomological dimension

Source: the blueprint of the Weil conjectures, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary`, node `lem-kun-0f11`, order 1732; Stacks Project,
Etale Cohomology, Tag 0F11 (`lemma-finite-cd-mod-n-direct-sums`)
(blueprint: lem-kun-0f11).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
