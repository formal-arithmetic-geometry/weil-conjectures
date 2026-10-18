/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction

import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
/-!
# The comparison unit for sheaves of sets

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
`sk-thm-pe-classical-sheaves-unit`; Stacks Project, Tag 099T
(blueprint: det-pe-classical-sheaves-unit).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The comparison unit is invertible for every etale sheaf of sets, and comparison
inverse image induces a bijection on every Hom set.
Source: Weil conjectures blueprint, main-20261015,
`sk-thm-pe-classical-sheaves-unit`; Stacks Project, Tag 099T
(blueprint: det-pe-classical-sheaves-unit).

Proof:
1. Fix an etale sheaf F and an etale object V over X. Direct image in
   def-weil-pbc-site-comparison-morphism is restriction, so its value at V after inverse
   image is the value of the inverse image at V. Apply
   lem-cbc-comparison-pullback-sections: this value is sections on V of the etale inverse
   image of F, compatibly with the actual comparison unit. By
   lem-weil-pbc-sets-etale-inverse-image-restriction these sections identify with F(V).
   The composite starting with the unit sends each section to itself. Thus the unit
   at V is bijective. All sheaves here are set-valued; no coefficient ring is needed.
2. Invert these component bijections. Naturality of the unit, composed on both sides
   with the component inverses, proves naturality of the inverses. They therefore give
   an inverse sheaf morphism, proving the first clause, also for the empty scheme.
3. The adjunction of def-weil-pbc-site-comparison-morphism identifies morphisms from
   inverse image F to inverse image F' with morphisms from F to direct image of inverse
   image F'. Naturality of the unit identifies the image of inverse image of a morphism
   with its postcomposition by the unit at F'. This postcomposition is bijective by
   step 2, hence so is inverse image on Hom sets. Explicitly the inverse sends psi to
   the composite of the unit at F, direct image of psi, and inverse unit at F'. -/
theorem proEtaleClassicalSheavesUnit (X : Scheme.{u}) :
    (∀ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      IsIso ((proEtaleSiteComparison X).unit.app F)) ∧
    (∀ F F' : Sheaf X.smallEtaleTopology (Type (u + 1)),
      Function.Bijective
        (fun φ : F ⟶ F' ↦
          (Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
            (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).map φ)) := by
  sorry

end AlgebraicGeometry.Scheme
