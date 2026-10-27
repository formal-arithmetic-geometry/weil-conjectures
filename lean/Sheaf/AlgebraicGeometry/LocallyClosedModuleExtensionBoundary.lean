/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionModel

/-!
# Open and closed normalizations of the fixed locally closed model

Source: Stacks Project, Tags 09AH, 09AA, 09BN, 03DI, 03DJ and 02V0.
(blueprint: lem-sfb-locally-closed-module-extension-boundary).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- For a single immersion, the fixed closed-then-open model has the normalized open
adjunction and the normalized comparison with actual closed direct image.

Source: Stacks Project, Tags 09AH, 09AA, 09BN, 03DI, 03DJ and 02V0; Steps 3--6 of
lem-sfb-locally-closed-module-extension-coherence.
(blueprint: lem-sfb-locally-closed-module-extension-boundary).

Proof: intersect the ambient opens of two closed-then-open factorizations. Restriction
of closed direct image to that intersection is direct image of the restricted closed
immersion; this is the open-restriction-counit comparison. The two coefficient actions
and closed counits agree under this comparison. Shrinking the ambient open does not
change the extension: the closed image has zero restriction to the removed complement,
so the localization sequence makes the open counit invertible. Thus each factorization
is canonically isomorphic to the extension on the intersection. The triangle identities
for the open unit and the closed counit say that this comparison preserves the specified
restriction maps. Compare the fixed factorization with the factorization of an open map
as identity followed by that open map. Transport its open adjunction; the normalized
restriction is the inverse of its unit. For a closed map compare instead with the map
followed by the identity open immersion. Its extension is actual closed direct image,
and the normalization is exactly its actual counit. This argument also covers clopen
immersions, including identities and the empty source; it never posits an adjunction for
an arbitrary locally closed extension. -/
theorem locallyClosedModel_boundary {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :
    (∀ ha : IsOpenImmersion a.hom, ∃ adj : a.modelExtension ⊣ a.pull,
      LocallyClosedOpenNormalization a.modelExtension a.pull a.modelRestriction adj) ∧
    (∀ ha : IsClosedImmersion a.hom, ∃ e : a.modelExtension ≅ a.push,
      LocallyClosedClosedNormalization a.modelExtension a.push a.pull a.modelRestriction
        (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit e) := by
  sorry

end AlgebraicGeometry.Scheme
