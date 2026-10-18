/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections

/-! # The essential image of the comparison inverse image

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-thm-pe-classical-sheaves/sk-thm-pe-classical-sheaves-image.md`
(blueprint: det-pe-classical-sheaves-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A pro-étale sheaf of sets is classical exactly when it comes from the étale site,
and exactly when the comparison counit is invertible.
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-thm-pe-classical-sheaves/sk-thm-pe-classical-sheaves-image.md`,
following Bhatt--Scholze, Lemma 5.1.2 (blueprint: det-pe-classical-sheaves-image).

Proof:
1. For (1) implies (2), choose an isomorphism from G to the inverse image of F.
   On every affine presentation, the scheme-general continuity theorem
   `lem-weil-pbc-proetale-classical-continuity-sets` makes the canonical restriction
   cocone for the inverse image a colimit. Naturality of the chosen isomorphism
   identifies its continuity map with that of G, through the bijections on the
   limit object and on the colimit of stage sections. The inverse isomorphism
   induces the inverse colimit map. Thus every continuity map for G is bijective.
2. For (2) implies (3), `IsClassical` says that the specified restriction cocone
   on each affine etale presentation is a colimit. Apply
   `lem-weil-pbc-proetale-continuous-counit-sets`: the section formula identifies
   the counit on such a limit object with exactly this restriction map, and
   affine ind-etale basis coverings detect isomorphisms of sheaves. This gives
   invertibility of the counit on the arbitrary scheme X.
3. For (3) implies (1), take F to be the direct image of G under the recorded
   comparison adjunction. The inverse of its invertible counit supplies the
   isomorphism from G to the inverse image of F. These three implications give
   the two displayed equivalences. -/
theorem proEtaleClassicalSheavesImage (X : Scheme.{u})
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :
    ((∃ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      Nonempty (G ≅
        (Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj F)) ↔
      AlgebraicGeometry.ProEtale.IsClassical G) ∧
      (AlgebraicGeometry.ProEtale.IsClassical G ↔
        IsIso ((proEtaleSiteComparison X).counit.app G)) := by
  sorry

end AlgebraicGeometry.Scheme
