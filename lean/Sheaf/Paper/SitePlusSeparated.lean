/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf
import Sheaf.CategoryTheory.SiteCoveringsCommonRefinement

/-! # The plus construction is separated and injects into its double plus.

Source: Stacks Project, Sites, Theorem 00WB (parts (1) and (2)).
(blueprint: lem-weil-pbc-sheafification-plus-separated).
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace CategoryTheory.GrothendieckTopology

/-- For a presheaf of sets on a site, the first plus construction is separated,
and its canonical map into the second plus construction is injective.

Source: Stacks Project, Sites, Theorem 00WB (parts (1) and (2)).
(blueprint: lem-weil-pbc-sheafification-plus-separated).

Proof, following the node's three steps:
1. Represent s and s' by compatible families on coverings, using
lem-weil-pbc-site-plus-construction-presheaf (1). Take a common refinement W
of those coverings and the covering where their restrictions agree, using
lem-weil-pbc-site-coverings-common-refinement twice. On each W_j, the restriction
formula (3) of lem-weil-pbc-site-plus-construction-presheaf expresses the two
sections as theta of restricted components x_j and x'_j. These images agree
by presheaf functoriality and the original local equality. The theta equality
criterion (2) of that lemma supplies a covering of W_j where x_j and x'_j
agree. Compose these coverings with W using site axiom (ii)
(def-weil-pbc-sites-and-cohomology). The resulting covering refines both original
representatives, and their compatible families agree componentwise by
functoriality (def-weil-pbc-site-plus-construction). The equality criterion (2)
therefore gives s = s', proving separatedness.
2. For a separated presheaf G, equality of theta(a) and theta(b) is equality
of the identity-cover representatives (def-weil-pbc-site-plus-construction).
The theta equality criterion of lem-weil-pbc-site-plus-construction-presheaf (2)
gives a covering where a and b agree. Separatedness then gives a = b.
3. Apply step 2 to G = P-plus, which is a presheaf by
lem-weil-pbc-site-plus-construction-presheaf (4) and separated by step 1.
This proves injectivity of theta at P-plus on every object.

The generated-topology `plusObj` and `toPlus` are the dependency's recorded
presentation of the covering-family construction; its colimit comparison
is a stage-3 bridge, rather than a second definition.
-/
theorem plus_separated_and_injective
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (P : Cᵒᵖ ⥤ Type (max u w)) :
    (∀ (U : C) (E : Precoverage.ZeroHypercover.{max u w} J U)
      (s s' : (J.toGrothendieck.plusObj P).obj (op U)),
      (∀ i : E.toPreZeroHypercover.I₀,
        (J.toGrothendieck.plusObj P).map (E.toPreZeroHypercover.f i).op s =
          (J.toGrothendieck.plusObj P).map (E.toPreZeroHypercover.f i).op s') →
        s = s') ∧
      (∀ (U : C), Function.Injective
        ((J.toGrothendieck.toPlus (J.toGrothendieck.plusObj P)).app (op U))) := by
  sorry

end CategoryTheory.GrothendieckTopology
