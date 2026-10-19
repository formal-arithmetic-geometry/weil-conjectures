/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.OpenImmersionRestriction
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Underived étale base change for an open and closed immersion

Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node lem-kun-base-change-open-closed (blueprint: lem-kun-base-change-open-closed).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Direct image along an open and closed immersion commutes with arbitrary base change,
for the canonical underived exchange and every abelian sheaf on the small étale site.
Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node lem-kun-base-change-open-closed (blueprint: lem-kun-base-change-open-closed).

Proof:
1. The image of `j` is open and closed, so its complement `V` is open. Base change
   preserves open immersions (lem-weil-pbc-open-immersion-base-change). The cartesian
   identification identifies the image of `h` with the inverse image of the image of `j`.
   A geometric point above that image has unique lifts to `U` and `U'`; every other
   point lies above `V`.
2. At a point in the image, inverse-image stalk comparison
   (lem-weil-pbc-inverse-image-stalk-germ) and the open-immersion restriction counits
   (lem-kun-open-immersion-restriction) identify both stalks with the stalk of `F`
   at the lifted geometric point of `U`.
3. Represent a germ by a pointed étale neighbourhood and a section. The unit germ
   formula and the representative formula for def-weil-pbc-underived-exchange send
   that section to its pullback on the base-changed neighbourhood. Its germ at the
   lifted point is the original germ. Thus the actual exchange is the identity under
   the identifications in step 2.
4. Outside the image, refine each pointed étale neighbourhood by its intersection
   with `V`, and on `Y` by the inverse image of `V`. These are still pointed étale
   neighbourhoods (lem-weil-pbc-open-immersion-etale). Their pullbacks to `U` and `U'`
   are empty, respectively. Direct image evaluates there as `F` (or its inverse image)
   on the empty scheme, hence as zero by the empty covering sheaf axiom. Every germ
   therefore vanishes on both sides, and exchange is the isomorphism from zero to zero.
5. Geometric stalks detect isomorphisms
   (lemma-weil-pbc-geometric-stalk-conservative), giving the conclusion. If `Y` is
   empty this applies vacuously; if `U` is empty only step 4 occurs, and if `j` is
   the identity only steps 2 and 3 occur. -/
theorem isIso_baseChangeMap_app_of_isOpenImmersion_of_isClosedImmersion
    {U' U Y X : Scheme.{u}} (p : U' ⟶ U) (h : U' ⟶ Y) (j : U ⟶ X) (g : Y ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] (sq : ChosenCartesianSquare p h j g)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) := by
  sorry

end AlgebraicGeometry.Etale
