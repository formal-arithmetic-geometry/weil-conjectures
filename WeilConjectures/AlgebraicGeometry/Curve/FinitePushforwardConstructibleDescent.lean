/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveSubQuotient
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Finite.Stalk

/-!
# Constructibility descends from finite direct image on curves

Source: Stacks Project, Etale Cohomology, Tags 03QP (1), 095G and 09BH (2),
combined in the converse of Tag 095R in the blueprint
(blueprint: lem-weil-pbc-finite-pushforward-constructible-descent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- Keep the inherited compatibility binder; the counit construction does not need it.

end AlgebraicGeometry
