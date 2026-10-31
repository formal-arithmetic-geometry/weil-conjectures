/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateRealization.CondensedTateRealizationData
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # The positive Tate tower and its derived augmentation

Source: Bhatt--Scholze 3.1.10, 6.8.2 and 6.8.4; Stacks 0941.
(blueprint: lem-pur-condensed-tate-augmentation-isomorphism)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures WeilConjectures.CondensedERealization

namespace AlgebraicGeometry.ProEtale.CondensedTateRealization

variable (l : ℕ) [Fact l.Prime]

/-- The specified tensor projections exhibit the positive Tate tower's derived limit.
Source: Bhatt--Scholze 3.1.10, 6.8.2 and 6.8.4; Stacks 0941;
Steps 3--6 of the realization argument
(blueprint: lem-pur-condensed-tate-augmentation-isomorphism).

Proof: Identify the integral condensed coefficient ring with its inverse limit of
finite constant quotients by completedCondensedIntegral and the completed-constant
comparison. The finite root module is killed by the corresponding prime power;
the map r tensor z maps to rho_n(r) z is inverse to z maps to 1 tensor z,
by locally lifting rho_n(r) to an integer. These maps respect root-power transitions;
the level-zero root module is zero, so omitting it does not change the limit.
The locally free Tate-line theorem gives a pro-etale cover with a basis e of the
integral limit line. Repleteness makes its finite projections epic. Their quotient
maps are epimorphisms between rank-one free modules, hence isomorphisms: the image
of 1 is locally a unit since it locally divides 1. Consequently the projections
of e are compatible bases of all finite root modules. Their tensor powers identify
the finite tower on this cover with the finite coefficient tower, and identify
integralPower with its ordinary limit, including d=0. The maps in this limit cone
are precisely powerProjection, by induction on d and the quotient unit equation.
The transitions are epic, being locally the finite quotient maps. Transport through
the exact integralEncoding equivalence. Apply proEtale_surjectiveTower_derivedLimit:
the ordinary limit in degree zero has the Roos triangle on the same product map
1-shift as completedRlim. TR3 and the levelwise-isomorphism theorem compare these
two triangles by an isomorphism. This comparison is the transpose of augmentation:
both have exactly the given cone projections; their difference factors through a
map from a degree-zero sheaf to the product sheaf shifted by -1, which vanishes by
the standard t-structure. Thus it is exactly derivedAugmentation and that map is
invertible. No global primitive root is chosen. The unit case is the coefficient
limit itself; on the empty scheme all the maps are the unique maps of zero sheaves. -/
theorem derivedAugmentation_isIso (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (T : Base k)
    (r : At l (LiftedQ.{u} l) T.scheme) (d : ℕ) :
    IsIso (derivedAugmentation T.scheme l r d) := by sorry

end AlgebraicGeometry.ProEtale.CondensedTateRealization
