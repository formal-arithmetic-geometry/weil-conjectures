/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf

/-! # A constant-rank exterior complex in the derived category

Source: Stacks Project, Tag 0BR0, the convention for a locally constant shift
(blueprint: lem-sc-constant-rank-exterior-derived-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A constant rank function gives a single exterior power in the indicated degree;
an isomorphism of the input sheaves transports that exterior power.
No smoothness, local freeness or duality hypothesis is needed.
Source: Stacks Project, Tag 0BR0, the expression wedge^r N[-r]
(blueprint: lem-sc-constant-rank-exterior-derived-comparison).

Proof: the fibre of the constant function d over d is all of X, while each other
fibre is empty. Restriction and pushforward along the inclusion of the full open
compose to the identity, and exterior powers commute with this restriction.
Pushforward from an empty open is zero. Thus the locally ranked exterior complex
has exteriorSheaf M d in degree d and zero in every other degree, with zero
 differential. The sectionwise exterior-power maps induced by e and e.inv commute
with restrictions (check on pure wedges) and are inverse; sheafification gives
exteriorSheaf M d isomorphic to exteriorSheaf N d. These maps give a degreewise
isomorphism to the single complex with that sheaf in degree d. Apply the derived
localization functor, and the single/shift comparison: a single in degree d is
the degree-zero single shifted by -d. Empty X and d = 0 obey the same calculation. -/
theorem constantRankExterior_derived_iso {X : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M N : X.Modules) (d : ℕ) (e : M ≅ N) :
    Nonempty (((DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj
        (locallyRankedExteriorComplex M (LocallyConstant.const X d))) ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (exteriorSheaf N d))⟦-(d : ℤ)⟧) := by sorry

end AlgebraicGeometry.Scheme.Modules
