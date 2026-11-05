/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Pushforward along a closed immersion of an extension by zero

Let `Λ` be a commutative condensed ring, `c : D ⟶ X` a closed immersion and `U` an open of `X`
containing the complement of the range of `c`, with preimage `V = c⁻¹(U)`. Then
`c_* V_! N ≅ U_! (c|_U)_* N` for every `Λ_V`-module `N`
(`ProEtale.CondensedRing.lowerStarOpenImmersionLowerShriekIso`): the sheaf `c_* V_! N` vanishes
on the closed complement `c(D ∖ V)` of `U`, so it is the extension by zero of its restriction to
`U` (`ProEtale.CondensedRing.isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app`), and
the restriction of `c_*` to the open `U` is computed by the weakly étale base change
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`).

On a scheme with noetherian underlying space the pushforward along a closed immersion is exact
(`ProEtale.CondensedRing.rightDerivedLowerStarSingleIsoOfIsClosedImmersion`), which gives the
derived version `Rc_* V_! Rc'_* L ≅ U_! R(c' ≫ c|_U)_* L` for `L` placed in degree `0`
(`ProEtale.CondensedRing.rightDerivedLowerStarOpenImmersionLowerShriekSingleIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
