/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!

# Proper base change along an arbitrary base, for `ℚ̄_ℓ`-coefficients

For a cartesian square `g' ≫ p = p' ≫ g` of schemes with `p` proper, the base change morphism
`Lg^* Rp_* ⟶ Rp'_* Lg'^*` on the ambient derived categories of `ℚ̄_ℓ`-modules
(`ProEtale.CondensedRing.baseChangeMap`) is invertible at every bounded constructible complex
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_padicAlgCl`). Unlike
`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`, whose squares
consist of schemes of finite type over a field, the base `g` is arbitrary: the nearby cycles use it
for the inclusion `Spec Ω ⟶ Spec k` of a geometric generic point and for the identification of
the geometric generic fibre of a model.

## Input from another subsection

`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_padicAlgCl` is blueprint
`sk-thm-sfb-proper-base-change` (section `sec-six-functors-basics`), read for an arbitrary base
`g`, as in the proof of blueprint `det-sp-nearby-cycles-exchanges` ("proper direct image commutes
with the base change from `η` to `η̄`"). It is `sorry`ed, to be proved with that node: reduce to
an integral model, to finite coefficients by derived Nakayama, and apply the étale proper base
change theorem (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Proper base change**, node-level compatibility required from section
`sec-six-functors-basics` (blueprint `sk-thm-sfb-proper-base-change`), on the ambient derived
categories of `ℚ̄_ℓ`-modules: for a cartesian square `g' ≫ p = p' ≫ g` of schemes with `p`
proper, the base change morphism `Lg^* Rp_* K ⟶ Rp'_* Lg'^* K` is an isomorphism for bounded
constructible `K`. The base `g` is arbitrary (here: the geometric generic point
`Spec Ω ⟶ Spec k`), unlike
`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`,
whose squares are of finite type over a field. -/
theorem isIso_baseChangeMap_app_of_isProper_padicAlgCl {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y}
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p] (sq : CommSq g' p' p g)
    (hsq : IsPullback g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
