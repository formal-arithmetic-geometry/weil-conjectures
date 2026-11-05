/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicBound
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarHeart

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperHeartUniformBound
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts

/-!
# The proper direct image for the `ℓ`-adic coefficient rings: the inputs

Let `ℓ` be a prime, `k` a field in which `ℓ` is invertible, and `p : Z ⟶ Y` a proper morphism to
a noetherian `k`-scheme. For the `ℓ`-adic condensed coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ`, the
properties of the derived direct image `Rp_*` on module objects over `Λ` used for the
compact-support direct image on `Loc(Dᵇc)` (blueprint `det-sf-comp-coherence-single`) are:

* `Rp_*` maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧` (blueprint `sk-thm-sfb-proper-base-change`):
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`;
* for `Y` separated of finite type over `k`, `Rp_*` has finite amplitude on the
  ind-constructible heart and commutes with direct sums there
  (`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses`, blueprints
  `sk-lem-proper-heart-bound` for `E` and `ℚ̄_ℓ`, `det-prop-int-compactness-direct-sums` (1) for
  `𝒪_E`): `properLowerStarHeartHypotheses_continuousMapRingObj`,
  `properLowerStarHeartHypotheses_padicIntegersRingObj`,
  `properLowerStarHeartHypotheses_padicAlgClRingObj`.

From the latter, the restriction of `Rp_*` to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses.preservesColimitsOfShape`,
blueprint `det-prop-int-compactness-direct-sums` (2), (3), proved by dévissage and left
completeness).

The finiteness of `Rp_*` on `Dᵇc` is reduced to residue field coefficients
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness`):
over a noetherian base this uses the finiteness theorem for proper morphisms with torsion
coefficients over a noetherian base
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`),
and over a base of finite type over `k` the proved finite type case
(`boundedConstructible_rightDerivedLowerStar_of_isProper_*_of_finiteType`). The heart hypotheses
follow from the ind-constructible heart (`isIndConstructibleHeart_*`), the continuity of `Rp_*`
(`properLowerStarHeartHypotheses_of_isIndConstructibleHeart`) and a uniform bound on
constructible sheaves
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicBound`); the
ind-constructible heart is stated for separated `k`-schemes of finite type (the setting of the
blueprint), hence the finite type hypotheses on `Y`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-! ### The coefficient ring `E` -/

/-! ### The coefficient ring `𝒪_E` -/

/-- Blueprint `sk-thm-sfb-proper-base-change` (`det-thm-sfb-proper-base-change-integral` (1)):
for the coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a proper morphism
`p : Z ⟶ Y` to a noetherian `k`-scheme, `Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into `Dᵇc(Y)⟦𝒪_E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicIntegersRingObj.{u} ℓ E⟧).obj K) :=
  boundedConstructible_rightDerivedLowerStar_padicIntegersRingObj_of_residueField ℓ p E
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

/-! ### The coefficient ring `ℚ̄_ℓ` -/

end AlgebraicGeometry.ProEtale.CondensedRing
