/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgClData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility

/-!

# Compact-support base change respects the coefficient comparisons

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`.
Blueprint `sk-thm-sf-compatibility`, (7), asserts that the compact-support base-change
isomorphisms `Ex_! : Rf_! ⋙ Lg^* ≅ Lg'^* ⋙ Rf'_!` of `sk-thm-sf-package`, (2), for the
coefficients `𝒪_E`, `E` and `ℚ̄_ℓ` commute with the coefficient comparisons of blueprint
`sk-prop-scalar-six`. This file states this compatibility for the two coefficient
changes used to pass from integral to `ℚ̄_ℓ`-coefficients:

* `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_toPadicAlgCl`, for the
  inclusion `E ⟶ ℚ̄_ℓ`;
* `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_extendScalars`, for the
  inclusion `𝒪_E ⟶ E`.

Both are inputs from `sec-six-functors`, stated in the form needed by the coefficient
compatibility of the supported restriction
(`CategoryTheory.Adjunction.map_exchangeRestriction_comp`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Compact-support base change `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` with `E`-coefficients for a
finite subextension `E ⊆ ℚ̄_ℓ`: `boundedConstructibleLowerShriekBaseChange` (stated for a normed
field `E`), typed with the coefficient ring `Profinite.continuousMapRingObj E` of the coefficient
comparisons. The two coefficient rings carry the topologies of `E` as a subspace of `ℚ̄_ℓ` and as
a normed field, which agree only after unfolding. -/
noncomputable def boundedConstructibleLowerShriekBaseChange_padicSubfield
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f' :=
  boundedConstructibleLowerShriekBaseChange ℓ E sq

instance isIso_boundedConstructibleLowerShriekBaseChange_padicSubfield
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E sq) :=
  isIso_boundedConstructibleLowerShriekBaseChange ℓ E sq

/-- Compatibility required from `sec-six-functors` (to be proved there): blueprint
`sk-thm-sf-compatibility`, (7): the base-change isomorphism `Ex_!` of `sk-thm-sf-package`, (2),
commutes with the coefficient comparisons of `sk-prop-scalar-six`. For a cartesian square and the
extension of scalars `T : E ⟶ ℚ̄_ℓ`, the image under `T` of compact-support base change
`Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` with `E`-coefficients, read through the pullback and
lower-shriek comparisons of `T`, is compact-support base change with `ℚ̄_ℓ`-coefficients. -/
theorem boundedConstructibleLowerShriekBaseChange_toPadicAlgCl (sq : IsPullback g' f' f g)
    (M : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleToPadicAlgCl Y'.left ℓ E).map
        ((boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E sq).app M) ≫
      (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f').hom.app _ ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E g').hom.app M) =
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E g).hom.app _ ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
        ((boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).hom.app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app _ := by
  sorry

/-- Compatibility required from `sec-six-functors` (to be proved there): blueprint
`sk-thm-sf-compatibility`, (7): the base-change isomorphism `Ex_!` of `sk-thm-sf-package`, (2),
commutes with the coefficient comparisons of `sk-prop-scalar-six`. For a cartesian square and the
extension of scalars `T : 𝒪_E ⟶ E`, the image under `T` of compact-support base change
`Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` with `𝒪_E`-coefficients, read through the pullback and
lower-shriek comparisons of `T`, is compact-support base change with `E`-coefficients. -/
theorem boundedConstructibleLowerShriekBaseChange_extendScalars (sq : IsPullback g' f' f g)
    (M : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleExtendScalars Y'.left ℓ E).map
        ((boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 sq).app M) ≫
      (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f').hom.app _ ≫
      (boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E.1) ℓ f').map
        ((boundedConstructibleUpperStarExtendScalarsIso ℓ E g').hom.app M) =
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E g).hom.app _ ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g).map
        ((boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).hom.app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E sq).app _ :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
