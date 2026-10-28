/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidueExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible

/-!
# Smooth base change with integral coefficients for quasi-compact quasi-separated pushforward

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. Fix a cartesian
square of schemes

```
Y --e--> W
|        |
h        g
v        v
X --p--> S
```

with `p` smooth, `g` quasi-compact and quasi-separated, `ℓ` invertible on `S`, all schemes
quasi-compact and quasi-separated and `W` noetherian. Then the base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K` with coefficients `𝒪_E` is an isomorphism at every bounded
constructible `K` (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`).
No finiteness is assumed on `g`: neither side need be constructible.

This is the blueprint's integral step of `sk-thm-sbc-coefficients`, with derived completeness in
place of constructibility of the two sides:

1. both sides are derived complete: `K` is (`ProEtale.derivedCompleteIntegers_of_boundedConstructible`),
   and derived pushforwards and pullbacks preserve derived completeness;
2. the first derived reduction of the base change map is the pro-étale base change map with
   coefficients `𝔽_E` at the first derived reduction of `K`
   (`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_map_exchangeRight`), which is a
   bounded constructible complex of étale origin, so finite-coefficient smooth base change
   (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`) applies;
3. derived Nakayama
   (`ProEtale.isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}
  {S W Y X : Scheme.{u}} {p : X ⟶ S} {g : W ⟶ S} {e : Y ⟶ W} {h : Y ⟶ X}

variable (ℓ E p) in
/-- **Integral smooth base change for quasi-compact quasi-separated pushforward.** For a
cartesian square `e ≫ g = h ≫ p` of quasi-compact quasi-separated schemes with `p` smooth, `g`
quasi-compact and quasi-separated, `W` noetherian and `ℓ` invertible on `S`, the base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K` with coefficients `𝒪_E` is an isomorphism at every bounded
constructible `K`. -/
theorem isIso_baseChangeMap_app_padicIntegers_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] [IsNoetherian W]
    (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(S, ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) W)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) W) K) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq.toCommSq).app K) := by
  have hK₀ : derivedCompleteIntegers ℓ E W K := derivedCompleteIntegers_of_boundedConstructible hK
  have hsrc := derivedCompleteIntegers_leftDerivedUpperStar_obj p
    (derivedCompleteIntegers_rightDerivedLowerStar_obj g hK₀)
  have htgt := derivedCompleteIntegers_rightDerivedLowerStar_obj h
    (derivedCompleteIntegers_leftDerivedUpperStar_obj e hK₀)
  refine isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map _ hsrc htgt ?_
  have : K.IsGE hK.1.1.choose := hK.1.1.choose_spec
  obtain ⟨α⟩ := nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E sq.toCommSq K
    hK.1.1.choose
  rw [← baseChangeMap_eq_exchangeRight] at α
  refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).2 ?_
  exact ProEtale.isIso_derivedBaseChangeMap_app_of_smooth _ p sq ℓ
    (Fact.out : ℓ.Prime).ne_zero (ProEtale.natCast_eq_zero_residueFieldCoeff.{u} ℓ E) hℓ _
    (ProEtale.boundedConstructible_derivedReduction_obj W ℓ E K hK)

end AlgebraicGeometry.ProEtale.CondensedRing
