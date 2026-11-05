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

1. both sides are derived complete: `K` is
   (`ProEtale.derivedCompleteIntegers_of_boundedConstructible`), and derived pushforwards and
   pullbacks preserve derived completeness;
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

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {S W Y X : Scheme.{u}} {p : X ⟶ S} {g : W ⟶ S} {e : Y ⟶ W} {h : Y ⟶ X}

omit [Fact ℓ.Prime] in
/-- The base change map is invertible at `K` as soon as the exchange morphism of the pullback
square comparison is. Stated for an abstract `Λ`: at a concrete coefficient ring, rewriting along
`baseChangeMap_eq_exchangeRight` makes the unifier compare instances elaborated in different
contexts. -/
lemma isIso_baseChangeMap_app_of_isIso_exchangeRight
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (sq : CommSq e h g p)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)))
    (hK : IsIso ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ g)
      (derivedUpperStarLowerStarAdjunction Λ h) (pullbackSquareComparison Λ sq)).app K)) :
    IsIso ((baseChangeMap Λ sq).app K) := by
  rw [baseChangeMap_eq_exchangeRight]
  exact hK

end AlgebraicGeometry.ProEtale.CondensedRing
