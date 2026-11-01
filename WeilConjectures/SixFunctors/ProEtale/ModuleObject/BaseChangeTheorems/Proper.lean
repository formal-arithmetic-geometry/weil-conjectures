/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralExchangeReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralReductionConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriekUnit

/-!

# The proper base change theorem for constructible `𝒪_E`-, `E`- and `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`. Its
condensed ring is `E̲ = C(-, E)` (`Profinite.continuousMapRingObj E`, of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`), and the coefficient ring
on `X_proét` is `E_X = p_X^* E̲`. Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the proper base
change theorem for bounded constructible `E`-sheaves: the base-change morphism
`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` is an
isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`. No hypothesis is imposed on `g`. The same
holds for the condensed ring `ℚ̲̄_ℓ` of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
(`Profinite.padicAlgClRingObj`), whose sections are continuous maps into finite
subextensions of `ℚ̄_ℓ`.

The same holds for the condensed ring `𝒪̲_E` (`Profinite.padicIntegersRingObj`) of a finite
extension `E` of `ℚ_ℓ` embedded in `ℚ̄_ℓ`.

All three are deduced from the torsion case, as in the proof of blueprint
`sk-thm-sbc-coefficients`.
A bounded constructible `E`-complex is `E ⊗ᴸ_{𝒪_E} K₀` for a bounded constructible
`𝒪_E`-complex `K₀` (`ProEtale.exists_boundedConstructibleExtendScalars_obj_iso`), and a bounded
constructible `ℚ̄_ℓ`-complex is `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀` for some `E` and `K₀`
(`ProEtale.exists_padicAlgCl_iso_integralModel`). The scalar comparisons identify the base-change
morphism at these complexes with the extension of scalars of the integral base-change morphism at
`K₀` (`nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational`,
`isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral`). By derived Nakayama, the latter
is invertible once its first derived reduction `- ⊗ᴸ_{𝒪_E} 𝔽_E` is
(`isIso_boundedConstructibleBaseChange_integral_app_of_reduction`). That reduction is the
pro-étale base-change morphism with coefficients `𝔽_E` at a complex of étale origin
(`ProEtale.boundedConstructible_derivedReduction_obj`), an isomorphism by finite-level
pro-étale proper base change (`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`), which is
the étale proper base change theorem `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`
read on the pro-étale site.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes are
separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms of `Over (Spec (.of k))`.

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers`: proper
  base change on bounded constructible `𝒪_E`-sheaves.
- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`: proper base
  change on bounded constructible `E`-sheaves.
- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`: proper
  base change on bounded constructible `ℚ̄_ℓ`-sheaves.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The proper base change theorem** for bounded constructible `𝒪_E`-sheaves (blueprint
`sk-thm-sfb-proper-base-change`), `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`: for a cartesian
square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y')⟦𝒪̲_E⟧`. This is the integral analogue of
`isIso_boundedConstructibleBaseChange_of_isProper`; it reduces to the étale proper base change
theorem `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` by finite reduction and
integral Nakayama (Bhatt–Scholze, Sections 6.7–6.8). The induced norm identifies the coefficient
with the continuous integral coefficient. The reduction of each base-change component is
invertible by `integralExchange_reduction_isIso`; `integralReduction_reflects_isIso` then gives
its invertibility on the Noetherian target, and componentwise invertibility assembles to an
isomorphism of functors. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers [IsProper f.left]
    (sq : IsPullback g' f' f g) :
    IsIso (PadicIntegersRingObj.boundedConstructibleBaseChange
      ℓ E sq.toCommSq) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E := ⟨fun a x ↦ by
    change ‖algebraMap E (PadicAlgCl ℓ) (a • x)‖ ≤
      ‖a‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
      PadicAlgCl.norm_extends]⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  let : LocallyOfFiniteType (X'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X'.hom›
  let : QuasiCompact (X'.left ↘ Spec (.of k)) := ‹QuasiCompact X'.hom›
  let : IsSeparated (X'.left ↘ Spec (.of k)) := ‹IsSeparated X'.hom›
  let : LocallyOfFiniteType (Y'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y'.hom›
  let : QuasiCompact (Y'.left ↘ Spec (.of k)) := ‹QuasiCompact Y'.hom›
  let : IsSeparated (Y'.left ↘ Spec (.of k)) := ‹IsSeparated Y'.hom›
  let : IsNoetherian (Spec (.of k)) := {}
  let : IsNoetherian Y'.left := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType
    (Y'.left ↘ Spec (.of k))
  have hbc : IsIso (UnitBallRingObj.boundedConstructibleBaseChange ℓ
      (continuousIntegers ℓ E) sq.toCommSq) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    have hred := integralExchange_reduction_isIso ℓ E k
      (X := X.left) (Y := Y.left) (X' := X'.left) (Y' := Y'.left)
      (f := f.left) (g := g.left) (f' := f'.left) (g' := g'.left)
      (sq.map (Over.forget (Spec (.of k)))) K
    exact integralReduction_reflects_isIso ℓ E Y'.left _ hred
  have hbcO (O : Subring E) [Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]
      (hO : O = continuousIntegers ℓ E) :
      IsIso (UnitBallRingObj.boundedConstructibleBaseChange ℓ O sq.toCommSq) := by
    subst O
    exact hbc
  have : Fact (∀ x : E, x ∈ (PadicAlgCl.integers ℓ E).toSubring ↔ ‖x‖ ≤ 1) := ⟨by
    intro x
    change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]⟩
  have hO : (PadicAlgCl.integers ℓ E).toSubring = continuousIntegers ℓ E := by
    ext x
    rfl
  have hbc' := hbcO (PadicAlgCl.integers ℓ E).toSubring hO
  rw [PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
  rw [UnitBallRingObj.boundedConstructibleBaseChange_eq_exchangeRight] at hbc'
  exact hbc'

/-- **The proper base change theorem** (blueprint `sk-thm-sfb-proper-base-change`) for bounded
constructible `E`-sheaves, `E` a finite extension of `ℚ_ℓ`: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [IsProper f.left] (sq : IsPullback g' f' f g) :
    IsIso (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq.toCommSq) := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨K₀, ⟨e⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X.left ℓ E K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  obtain ⟨α⟩ := nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational ℓ E
    sq.toCommSq K₀
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E.1 sq
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).1 (by
    simp only [MorphismProperty.isomorphisms.iff]
    infer_instance)

/-- **The proper base change theorem** (blueprint `sk-thm-sfb-proper-base-change`) for bounded
constructible `ℚ̄_ℓ`-sheaves: for a cartesian square of schemes `sq : IsPullback g' f' f g` with
`f` proper, the base-change morphism
`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an isomorphism of functors
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`, for the condensed ring
`ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl [IsProper f.left]
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange ℓ sq.toCommSq) := by
  have hsq : IsPullback g'.left f'.left f.left g.left := sq.map (Over.forget _)
  have := isNoetherian_of_locallyOfFiniteType X.hom
  exact isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral ℓ _ hsq fun E K₀ ↦
    have := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E.1 sq
    inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
