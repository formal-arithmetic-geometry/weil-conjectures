module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleEssentiallySmall
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekTensorRight
public import WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection
public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek

/-! Declarations of ours that lived in the upstream file `WeilConjectures.SixFunctors.Etale.Derived.Exchange` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Compact-support base change, the projection formula and finite reduction

The two theorems of the six-functor formalism attached to `Rf_!` that the purity chapter
consumes: compact-support base change for a cartesian square, and the projection formula.
Alongside them, the compatibilities of `Rf_!`, `Lf^*` and `Rf_*` with the reduction
`K ↦ K ⊗ᴸ (Λ/J)` of the coefficients modulo an ideal `J`.

## Implementation notes

Compact-support base change is stated as `IsIso Ex_!` for the exchange
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of the framework chapter's `sk-def-sf-exchanges`, on the
unbounded derived categories. The main form is for the exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` computed with
an arbitrary compactification `c` of `f`: it reduces to unbounded proper base change for the
proper map of `c`. The blueprint states it on `D⁺` instead.

The statement for the canonical exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap` is a corollary. That map is only
defined for `f'` quasi-compact, and it goes through the comparison isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, which is defined for torsion coefficients
and rests on unbounded proper base change. The hypothesis `[QuasiCompact f']` should disappear
once `Ex_!` is constructed on `D⁺`.

The projection formula is stated as the invertibility of the projection map
`PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)` of `AlgebraicGeometry.Etale.projectionMap`
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`, in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`); its case of `sk-thm-sf-pf-finite`,
for `K` bounded constructible and `L` in `Dᵇctf`, is
`AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`.

The exchange `Ex_*` for `Rf_*` does already exist in this repository, as
`AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_leftDerivedUpperStar`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Exchange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `sk-prop-sf-cbc`: Compact-support base change

**Compact-support base change.** For `f : X ⟶ Y` admitting a compactification, `g : Y' ⟶ Y`
arbitrary, a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f'` quasi-compact and admitting a compactification, and `Λ` finite, the exchange
transformation `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of `sk-def-sf-exchanges` is an isomorphism of
functors `D(X_ét, Λ) ⥤ D(Y'_ét, Λ)`.

`Ex_!` is `Ex_!(c)` for the chosen compactification `c` of `f`, followed by the comparison
isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` for `f'`, so this follows from
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`.
That comparison isomorphism is
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, which rests
on unbounded proper base change; the blueprint states this theorem on `D⁺`. If `f` is
quasi-compact, `[QuasiCompact f']` is obtained from `sq` by `MorphismProperty.of_isPullback`. -/
-- TODO: state this for the `D⁺` exchange map built from `derivedBaseChangeMapPlus`, and drop
-- `[QuasiCompact f']` once `Ex_!` is constructed without it.
end Exchange

section Projection

variable (f : X ⟶ Y) [HasCompactification f]

omit [HasCompactification f] in
private theorem constant_projection_of_preservesCoproducts {Z : Scheme.{u}} (g : Z ⟶ Y)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (R((g)_*[ModuleCat.{u + 1} Λ]))]
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : ModuleCat.{u + 1} Λ) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y N)) := by
  let A := ModuleCat.{u + 1} Λ
  let τ := Functor.whiskerLeft (constantFunctor Λ Y)
    (rightDerivedLowerStarProjectionMapApp Λ g K)
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) (L((g)^*[A])) :=
    (derivedUpperStarLowerStarAdjunction _ g).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have e (M : A) :
      (constantFunctor Λ Y).obj ((_root_.DerivedCategory.singleFunctor A 0).obj M) ≅
        constantSingle A Y M :=
    (Functor.mapDerivedCategorySingleFunctor _ 0).app M
  have key := _root_.DerivedCategory.isIso_app_singleFunctor_obj τ (by
    change IsIso ((rightDerivedLowerStarProjectionMapApp Λ g K).app _)
    exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso (e _).symm
      (isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_self Λ g K)) N
  exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso (e N) key

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

**`Rf_!` commutes with finite reduction.** For an ideal `J` of `Λ`,

`Rf_!(K ⊗^L (Λ/J)_X) ≅ (Rf_! K) ⊗^L (Λ/J)_Y`.

This is one of the three compatibilities out of which the comparison square of
`sk-prop-sf-pf-reduction` (`AlgebraicGeometry.Etale.projectionMapOfCompactification_constantSingle`)
is built, and the only one that is not formal; it is what reduces the projection formula at
level `n` to the projection formula at level `m ≤ n`. -/
-- STATEMENT-DISPUTED: the cited finite-reduction unit assumes finite coefficient rings.
-- This declaration instead quantifies over arbitrary rings and ideals on unbounded categories.
-- The proper projection theorem available here requires additive torsion; the arbitrary-ring
-- argument applies to dualizable quotient complexes. Neither hypothesis is present below.
-- This is a source/interface dispute, not a claim to have constructed a counterexample.
omit [HasCompactification f] in
end Projection

section LowerStar

private theorem isDualizable_constantSingle_principalQuotient [IsDomain Λ]
    (J : Ideal Λ) (hJ : J.IsPrincipal) :
    IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) Y (ModuleCat.of Λ (Λ ⧸ J))) := by
  obtain ⟨π, rfl⟩ := hJ.principal
  by_cases hπ : π = 0
  · have hbot : (Submodule.span Λ {π} : Ideal Λ) = ⊥ := by
      rw [hπ]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    rw [hbot]
    exact isDualizable_constantSingle_quotient_bot Λ Y
  · have hpow : (Submodule.span Λ {π} : Ideal Λ) = Ideal.span {π} ^ 1 := (pow_one _).symm
    rw [hpow]
    exact isDualizable_constantSingle_quotient_span_pow
      (mem_nonZeroDivisors_of_ne_zero hπ) 1 Y

end LowerStar

end Etale

end AlgebraicGeometry
