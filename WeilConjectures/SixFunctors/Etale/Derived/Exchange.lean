/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

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
proper map of `c`. As in the blueprint and Stacks 0F7H (Lemma 63.9.4), it holds on the
unbounded derived categories since `Λ` is finite, hence torsion.

The statement for the canonical exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap` is a corollary. That map is only
defined for `Λ` finite and `f'` quasi-compact, and it goes through the comparison isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, which rests on the unproved instance
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison` (Stacks 0F7H,
Lemma 63.9.1).

The projection formula is stated as `IsIso PF` for the projection map
`AlgebraicGeometry.Etale.projectionMap : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)` of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`.

The exchange `Ex_*` for `Rf_*` does already exist in this repository, as
`AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.isIso_projectionMap_app_app`,
  `AlgebraicGeometry.Etale.isIso_projectionMap_of_isClosedImmersion`
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdeal`,
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdeal`

## Main definitions

- `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantIso`: `Lf^* M_Y ≅ M_X`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekReductionModIdeal`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarReductionModIdeal`: the comparisons of `Rf_!`
  and `Rf_*` with finite reduction.
- `AlgebraicGeometry.Etale.reductionModIdealLeftDerivedUpperStarIso`: `Lf^*` commutes with
  finite reduction.
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

/-- **Compact-support base change along a compactification.** For a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `g` arbitrary, a compactification `c` of `f` and `Λ` finite, the exchange transformation
`Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*` of `sk-def-sf-exchanges`, computed with `c`
and its base change, is an isomorphism of functors `D(X_ét, Λ) ⥤ D(Y'_ét, Λ)`.

This is the blueprint's raw finite compact-support base change theorem, stated on the
unbounded derived categories rather than on `D⁺`. By
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap` it
reduces to the invertibility of the derived base change map `Ex_*` for the proper map `c.g`,
which is unbounded proper base change
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite [Finite Λ]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c) :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
    (IsPullback.of_hasPullback c.g g)
  isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c

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
That comparison isomorphism rests on the unproved instance
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, the
independence of `Rf_!` of the compactification on unbounded derived categories with torsion
coefficients (Stacks 0F7H, Lemma 63.9.1). The theorem itself is Stacks 0F7H (Lemma 63.9.4), which
holds on unbounded derived categories for torsion `Λ`. If `f` is quasi-compact,
`[QuasiCompact f']` is obtained from `sq` by `MorphismProperty.of_isPullback`. -/
-- TODO: drop `[QuasiCompact f']` once `Ex_!` is constructed without it.
theorem isIso_rightDerivedLowerShriekBaseChangeMap [Finite Λ] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedLowerShriekBaseChangeMap Λ sq) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite Λ sq
    (HasCompactification.compactification f)
  unfold rightDerivedLowerShriekBaseChangeMap
  infer_instance

end Exchange

section Projection

/-- The derived pullback of a constant sheaf placed in degree `0` is the constant sheaf in
degree `0`: `Lf^*` agrees with the exact functor `f^*` on objects in degree `0`
(`CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso`), and `f^*` carries constant
sheaves to constant sheaves (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`). -/
noncomputable def leftDerivedUpperStarConstantIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} Λ) :
    L((f)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  ((f)^*[ModuleCat.{u + 1} Λ].singleFunctorCompLeftDerivedFunctorIso).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).app M)

variable (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-thm-sf-pf-finite`: Projection formula, finite coefficients

**The projection formula at finite coefficients.** For `Λ` a finite coefficient ring whose
exponent is invertible on `Y`, `f : X ⟶ Y` separated of finite type, `K` bounded constructible
on `X` and `L` bounded constructible *of finite Tor amplitude* on `Y`, the projection map

`PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)`

is an isomorphism, naturally in `K` and `L`. The finite Tor amplitude of `L` is essential: the
fibrewise argument represents the stalks of `L` by bounded complexes of finite free modules. -/
theorem isIso_projectionMap_app_app [Finite Λ]
    [HasInvertibleExponent Λ Y] [LocallyOfFiniteType f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L) :=
  sorry

/-- Blueprint `sk-lem-coprojection`: Co-projection for a closed immersion

**The projection formula for a closed immersion.** For a closed immersion `i`, the projection
map `PF : Ri_! K ⊗^L L ⟶ Ri_!(K ⊗^L Li^* L)` is an isomorphism for *all* `K` and `L`: here
`Ri_! = Ri_*` is exact and the claim is checked on geometric stalks, where both sides are
`K_x̄ ⊗ L_x̄` at points of `Z` and vanish elsewhere. This is the projection formula the
co-projection of `sk-lem-coprojection` is built from. -/
theorem isIso_projectionMap_of_isClosedImmersion (i : X ⟶ Y) [IsClosedImmersion i]
    [HasCompactification i] :
    IsIso (projectionMap (ModuleCat.{u + 1} Λ) i) :=
  sorry

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

**`Rf_!` commutes with finite reduction.** For an ideal `J` of `Λ`, the comparison

`(Rf_! K) ⊗^L (Λ/J)_Y ⟶ Rf_!(K ⊗^L Lf^*(Λ/J)_Y) ≅ Rf_!(K ⊗^L (Λ/J)_X)`,

the projection map `PF` at `L = (Λ/J)_Y` followed by `Lf^*(Λ/J)_Y ≅ (Λ/J)_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarConstantIso`).

This is one of the three compatibilities out of which the comparison square of
`sk-prop-sf-pf-reduction` is built, and the only one that is not formal; it is what reduces
the projection formula at level `n` to the projection formula at level `m ≤ n`. -/
noncomputable def rightDerivedLowerShriekReductionModIdeal (J : Ideal Λ) :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ⟶
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ] :=
  ((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ J)))) ≫
    Functor.whiskerRight ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.map
      (leftDerivedUpperStarConstantIso Λ f (ModuleCat.of Λ (Λ ⧸ J))).hom)
      R(f)_![ModuleCat.{u + 1} Λ]

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

The comparison `AlgebraicGeometry.Etale.rightDerivedLowerShriekReductionModIdeal` is an
isomorphism. -/
theorem isIso_rightDerivedLowerShriekReductionModIdeal (J : Ideal Λ) :
    IsIso (rightDerivedLowerShriekReductionModIdeal Λ f J) :=
  sorry

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

**`Lf^*` commutes with finite reduction.** For an ideal `J` of `Λ`, the canonical
isomorphism

`Lf^*(L ⊗^L (Λ/J)_Y) ≅ Lf^* L ⊗^L Lf^*(Λ/J)_Y ≅ (Lf^* L) ⊗^L (Λ/J)_X`

of the monoidal structure of `Lf^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso`)
and of `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantIso`. Together with the
associativity of `⊗^L` and
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdeal` this is what makes
the comparison square of the blueprint commute. -/
noncomputable def reductionModIdealLeftDerivedUpperStarIso (J : Ideal Λ) :
    reductionModIdeal Λ Y J ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ X J :=
  ((flipFunctor _ _ _).mapIso (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) f)).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ J)))) ≪≫
    Functor.isoWhiskerLeft L((f)^*[ModuleCat.{u + 1} Λ])
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
        (leftDerivedUpperStarConstantIso Λ f (ModuleCat.of Λ (Λ ⧸ J))))

end Projection

section LowerStar

/-- Used in blueprint `sk-lem-finite`.

**`Rf_*` commutes with reduction modulo a principal ideal.** For `f : X ⟶ Y` arbitrary and a
principal ideal `J` of a domain `Λ`, the square

```
  D(X_ét, Λ) ---Rf_*---> D(Y_ét, Λ)
      |                      |
  – ⊗ᴸ (Λ/J)_X           – ⊗ᴸ (Λ/J)_Y
      ↓                      ↓
  D(X_ét, Λ) ---Rf_*---> D(Y_ét, Λ)
```

commutes, through the comparison

`(Rf_* K) ⊗^L (Λ/J)_Y ⟶ Rf_*(K ⊗^L Lf^*(Λ/J)_Y) ≅ Rf_*(K ⊗^L (Λ/J)_X)`

built from the projection map of `Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`).

The hypotheses only serve to make `Λ/J` a perfect `Λ`-module, which is all the proof uses:
for `J = (π)` with `π ≠ 0`, the module `Λ/J` is the cone of `π : Λ → Λ`, and for `J = 0` it
is `Λ`. This is the reduction `𝒪_E → 𝒪_E/𝔪_Eⁿ` that carries `sk-lem-finite` from the finite
stages to the integral stage `𝒪_E`, and the input of
`AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerStar`. -/
noncomputable def rightDerivedLowerStarReductionModIdeal (f : X ⟶ Y) (J : Ideal Λ) :
    R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ Y J ⟶
      reductionModIdeal Λ X J ⋙ R((f)_*[ModuleCat.{u + 1} Λ]) :=
  ((flipFunctor _ _ _).map (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f)).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ J)))) ≫
    Functor.whiskerRight ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.map
      (leftDerivedUpperStarConstantIso Λ f (ModuleCat.of Λ (Λ ⧸ J))).hom)
      R((f)_*[ModuleCat.{u + 1} Λ])

/-- Used in blueprint `sk-lem-finite`.

The comparison `AlgebraicGeometry.Etale.rightDerivedLowerStarReductionModIdeal` is an
isomorphism when `Λ` is a domain and `J` is principal. -/
theorem isIso_rightDerivedLowerStarReductionModIdeal (f : X ⟶ Y) [IsDomain Λ]
    (J : Ideal Λ) (hJ : J.IsPrincipal) :
    IsIso (rightDerivedLowerStarReductionModIdeal Λ f J) :=
  -- Proof sketch: for `J = (π)` with `π ≠ 0`, `π` is a nonzerodivisor, so the constant
  -- complex `(Λ/J)_Z` is the cone of `π : Λ_Z → Λ_Z` and `– ⊗ᴸ (Λ/J)_Z` is the cone of
  -- multiplication by `π`, naturally on `D(Z_ét, Λ)`. The triangulated functor `Rf_*` is
  -- `Λ`-linear, so it commutes with multiplication by `π` and hence with its cone. For
  -- `J = 0` both reductions are isomorphic to the identity.
  sorry

end LowerStar

end Etale

end AlgebraicGeometry
