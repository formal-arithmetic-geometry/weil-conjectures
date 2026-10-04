/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!

# The projection formula for compactly supported direct image

Let `A` be a monoidal Grothendieck abelian coefficient category and let `f : X ⟶ Y` be a
morphism of schemes admitting a compactification, so that the compactly supported direct
image `Rf_! : D(X_ét) ⥤ D(Y_ét)` is available. The *projection formula* is the assertion
that the projection map

```
  PF_{f, K, L} : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMapOfCompactification` is an
isomorphism, for `K : D(X_ét)` and `L : D(Y_ét)`.

## Main definitions

- `AlgebraicGeometry.Etale.HasProjectionFormulaOfCompactification` : the projection formula
  for `Rf_!` computed with a given compactification `c` of `f`.
- `AlgebraicGeometry.Etale.HasProjectionFormula` : the projection formula for `Rf_!`
  computed with the chosen compactification `HasCompactification.compactification f`.

## Main statements

- `hasProjectionFormulaOfCompactification_iff_isIso_rightDerivedLowerStarProjectionMap`
  (`sk-prop-sf-pf`) : the projection formula for `Rf_!(c)` at `(K, L)` is equivalent to the
  projection formula for the proper part `Rg_*` of `c = (X ⟶[i] Z ⟶[g] Y)` at `(i_!K, L)`.
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral`
  (`sk-thm-sf-pf-adic`) : the projection formula at the integral stage `𝒪_E`, for derived
  complete objects of finite Tor amplitude.
- `AlgebraicGeometry.Etale.hasProjectionFormula_field` (`sk-thm-sf-pf-field`) : the
  projection formula over a field of coefficients, for bounded constructible objects of
  finite Tor amplitude.
- `AlgebraicGeometry.Etale.hasProjectionFormula_id`,
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`,
  `AlgebraicGeometry.Etale.hasProjectionFormula_comp`,
  `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_iff`
  (`sk-prop-sf-pf-coherence`) : the coherence of the projection formula.

## Implementation notes

The projection map `PF_{f, K, L}` is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMapOfCompactification`, built in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection` from a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`: it is the projection map of `Rg_*` followed by the inverse of
the projection formula for the open immersion `i`. The projection formula is the assertion
`IsIso (PF_{f, K, L})`. Building `PF` needs `Etale.UpperStarPreservesFlat A` and a concrete
structure on `A` (with `forget A` reflecting isomorphisms, preserving filtered colimits and
sheaves); these hold for `A = ModuleCat Λ`. The concrete-category hypotheses are temporary:
they come only from the proof that the open-immersion projection map is an isomorphism, see
the TODO of `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`. The sheaf
condition `HasSheafCompose` is asked on every scheme, rather than only on the scheme of the
compactification, so that the statements do not have to name
`(HasCompactification.compactification f).Z`.

The statements of `sk-prop-sf-pf-coherence` below are still objectwise: the identity case,
the composition law and the independence of the compactification. The blueprint node also
asks for identities between natural transformations — naturality in `f`, the associativity
pentagon, agreement with the direct-image projection formula for proper `f` through
`Rf_! ≅ Rf_*`, and compatibility with finite reduction, scalar extension and the pro-étale
realization. These are not stated yet. Two comparison isomorphisms for `Rf_!` are needed:
- change of compactification:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationIso` exists for
  quasi-compact `f`; the next step is to show that `PF_c` and `PF_d` correspond under it,
  which upgrades `hasProjectionFormulaOfCompactification_iff` to an identity of maps;
- composition: an isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (intended name
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`), not constructed yet; the
  associativity pentagon and `hasProjectionFormula_comp` as an identity of maps depend on it.

The integral stage is modelled exactly as in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient`: the
coefficient category is `ModuleCat 𝒪_E` for `𝒪_E = PadicAlgCl.integers l E` the ring of
integers of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` (transported to the universe `u + 1` by
`Shrink`), and derived completeness is `DerivedCategory.derivedCompleteIntegral`, that is,
derived completeness for the maximal ideal `𝔪_E`.

`AlgebraicGeometry.Etale.hasProjectionFormula_field` is stated for an arbitrary field of
coefficients. The blueprint proves the two instances it needs, `F = E` and `F = ℚ̄_ℓ`, by
rationalizing the integral statement and passing to the `2`-colimit over the finite stages;
that argument does not apply to a general field, so the general case as stated here will need
a different proof.

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

section Composition

variable {X Y Z : Scheme.{u}}

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the compactly supported direct image. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) :=
  sorry

end Composition

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

section Defs

variable {X Y : Scheme.{u}}

/-- The projection formula for a morphism `f : X ⟶ Y`, at `K : D(X_ét)` and `L : D(Y_ét)`,
with `Rf_!` computed from a chosen compactification `c` of `f`: the assertion that the
projection map

```
  PF_c : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMapOfCompactification` is an
isomorphism. -/
def HasProjectionFormulaOfCompactification {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  IsIso (((rightDerivedLowerShriekProjectionMapOfCompactification A c).app K).app L)

omit [HasSmallSiteSheafify A] in
/-- The projection formula for `Rf_!(c)` at `(K, L)` reduces to the projection formula for
the proper part `Rg_*` of `c = (X ⟶[i] Z ⟶[g] Y)` at `(i_!K, L)`: the other two arrows of
`PF_c` are isomorphisms. -/
theorem hasProjectionFormulaOfCompactification_iff_isIso_rightDerivedLowerStarProjectionMap
    {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    HasProjectionFormulaOfCompactification A c K L ↔
      IsIso (((rightDerivedLowerStarProjectionMap A c.g).app
        (D((c.i)_!open[A]).obj K)).app L) := by
  rw [HasProjectionFormulaOfCompactification,
    rightDerivedLowerShriekProjectionMapOfCompactification_app_app]
  exact isIso_comp_right_iff _ _

/-- The projection formula for a morphism `f : X ⟶ Y` admitting a compactification, at
`K : D(X_ét)` and `L : D(Y_ét)`: the assertion that the projection map

```
  PF : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMap` is an isomorphism, with
`Rf_!` the compactly supported direct image `AlgebraicGeometry.Etale.rightDerivedLowerShriek`
attached to the chosen compactification of `f`. -/
def HasProjectionFormula (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  HasProjectionFormulaOfCompactification A (HasCompactification.compactification f) K L

end Defs

section Integral

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-pf-adic`: Projection formula: the derived-complete stage.

At the integral stage of the `ℓ`-adic formalism, where the coefficients are the ring of
integers `𝒪_E` of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`: if `K` and `L` are derived
complete for the maximal ideal `𝔪_E` and of finite Tor amplitude, then the projection
formula holds for `f` at `K` and `L`. -/
theorem hasProjectionFormula_of_derivedCompleteIntegral (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) X K)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) Y L) :
    HasProjectionFormula
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) f K L :=
  sorry

end Integral

section Field

variable (F : Type (u + 1)) [Field F]

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-pf-field`: Projection formula: rational and algebraically closed
stages.

Over a field `F` of coefficients — the blueprint names the two instances `F = E`, the
rational stage, and `F = ℚ̄_ℓ`, the algebraically closed stage — the projection formula
holds for `f` at any bounded constructible `K` and `L` of finite Tor amplitude. -/
theorem hasProjectionFormula_field (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} F)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} F) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} F) Y L) :
    HasProjectionFormula (ModuleCat.{u + 1} F) f K L :=
  sorry

end Field

section Coherence

variable {X Y Z : Scheme.{u}}

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The identity case: the projection formula holds for `f = 𝟙 X`. -/
theorem hasProjectionFormula_id (X : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    HasProjectionFormula A (𝟙 X) K L :=
  sorry

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

Compatibility of the projection formula with the composition law: if the formula holds for
`f` at `K` and `Lg^* M`, and for `g` at `Rf_! K` and `M`, then it holds for `f ≫ g` at `K`
and `M`. This is the objectwise shadow of the blueprint's associativity pentagon; the
pentagon itself is an identity between canonical transformations and is not stated, see the
module docstring. -/
theorem hasProjectionFormula_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hf : HasProjectionFormula A f K ((L((g)^*[A])).obj M))
    (hg : HasProjectionFormula A g ((R(f)_![A]).obj K) M) :
    HasProjectionFormula A (f ≫ g) K M :=
  sorry

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

Independence of the compactification: the formula computed with an arbitrary compactification
`c` of `f` holds if and only if it holds for the chosen one, i.e. for
`AlgebraicGeometry.Etale.HasProjectionFormula`. Applying this to two compactifications `c`
and `c'` shows that the two agree. -/
theorem hasProjectionFormulaOfCompactification_iff {f : X ⟶ Y} [HasCompactification f]
    (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    HasProjectionFormulaOfCompactification A c K L ↔ HasProjectionFormula A f K L :=
  sorry

end Coherence

end Etale

end AlgebraicGeometry
