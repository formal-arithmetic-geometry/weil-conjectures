/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# The projection formula for compactly supported direct image

Let `A` be a monoidal Grothendieck abelian coefficient category and let `f : X ⟶ Y` be a
morphism of schemes admitting a compactification, so that the compactly supported direct
image `Rf_! : D(X_ét) ⥤ D(Y_ét)` is available. The *projection formula* is the assertion
that the canonical comparison map

```
  PF_{f, K, L} : Rf_!(K ⊗ᴸ Lf^* L) ⟶ (Rf_! K) ⊗ᴸ L
```

is an isomorphism, for `K : D(X_ét)` and `L : D(Y_ét)`.

## Main definitions

- `AlgebraicGeometry.Etale.HasProjectionFormulaOfCompactification` : the projection formula
  for `Rf_!` computed with a given compactification `c` of `f`.
- `AlgebraicGeometry.Etale.HasProjectionFormula` : the projection formula for `Rf_!`
  computed with the chosen compactification `HasCompactification.compactification f`.

## Main statements

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

The canonical map `PF_{f, K, L}` — the mate of the tensor-hom adjunction against the
adjunction `Rf_! ⊣ Rf^!` — is not available in this repository, so, following the convention
of this folder, the projection formula is recorded as the `Prop`-valued property
`AlgebraicGeometry.Etale.HasProjectionFormula` asserting that the two objects are
*isomorphic*, and the blueprint statements below are statements about that property.

That convention costs `sk-prop-sf-pf-coherence` most of its content. The blueprint node is a
list of identities between natural transformations — naturality in `K`, `L` and `f`, the
associativity pentagon, agreement with the direct-image projection formula for proper `f`
through `Rf_! ≅ Rf_*`, and compatibility with finite reduction, scalar extension and the
pro-étale realization. None of these is expressible without the transformation itself; what
survives is the objectwise shadow of the identity case, of the composition law and of the
independence of the compactification, which is what the four statements below record.

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

section Defs

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}}

/-- The projection formula for a morphism `f : X ⟶ Y`, at `K : D(X_ét)` and `L : D(Y_ét)`,
with `Rf_!` computed from a chosen compactification `c` of `f`: the assertion that

```
  Rf_!(K ⊗ᴸ Lf^* L)  ≅  (Rf_! K) ⊗ᴸ L .
```

The canonical comparison map going from left to right is not constructed in this
repository, so the property records the existence of *some* isomorphism between the two
objects; see the module docstring. -/
def HasProjectionFormulaOfCompactification {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  Nonempty ((Rf_!(c)[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj ((L((f)^*[A])).obj L)) ≅
    ((-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K)).obj L)

/-- The projection formula for a morphism `f : X ⟶ Y` admitting a compactification, at
`K : D(X_ét)` and `L : D(Y_ét)`: the assertion that

```
  Rf_!(K ⊗ᴸ Lf^* L)  ≅  (Rf_! K) ⊗ᴸ L ,
```

with `Rf_!` the compactly supported direct image
`AlgebraicGeometry.Etale.rightDerivedLowerShriek` attached to the chosen compactification
of `f`. -/
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

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X Y Z : Scheme.{u}}

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The identity case: the projection formula holds for `f = 𝟙 X`, where the comparison
transformation is the identity. -/
theorem hasProjectionFormula_id (X : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    HasProjectionFormula A (𝟙 X) K L :=
  sorry

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the compactly supported direct image. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) :=
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
