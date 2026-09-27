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

The canonical map itself — the mate of the tensor-hom adjunction against the adjunction
`Rf_! ⊣ Rf^!` — is not available in this repository, so, following the convention of this
branch, the projection formula is recorded as the `Prop`-valued property
`AlgebraicGeometry.Etale.HasProjectionFormula` asserting that the two objects are
*isomorphic*, and the blueprint statements below are statements about that property.

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
  finite Tor amplitude; the two instances the blueprint names are `E` and `ℚ̄_ℓ`.
- `AlgebraicGeometry.Etale.hasProjectionFormula_coherence` (`sk-prop-sf-pf-coherence`) : the
  coherence of the projection formula.

## Implementation notes

The integral stage is modelled exactly as in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient`: the
coefficient category is `ModuleCat 𝒪_E` for `𝒪_E = PadicAlgCl.integers l E` the ring of
integers of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` (transported to the universe `u + 1` by
`Shrink`), and derived completeness is `DerivedCategory.derivedCompleteIntegral`, that is,
derived completeness for the maximal ideal `𝔪_E`.

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

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

omit [HasSmallSiteSheafify A] in
lemma hasProjectionFormula_iff (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    HasProjectionFormula A f K L ↔
      Nonempty ((R(f)_![A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj ((L((f)^*[A])).obj L)) ≅
        ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj K)).obj L) :=
  Iff.rfl

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
formula holds for `f` at `K` and `L`. The blueprint proof assembles the finite-level
isomorphisms `PF_{f, Kₙ, Lₙ}` into a morphism of normalized systems and reconstructs the
integral isomorphism from the uniform tower; the reduction maps are conservative on derived
complete complexes of finite Tor amplitude, which is what upgrades it to an isomorphism. -/
theorem hasProjectionFormula_of_derivedCompleteIntegral (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K ∧
      DerivedCategory.finiteTorAmplitude _ X K)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L ∧
      DerivedCategory.finiteTorAmplitude _ Y L) :
    HasProjectionFormula _ f K L :=
  sorry

end Integral

section Field

variable (F : Type (u + 1)) [Field F]

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-pf-field`: Projection formula: rational and algebraically closed
stages.

Over a field `F` of coefficients — the blueprint names the two instances `F = E`, the
rational stage obtained by rationalizing the `𝒪_E`-objects, and `F = ℚ̄_ℓ`, the
algebraically closed stage, where every object is represented at a finite stage `E'/ℚ_ℓ` —
the projection formula holds for `f` at any bounded constructible `K` and `L` of finite Tor
amplitude. The blueprint proof deduces this from the integral statement
`AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral`: rationalization
is exact and commutes with `Rf_!`, `⊗ᴸ` and `Lf^*`, and the `ℚ̄_ℓ`-stage descends from the
`2`-colimit over the finite stages. -/
theorem hasProjectionFormula_field (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} F)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K ∧
      DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K)
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) Y L ∧
      DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) Y L) :
    HasProjectionFormula _ f K L :=
  sorry

end Field

section Coherence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X Y Z : Scheme.{u}}

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The projection transformations fit together coherently. The clauses stated here are, in
order:

* the **identity case**: the projection formula holds for `f = 𝟙 X`, at every pair of
  objects (there the transformation is the identity);
* the **composition law** `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the compactly supported direct
  image, and the compatibility of the projection formula with it: if the formula holds for
  `f` at `K` and `Lg^* M`, and for `g` at `Rf_! K` and `M`, then it holds for `f ≫ g` at
  `K` and `M` — this is the associativity pentagon of the blueprint, read off objectwise;
* **independence of the compactification**: the formula computed with a compactification
  `c` of `f` holds if and only if it holds for any other compactification `c'`, and if and
  only if it holds for the chosen compactification, i.e. for
  `AlgebraicGeometry.Etale.HasProjectionFormula`.

The remaining blueprint clauses — naturality in `K`, `L` and `f`, agreement with the
direct-image projection formula for proper `f` through `Rf_! ≅ Rf_*`, and compatibility
with finite reduction, scalar extension and the pro-étale realization — are statements
about the canonical comparison transformation itself, which this repository does not
construct; they are not stated here. -/
theorem hasProjectionFormula_coherence (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification (𝟙 X)] (c c' : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (∀ M₁ M₂ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
        HasProjectionFormula A (𝟙 X) M₁ M₂) ∧
      Nonempty (R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) ∧
      (HasProjectionFormula A f K ((L((g)^*[A])).obj M) →
        HasProjectionFormula A g ((R(f)_![A]).obj K) M →
          HasProjectionFormula A (f ≫ g) K M) ∧
      (HasProjectionFormulaOfCompactification A c K L ↔
        HasProjectionFormulaOfCompactification A c' K L) ∧
      (HasProjectionFormulaOfCompactification A c K L ↔ HasProjectionFormula A f K L) :=
  sorry

end Coherence

end Etale

end AlgebraicGeometry
