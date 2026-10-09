/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Presentation
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Finiteness, perfectness, flat models and Künneth

The four finiteness inputs the purity chapter takes from the six-functor formalism:

* `Rf_*` and `Rf_!` preserve bounded constructibility, with a cohomological-dimension bound
  in terms of the fibre dimension (`sk-prop-sf-finiteness`);
* compactly supported cohomology is a perfect complex of `Λ`-modules
  (`sk-prop-sf-trace-perfectness`);
* finite Tor amplitude in `[a, b]` is the same as admitting a bounded flat model concentrated
  in `[a, b]` (`sk-lem-sf-flat-model`);
* the Künneth formula and the projection formula in ordinary étale cohomology
  (`sk-prop-sf-kunneth-ordinary`).

Throughout, `Λ` is a finite coefficient ring whose exponent is invertible on the schemes in
question (`AlgebraicGeometry.HasInvertibleExponent`) and the schemes are of finite type over a
field: without the invertibility the Artin–Schreier sequence already defeats constructibility
of `R¹f_*` in characteristic `p`.

## Implementation notes

`sk-prop-sf-trace-perfectness` concludes that `RΓ_c(X, K)` is *perfect*: bounded, with finite
cohomology modules, and of finite Tor amplitude. The first two are stated below; the third is
not, because the repository has no Tor-amplitude notion for objects of `D(ModuleCat Λ)` — only
for complexes of sheaves. The geometric-stalk half of the same subsection is likewise omitted.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`
  (`sk-thm-sf-direct-image-tor-amplitude`, constructibility half)
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`
- `AlgebraicGeometry.Etale.finite_compactlySupportedCohomology`
- `AlgebraicGeometry.Etale.torAmplitudeIn_iff_exists_flatModel`
- `AlgebraicGeometry.Etale.torAmplitudeIn_iff_exists_flatConstructibleModel`
- `AlgebraicGeometry.Etale.nonempty_iso_kunneth`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Finiteness

variable [Finite Λ] {k : Type u} [Field k]

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of direct images.** Let `Λ` be a finite ring whose exponent is invertible on `X`
and let `f : X ⟶ Y` be a quasi-compact morphism of finite-type `k`-schemes. Then `Rf_*`
carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`; separatedness of `f` is not needed.

The underlying numerical input is that the torsion cohomological dimension of a finite-type
`k`-scheme of dimension `d` over a field of torsion cohomological dimension at most `c` is
bounded by `2d + c`; in particular it is `0` for the spectrum of a separably closed field. -/
theorem boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (f : X ⟶ Y)
    [QuasiCompact f] [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude

Let `Λ` be a finite ring whose exponent is invertible on `X`, let `f : X ⟶ Y` be a separated
quasi-compact morphism of finite-type `k`-schemes with `dim X ≤ d`, and let `K` be a bounded
constructible complex on `X_ét` with Tor amplitude in `[a, b]`. Then `Rf_* K` is bounded
constructible on `Y_ét`.

This is the constructibility half of the blueprint theorem, whose Tor-amplitude half
(`Rf_* K` has Tor amplitude in `[a, b + 2d]`) is not stated on this branch. The constructibility
is `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
(`sk-prop-sf-finiteness`); the dimension bound and the Tor amplitude are only used by the other
half. The finite-coefficient and invertible-exponent hypotheses are necessary: for `Λ = 𝔽_p` and
the structure morphism of `𝔸¹` over `𝔽̄_p`, `H¹(𝔸¹, 𝔽_p)` is infinite by Artin–Schreier. -/
theorem boundedConstructible_rightDerivedLowerStar (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]
    [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] (hf : f ≫ aY = aX) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of compactly supported direct images.** For `f : X ⟶ Y` separated of finite type
between finite-type `k`-schemes, `Rf_!` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`. -/
theorem boundedConstructible_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**The fibre-dimension bound.** If `e` bounds the dimensions of the *geometric* fibres of a
separated finite-type `f : X ⟶ Y`, then `R^q f_! K = 0` for `q > 2e` and every bounded
constructible `K`. -/
theorem isZero_homology_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (q : ℤ) (hq : (2 * e : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) :=
  sorry

end Finiteness

section Perfectness

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [HasCompactification aX]
  [HasInvertibleExponent Λ X]

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Boundedness of compactly supported cohomology.** Let `Λ` be a finite coefficient ring, `k`
separably closed, `X` separated of finite type over `k` with structure morphism `a_X`, and
`K ∈ D^b_{ctf}(X, Λ)`. Then `RΓ_c(X, K) = Ra_{X!} K` vanishes in all but finitely many
degrees. Separable closedness of the base is essential: over `Spec ℚ` already
`H¹_c(Spec ℚ, ℤ/n) = Hom(G_ℚ, ℤ/n)` is infinite. -/
theorem isZero_compactlySupportedCohomology_of_lt
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Finiteness of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, every compactly supported
cohomology module `H^q_c(X, K)` is a finite `Λ`-module. Together with boundedness and finite
Tor amplitude these are exactly perfectness over the Artinian local ring `A_{E,n}`. -/
theorem finite_compactlySupportedCohomology
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) (q : ℤ) :
    Module.Finite Λ ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) :=
  sorry

end Perfectness

/-- Blueprint `sk-lem-sf-flat-model`: Bounded flat model of finite Tor amplitude

**Finite Tor amplitude means a bounded flat model.** For `K ∈ D^b_c(X, Λ)` and integers
`a ≤ b` the following are equivalent: `K` has Tor amplitude in `[a, b]`; and `K` is isomorphic
to a complex `P` of flat sheaves with `P^q = 0` for `q ∉ [a, b]`.

One direction is that a bounded-above complex of flat sheaves is K-flat; the other truncates a
bounded-above free resolution and checks that the truncation is flat by the Tor criterion. -/
theorem torAmplitudeIn_iff_exists_flatModel (a b : ℤ) (hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
          Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) :=
  sorry

/-- Blueprint `sk-lem-sf-flat-model`: Bounded flat model of finite Tor amplitude

**Constructible variant.** Let `X` be Noetherian and `Λ` finite. For `K ∈ D^b_c(X, Λ)` and
integers `a ≤ b`, `K` has Tor amplitude in `[a, b]` if and only if it is isomorphic to a bounded
flat complex `P` in degrees `[a, b]` whose terms are *constructible*. In particular every object
of `Dctf(X, Λ)` has such a model.

The bounded-above resolution of `torAmplitudeIn_iff_exists_flatModel` is built with terms
finite sums of sheaves `j_{V!} Λ_V`, by `Scheme.exists_epi_sigma_lowerShriek_constantSheaf`
applied to the constructible cohomology sheaves of `K` and to the constructible kernels and
cokernels that arise (`Scheme.IsConstructibleSheaf.kernel`,
`Scheme.IsConstructibleSheaf.cokernel`); its truncation in degree `a` is then a cokernel of a
map of constructible sheaves, hence flat and constructible. The converse is the corresponding
direction of `torAmplitudeIn_iff_exists_flatModel`. Finiteness of `Λ` is needed: for
`Λ = ℤ` a flat constructible sheaf has finite flat stalks, hence is zero. -/
theorem torAmplitudeIn_iff_exists_flatConstructibleModel [Finite Λ] [IsNoetherian X]
    (a b : ℤ) (hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
          (∀ q : ℤ, IsConstructibleSheaf (P.X q)) ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) :=
  sorry

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [LocallyOfFiniteType aY]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- Blueprint `sk-prop-sf-kunneth-ordinary`: Künneth and the projection formula in ordinary
étale cohomology

**Künneth.** Let `k` be separably closed, let the exponent of `Λ` be invertible on `X` and `Y`
and let `X`, `Y` be finite-type `k`-schemes. For the cartesian square

```
  W --p₂--> Y
  |         |
  p₁        a_Y
  |         |
  v         v
  X --a_X-> Spec k
```

exhibiting `W = X ×_k Y`, the exterior-product map

`RΓ(X, E) ⊗^L RΓ(Y, K) ≅ RΓ(X ×_k Y, Lp₁^* E ⊗^L Lp₂^* K)`

is an isomorphism for all `E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)` — unbounded, and with no
properness hypothesis. Without the cartesian hypothesis the statement is false: for `W = ∅`
and `X = Y = Spec k` the right-hand side is `0` and the left-hand side is `Λ`. -/
theorem nonempty_iso_kunneth {W : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) :=
  sorry

/-- Blueprint `sk-prop-sf-kunneth-ordinary`: Künneth and the projection formula in ordinary
étale cohomology

**The projection formula for a proper morphism.** For `f : X ⟶ Y` proper between finite-type
`k`-schemes and all `E ∈ D(X_ét, Λ)`, `L ∈ D(Y_ét, Λ)`, the projection map

`Rf_* E ⊗^L L ⟶ Rf_*(E ⊗^L Lf^* L)`

(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`) is an isomorphism. -/
theorem isIso_rightDerivedLowerStarProjectionMap_of_isProper (f : X ⟶ Y) [IsProper f]
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app L) :=
  sorry

end Kunneth

end Etale

end AlgebraicGeometry
