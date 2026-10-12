/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SepClosedPoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# Compactly supported cohomology is perfect

Compactly supported cohomology of a bounded constructible complex of finite Tor amplitude over
a separably closed field is a perfect complex of `Λ`-modules, and so are the derived geometric
stalks of such a complex (`sk-prop-sf-trace-perfectness`, `prop-trf-compact-support-perfectness`).

## Implementation notes

`sk-prop-sf-trace-perfectness` concludes that `RΓ_c(X, K)` is *perfect*: bounded, with finite
cohomology modules, and of finite Tor amplitude. The proof follows the blueprint in a slightly
different order: `Ra_{X!}` carries `Dctf(X, Λ)` into `Dctf(Spec k, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek`, the clause (iv) of
`sk-thm-sf-ctf-stability`, whose Tor amplitude bound is the cohomological dimension input of the
blueprint proof), and on the separably closed point `Spec k` the derived global sections
`RΓ(Spec k, -)` are a monoidal equivalence `D(Spec k_ét, Λ) ≌ D(Λ)` which carries
`Dctf(Spec k, Λ)` into the perfect complexes
(`AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections_of_isSepClosed`). The geometric
stalk `L x̄^* K` is handled the same way, `Lx̄^*` preserving `Dctf`.

The three ingredients of perfectness of `RΓ_c(X, K)` are also stated separately, finite Tor
amplitude in the sense of `DerivedCategory.finiteTorAmplitude` for `D(ModuleCat Λ)`.

"Separated of finite type over `k`" is spelled `[HasCompactification aX]`, which supplies
`IsSeparated aX` and `LocallyOfFiniteType aX`; quasi-compactness follows
(`AlgebraicGeometry.Etale.quasiCompact_of_hasCompactification`).

## Main statements

- `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_of_isSepClosed`
- `AlgebraicGeometry.Etale.isPerfect_geometricStalk`
- `AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`
- `AlgebraicGeometry.Etale.finite_compactlySupportedCohomology`
- `AlgebraicGeometry.Etale.finiteTorAmplitude_compactlySupportedGlobalSections`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- A zero object of `D(X_ét, Λ)` lies in `Dctf(X, Λ)`. -/
lemma constructibleFiniteTor_of_isZero
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsZero K) : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K :=
  ⟨boundedConstructible_of_isZero Λ hK, 0, 0,
    _root_.DerivedCategory.torAmplitudeIn_of_isZero 0 0 hK⟩

section Perfectness

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) [HasCompactification aX]
  [HasInvertibleExponent Λ X]

omit [IsSepClosed k] [HasInvertibleExponent Λ X] in
include aX in
/-- A scheme admitting a compactification over a field is quasi-compact over it: it is an open
subscheme of a proper, hence Noetherian, scheme. -/
lemma quasiCompact_of_hasCompactification : QuasiCompact aX := by
  let c := HasCompactification.compactification aX
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ 𝟙 _) }
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 inferInstance

omit [IsSepClosed k] in
/-- In the situation of `sk-prop-sf-trace-perfectness`, `Ra_{X!} K` lies in
`Dctf(Spec k, Λ)`. -/
lemma constructibleFiniteTor_rightDerivedLowerShriek_of_isSepClosed
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
    exact constructibleFiniteTor_of_isZero Λ
      ((R(aX)_![ModuleCat.{u + 1} Λ]).map_isZero (isZero_derivedCategory_of_isEmpty _ X K))
  | inr hX =>
    have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
    have := quasiCompact_of_hasCompactification aX
    exact constructibleFiniteTor_rightDerivedLowerShriek Λ (𝟙 _) aX hK

/-- Blueprint `prop-trf-compact-support-perfectness`: Compact-support perfectness (compactly
supported cohomology).

Also blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks.

Let `Λ` be a finite coefficient ring whose exponent is invertible on `X` (for instance
`Λ = A_{E,n}`), `k` separably closed, `X` separated of finite type over `k` with structure
morphism `a_X`, and `K ∈ D^b_{ctf}(X, Λ)`. Then `RΓ_c(X, K) = RΓ(Spec k, Ra_{X!} K)` is a perfect
complex of `Λ`-modules: `Ra_{X!} K ∈ Dctf(Spec k, Λ)`, and `RΓ(Spec k, -)` carries
`Dctf(Spec k, Λ)` into perfect complexes. -/
theorem isPerfect_compactlySupportedGlobalSections_of_isSepClosed
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect :=
  isPerfect_rightDerivedGlobalSections_of_isSepClosed _
    (constructibleFiniteTor_rightDerivedLowerShriek_of_isSepClosed Λ aX K hK)

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Boundedness of compactly supported cohomology.** Let `Λ` be a finite coefficient ring, `k`
separably closed, `X` separated of finite type over `k` with structure morphism `a_X`, and
`K ∈ D^b_{ctf}(X, Λ)`. Then `RΓ_c(X, K) = Ra_{X!} K` vanishes in all but finitely many
degrees. Separable closedness of the base is essential: over `Spec ℚ` already
`H¹_c(Spec ℚ, ℤ/n) = Hom(G_ℚ, ℤ/n)` is infinite. -/
theorem isZero_compactlySupportedCohomology_of_lt
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) := by
  obtain ⟨a, b, ha, hb⟩ :=
    (isPerfect_compactlySupportedGlobalSections_of_isSepClosed Λ aX K
      hK).exists_homologyConcentratedIn
  refine ⟨a, b, fun q hq ↦ ?_⟩
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha q hq
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb q hq

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Finiteness of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, every compactly supported
cohomology module `H^q_c(X, K)` is a finite `Λ`-module. Together with boundedness and finite
Tor amplitude these are exactly perfectness over the Artinian local ring `A_{E,n}`. -/
theorem finite_compactlySupportedCohomology
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (q : ℤ) :
    Module.Finite Λ ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) :=
  (isPerfect_compactlySupportedGlobalSections_of_isSepClosed Λ aX K hK).finite_homology q

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Finite Tor amplitude of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, the complex of
`Λ`-modules `RΓ_c(X, K)` has finite Tor amplitude: `Ra_{X!} K` has finite Tor amplitude on
`Spec k` (`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek`), and
`RΓ(Spec k, -)` is a monoidal equivalence. -/
theorem finiteTorAmplitude_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    _root_.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ)
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K) := by
  obtain ⟨-, a, b, hta⟩ := constructibleFiniteTor_rightDerivedLowerShriek_of_isSepClosed Λ aX K hK
  exact ⟨a, b, torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed _ hta⟩

end Perfectness

section Stalk

variable [Finite Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Blueprint `prop-trf-compact-support-perfectness`: Compact-support perfectness (geometric
stalks).

Also blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks.

For a finite coefficient ring `Λ`, `K ∈ D^b_{ctf}(X, Λ)` and a geometric point
`x̄ : Spec Ω ⟶ X` (`Ω` separably closed), the derived geometric stalk
`K_x̄ = RΓ(Spec Ω, Lx̄^* K)` is a perfect complex of `Λ`-modules: `Lx̄^*` preserves `Dctf`, and
`RΓ(Spec Ω, -)` carries `Dctf(Spec Ω, Λ)` into perfect complexes. -/
theorem isPerfect_geometricStalk (x : Spec (.of Ω) ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
      ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K)).IsPerfect :=
  isPerfect_rightDerivedGlobalSections_of_isSepClosed _
    (constructibleFiniteTor_leftDerivedUpperStar _ x hK)

end Stalk

end Etale

end AlgebraicGeometry
