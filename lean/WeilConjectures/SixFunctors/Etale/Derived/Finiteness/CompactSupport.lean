/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Compactly supported cohomology is perfect

Compactly supported cohomology of a bounded constructible complex of finite Tor amplitude over
a separably closed field is a perfect complex of `Λ`-modules (`sk-prop-sf-trace-perfectness`).

## Implementation notes

`sk-prop-sf-trace-perfectness` concludes that `RΓ_c(X, K)` is *perfect*: bounded, with finite
cohomology modules, and of finite Tor amplitude. The three are stated separately below, finite
Tor amplitude in the sense of `DerivedCategory.finiteTorAmplitude` for `D(ModuleCat Λ)`; they
are assembled into perfectness in `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`.
The geometric-stalk half of the same subsection is omitted.

## Main statements

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
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
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
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (q : ℤ) :
    Module.Finite Λ ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Finite Tor amplitude of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, the complex of
`Λ`-modules `RΓ_c(X, K)` has finite Tor amplitude: by the projection formula
`RΓ_c(X, K) ⊗ᴸ M ≅ RΓ_c(X, K ⊗ᴸ M_X)` for a `Λ`-module `M`, and the cohomological amplitude of
`Ra_{X!}` on complexes of Tor amplitude in a fixed interval. -/
theorem finiteTorAmplitude_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    _root_.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ)
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K) :=
  sorry

end Perfectness

end Etale

end AlgebraicGeometry
