/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-!
# Bounded flat models

Finite Tor amplitude in `[a, b]` is the same as admitting a bounded flat model concentrated in
`[a, b]` (`sk-lem-sf-flat-model`).

## Main definitions

- `AlgebraicGeometry.Etale.IsBoundedFlatComplex`

## Main statements

- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`
- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- A complex `P` of sheaves of `Λ`-modules on `X_ét` is a *bounded flat complex in degrees
`[a, b]`* if every `P^q` is flat and `P^q = 0` for `q ∉ [a, b]`. -/
def IsBoundedFlatComplex (a b : ℤ)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) : Prop :=
  (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q)

/-- Blueprint `sk-lem-sf-flat-model`: Bounded flat model of finite Tor amplitude

**Finite Tor amplitude means a bounded flat model.** For `K ∈ D^b_c(X, Λ)` and integers
`a ≤ b` the following are equivalent: `K` has Tor amplitude in `[a, b]`; and `K` is isomorphic
to a bounded flat complex `P` in degrees `[a, b]`.

One direction is that a bounded-above complex of flat sheaves is K-flat; the other truncates a
bounded-above free resolution and checks that the truncation is flat by the Tor criterion. -/
theorem hasTorAmplitudeIn_iff_exists_flatModel (a b : ℤ) (hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        IsBoundedFlatComplex Λ a b P ∧ Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) :=
  sorry

/-- Blueprint `sk-lem-sf-flat-model`: Bounded flat model of finite Tor amplitude

**Constructible variant.** Let `X` be Noetherian and `Λ` finite. For `K ∈ D^b_c(X, Λ)` and
integers `a ≤ b`, `K` has Tor amplitude in `[a, b]` if and only if it is isomorphic to a bounded
flat complex `P` in degrees `[a, b]` whose terms are *constructible*. In particular every object
of `Dctf(X, Λ)` has such a model.

The bounded-above resolution of `hasTorAmplitudeIn_iff_exists_flatModel` is built with terms
finite sums of sheaves `j_{V!} Λ_V`, by `Scheme.exists_epi_sigma_lowerShriek_constantSheaf`
applied to the constructible cohomology sheaves of `K` and to the constructible kernels and
cokernels that arise (`Scheme.IsConstructibleSheaf.kernel`,
`Scheme.IsConstructibleSheaf.cokernel`); its truncation in degree `a` is then a cokernel of a
map of constructible sheaves, hence flat and constructible. The converse is the corresponding
direction of `hasTorAmplitudeIn_iff_exists_flatModel`. The statement is made for a finite ring
`Λ`, as in the blueprint. -/
theorem hasTorAmplitudeIn_iff_exists_flatConstructibleModel [Finite Λ] [IsNoetherian X]
    (a b : ℤ) (hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        IsBoundedFlatComplex Λ a b P ∧ (∀ q : ℤ, IsConstructibleSheaf (P.X q)) ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) :=
  sorry

end Etale

end AlgebraicGeometry
