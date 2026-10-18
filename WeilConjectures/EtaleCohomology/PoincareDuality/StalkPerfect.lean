/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Geometric stalks of `Dctf` complexes are perfect

Let `Λ` be a finite ring, `k` a separably closed field in which the exponent of `Λ` is
invertible, and `x : Spec k ⟶ X` a geometric point of a scheme `X`. For `K ∈ Dctf(X, Λ)`, the
geometric stalk `K_x = RΓ(Spec k, Lx^* K)` is a perfect complex of `Λ`-modules. This is the
stalk half of blueprint `sk-prop-sf-trace-perfectness`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfect_geometricStalk`: `RΓ(Spec k, Lx^* K)` is perfect.

## Implementation notes

The pullback `Lx^* K` lies in `Dctf(Spec k, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_leftDerivedUpperStar`), and `RΓ(Spec k, -)`
of such a complex is perfect by
`AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections` applied to the identity of
`Spec k`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

/-- Blueprint `sk-prop-sf-trace-perfectness` (stalk half): geometric stalks of `Dctf` complexes
are perfect.

For a finite ring `Λ` whose exponent is invertible in the separably closed field `k`, a
geometric point `x : Spec k ⟶ X` and `K ∈ Dctf(X, Λ)`, the geometric stalk
`RΓ(Spec k, Lx^* K)` is a perfect complex of `Λ`-modules. -/
theorem isPerfect_geometricStalk (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u}
    [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
      ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K)).IsPerfect :=
  isPerfect_rightDerivedGlobalSections Λ (𝟙 (Spec (.of k))) _
    (constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) x hK)

end Etale

end AlgebraicGeometry
