/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrobeniusDatum
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# Frobenius pullback commutes with compactly supported direct image

Let `f₀ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field `k₀`, with base change
`f : X ⟶ Y` to `k̄`, and let `D` be a purity Frobenius datum. For `M ∈ D(X_ét, Λ)`, `Λ` finite,
the base change comparison identifies

`LΦ_Y^* Rf_! M ≅ Rf_! LΦ_X^* M`

for the scheme Frobenii `Φ_X`, `Φ_Y`. This is the second isomorphism of (10.9) in blueprint
`proposition-purity-trace-commute-frobenius`.

## Main definitions

- `AlgebraicGeometry.Etale.PurityFrobeniusDatum.schemeFrobeniusLowerShriekIso`: the isomorphism
  `LΦ_Y^* Rf_! M ≅ Rf_! LΦ_X^* M`.

## Implementation notes

The square formed by `f` with the scheme Frobenii commutes but is not Cartesian (for smooth `f`
of positive relative dimension the relative Frobenius of `X` over `Y` is not an isomorphism),
so the blueprint's base change comparison is read, as everywhere in the repository, through the
Cartesian square formed by `f` with the geometric-Galois Frobenii `g_X`, `g_Y`
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`) and the
comparisons `κ : LΦ^* ≅ Lg^*` of the datum: the isomorphism is
`LΦ_Y^* Rf_! M ≅ Lg_Y^* Rf_! M ≅ Rf_! Lg_X^* M ≅ Rf_! LΦ_X^* M`, the middle one being
compact-support base change (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

namespace PurityFrobeniusDatum

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k₀ : Type u} [Field k₀] [Finite k₀]
  {X₀ Y₀ : Scheme.{u}} {aX : X₀ ⟶ Spec (.of k₀)} {aY : Y₀ ⟶ Spec (.of k₀)}
  {f₀ : X₀ ⟶ Y₀} {hf₀ : f₀ ≫ aY = aX} (D : PurityFrobeniusDatum Λ f₀ hf₀)
  [HasCompactification (Hom.geometricFiberMap f₀ hf₀)]
  [QuasiCompact (Hom.geometricFiberMap f₀ hf₀)]

/-- Blueprint `proposition-purity-trace-commute-frobenius--3`: Frobenius pullback commutes
with compactly supported direct image,

`Fr_Y^* Rf_! M ≅ Rf_! Fr_X^* M`,

for the scheme Frobenii `Fr_X = Φ_X`, `Fr_Y = Φ_Y` of a purity Frobenius datum and a finite
coefficient ring `Λ`. It is the composite
`LΦ_Y^* Rf_! M ≅ Lg_Y^* Rf_! M ≅ Rf_! Lg_X^* M ≅ Rf_! LΦ_X^* M` of the comparison `κ_Y`, the
compact-support base change `Ex_!` of the Cartesian geometric-Galois square (an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`) and the inverse of
`κ_X`. -/
noncomputable def schemeFrobeniusLowerShriekIso (M : DerivedCategoryModule Λ aX.geometricFiber) :
    (L((D.schemeFrobeniusY)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(Hom.geometricFiberMap f₀ hf₀)_![ModuleCat.{u + 1} Λ]).obj M) ≅
      (R(Hom.geometricFiberMap f₀ hf₀)_![ModuleCat.{u + 1} Λ]).obj
        ((L((D.schemeFrobeniusX)^*[ModuleCat.{u + 1} Λ])).obj M) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀)
  D.κY.app _ ≪≫
    asIso ((rightDerivedLowerShriekBaseChangeMap Λ
      (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀)).app M) ≪≫
    (R(Hom.geometricFiberMap f₀ hf₀)_![ModuleCat.{u + 1} Λ]).mapIso (D.κX.app M).symm

/-- The isomorphism `Fr_Y^* Rf_! M ≅ Rf_! Fr_X^* M` of
`AlgebraicGeometry.Etale.PurityFrobeniusDatum.schemeFrobeniusLowerShriekIso` is `κ_Y`, followed
by the compact-support base change of the geometric-Galois square and by `Rf_! κ_X⁻¹`. -/
lemma schemeFrobeniusLowerShriekIso_hom (M : DerivedCategoryModule Λ aX.geometricFiber) :
    (D.schemeFrobeniusLowerShriekIso M).hom =
      D.κY.hom.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap Λ
          (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀)).app M ≫
        (R(Hom.geometricFiberMap f₀ hf₀)_![ModuleCat.{u + 1} Λ]).map (D.κX.inv.app M) :=
  rfl

end PurityFrobeniusDatum

end Etale

end AlgebraicGeometry
