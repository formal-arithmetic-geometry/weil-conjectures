/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Künneth and the projection formula in ordinary étale cohomology

The Künneth formula and the projection formula in ordinary étale cohomology
(`sk-prop-sf-kunneth-ordinary`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kunneth`
- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerStar_of_isProper`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

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
`k`-schemes and all `E ∈ D(X_ét, Λ)`, `L ∈ D(Y_ét, Λ)`,

`Rf_* E ⊗^L L ≅ Rf_*(E ⊗^L Lf^* L)`. -/
theorem nonempty_iso_derivedTensor_rightDerivedLowerStar_of_isProper (f : X ⟶ Y) [IsProper f]
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E)).obj L ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L))) :=
  sorry

end Kunneth

end Etale

end AlgebraicGeometry
