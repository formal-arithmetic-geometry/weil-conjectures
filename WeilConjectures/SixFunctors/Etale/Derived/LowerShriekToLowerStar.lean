/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# The derived comparison from extension by zero to pushforward

For an open immersion `j` the derived extension by zero `D(j_!)` maps to the derived
pushforward `Rj_*`; composing with the proper pushforward of a compactification `(i, g)` of
`f` gives the *forget-supports* map

`Rf_! = Rg_* D(i_!) ⟶ Rg_* Ri_*`,

whose target is right adjoint to `Li^* Lg^*`. For a closed immersion `f` this is how a class
`K ⟶ Rf_! N` is transposed into a morphism `Lf^* K ⟶ N`: a closed immersion is proper, the
comparison is then an isomorphism, and the transposition is the adjunction `Lf^* ⊣ Rf_*`.

The comparison for an open immersion is the transpose, under `D(j^*) ⊣ Rj_*`, of the inverse
of the unit `K ⟶ D(j^*) D(j_!) K`, which is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit`).

## Main definitions

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar`
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekTranspose`

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isClosedImmersion`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived comparison `D(j_!) ⟶ Rj_*` along an open immersion `j`: the transpose, under
`D(j^*) ⊣ Rj_*`, of the inverse of the unit `K ⟶ D(j^*) D(j_!) K` of `D(j_!) ⊣ D(j^*)`. It is
the derived counterpart of the comparison `j_! ⟶ j_*` of sheaves. Componentwise it is the
composite

```
          η_{D(j_!) K}                         Rj_* (η'_K)⁻¹
D(j_!) K ─────────────▶ Rj_* D(j^*) D(j_!) K ───────────────▶ Rj_* K
```

of the unit `η` of `D(j^*) ⊣ Rj_*` and the inverse of the unit `η'` of `D(j_!) ⊣ D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : D((j)_!open[A]) ⟶ R((j)_*[A]) :=
  Functor.whiskerLeft D((j)_!open[A]) (mapDerivedUpperStarLowerStarAdjunction A j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (inv (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit)
        R((j)_*[A])

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The *forget-supports* map `Rf_! ⟶ Rg_* Ri_*` for the chosen compactification `(i, g)` of
`f`: the proper pushforward `Rg_*` applied to the comparison `D(i_!) ⟶ Ri_*` of the open
immersion `i`. Its target is right adjoint to `Li^* Lg^* = Lf^*`. -/
noncomputable def rightDerivedLowerShriekToLowerStarComp :
    R(f)_![A] ⟶ R(((HasCompactification.compactification f).i)_*[A]) ⋙
      R(((HasCompactification.compactification f).g)_*[A]) :=
  Functor.whiskerRight (derivedOpenImmersionLowerShriekToLowerStar A _) _

/-- For a closed immersion `f` the forget-supports map `Rf_! ⟶ Rg_* Ri_*` is an isomorphism.
The open immersion `i : X ⟶ X̄` of the chosen compactification is then also closed, since `X`
is proper over `Y` and `X̄` is separated over `Y`, so `X` is open and closed in `X̄` and the
comparison `D(i_!) ⟶ Ri_*` is an isomorphism. -/
theorem isIso_rightDerivedLowerShriekToLowerStarComp_of_isClosedImmersion [IsClosedImmersion f] :
    IsIso (rightDerivedLowerShriekToLowerStarComp A f) :=
  sorry

/-- The *transpose* of a class `γ : K ⟶ Rf_! N` along the forget-supports map: the morphism
`Li^* Lg^* K ⟶ N` adjoint, under `Li^* Lg^* ⊣ Rg_* Ri_*`, to
`K ⟶ Rf_! N ⟶ Rg_* Ri_* N`, where `(i, g)` is the chosen compactification of `f`.

For a closed immersion `f` the forget-supports map is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isClosedImmersion`)
and this is the adjunction `Lf^* ⊣ Rf_*`, transported along `Rf_! ≅ Rf_*`. -/
noncomputable def rightDerivedLowerShriekTranspose
    {K : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {N : DerivedCategory (Sheaf X.smallEtaleTopology A)} (γ : K ⟶ (R(f)_![A]).obj N) :
    (L(((HasCompactification.compactification f).i)^*[A])).obj
        ((L(((HasCompactification.compactification f).g)^*[A])).obj K) ⟶ N :=
  (((derivedUpperStarLowerStarAdjunction A _).comp
    (derivedUpperStarLowerStarAdjunction A _)).homEquiv _ _).symm
      (γ ≫ (rightDerivedLowerShriekToLowerStarComp A f).app N)

end Etale

end AlgebraicGeometry
