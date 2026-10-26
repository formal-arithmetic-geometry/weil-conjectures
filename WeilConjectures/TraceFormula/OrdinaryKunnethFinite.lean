/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.TraceFormula.Product

/-!
# Vanishing on the boundary for the ordinary Künneth formula, finite coefficients

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and `X`, `Y`, `U`, `Z`
separated `k`-schemes of finite type. For a morphism `f : U ⟶ Y`, a morphism `i : Z ⟶ X`, a
complex `M ∈ D(X_ét, Λ)` with `Li^* M = 0` and any `G ∈ D(U_ét, Λ)`, the complex
`R(𝟙 × f)_* (Lp_X^* M ⊗ᴸ Lp_U^* G)` vanishes on `Z ⨯ Y`
(`AlgebraicGeometry.Etale.isZero_upperStar_prodMap_lowerStar_prodMap_tensor`).

By the base change theorem for a pushforward tensored with a complex (blueprint `lem-kun-0f1n`,
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`) for the cartesian squares
```
X <--p_X-- X ⨯ Y <--(𝟙 × f)-- X ⨯ U
|            |                  |
v            v p_Y              v p_U
Spec k <---- Y <------f-------- U
```
the complex is `Lp_X^* M ⊗ᴸ Lp_Y^* Rf_* G` (the ordinary Künneth formula, blueprint
`lem-trf-ordinary-kunneth`), and its pullback to `Z ⨯ Y` is `Lp_Z^* Li^* M ⊗ᴸ (…) = 0`.

This is the finite-coefficient stage of the boundary vanishing
`ProEtale.CondensedRing.isZero_upperStar_lowerStar_externalProduct_lowerShriek`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y U Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]

/-- **Vanishing on the boundary, finite coefficients**: for morphisms `f : U ⟶ Y` and
`i : Z ⟶ X` of `k`-schemes of finite type, `M ∈ D(X_ét, Λ)` with `Li^* M = 0` and
`G ∈ D(U_ét, Λ)`, the pullback to `Z ⨯ Y` of `R(𝟙 × f)_* (Lp_X^* M ⊗ᴸ Lp_U^* G)` vanishes.
By the ordinary Künneth formula (blueprint `lem-trf-ordinary-kunneth`, through
`isIso_tensorBaseChangeMap`, blueprint `lem-kun-0f1n`) the complex is
`Lp_X^* M ⊗ᴸ Lp_Y^* Rf_* G`, whose pullback to `Z ⨯ Y` is `Lp_Z^* Li^* M ⊗ᴸ (…) = 0`. -/
theorem isZero_upperStar_prodMap_lowerStar_prodMap_tensor (f : U ⟶ Y) (i : Z ⟶ X)
    (M : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : IsZero (L((i.left)^*[ModuleCat.{u + 1} Λ]).obj M))
    (G : DerivedCategory (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero (L(((prod.map i (𝟙 Y)).left)^*[ModuleCat.{u + 1} Λ]).obj
      (R(((prod.map (𝟙 X) f).left)_*[ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-((X ⨯ U).left)[ModuleCat.{u + 1} Λ]).obj
          (L(((prod.fst : X ⨯ U ⟶ X).left)^*[ModuleCat.{u + 1} Λ]).obj M)).obj
          (L(((prod.snd : X ⨯ U ⟶ U).left)^*[ModuleCat.{u + 1} Λ]).obj G)))) :=
  sorry

end AlgebraicGeometry.Etale
