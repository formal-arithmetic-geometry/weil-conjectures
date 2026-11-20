/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor

/-!
# Proper direct image preserves `Dctf` on the pro-étale side

Let `Λ` be a finite ring whose exponent is invertible on a finite-type `k`-scheme `Y`, and let
`p : X ⟶ Y` be a proper morphism of finite-type `k`-schemes. Then the pro-étale direct image
`Rp_* : D(X_proét, Λ) ⥤ D(Y_proét, Λ)` maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`
(`AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedLowerStar_of_isProper`, the
proper direct image with finite coefficients, on the pro-étale side). On `ν^* G` the direct
image is `ν^* Rp_*^{ét} G` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso`),
and the étale `Rp_*^{ét}` preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar_of_isProper`). This is
the proper-leg half of the argument for the compact-support functor of a compactification
(`AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-- *Proper direct image with finite coefficients*, pro-étale side: for a proper morphism
`p : X ⟶ Y` of finite-type `k`-schemes and a finite `Λ` whose exponent is invertible on `Y`,
`Rp_*` maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`. An object of `Dctf(X_proét, Λ)` is `ν^* G` with
`G` in `Dctf(X_ét, Λ)` (the comparison `ν^*` detects Tor amplitude), the direct image of `ν^* G`
is `ν^* Rp_*^{ét} G` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso`), and
`Rp_*^{ét} G` lies in `Dctf(Y_ét, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar_of_isProper`). -/
theorem constructibleFiniteTor_rightDerivedLowerStar_of_isProper {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (p : X ⟶ Y) (hp : p ≫ aY = aX) [IsProper p]
    [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj K) := by
  obtain ⟨⟨G, hG, ⟨e⟩⟩, a, b, hab⟩ := hK
  have hGt : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X G :=
    ⟨hG, a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
      ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩
  exact (DerivedCategory.constructibleFiniteTor _ Y).prop_of_iso
    ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.mapIso e.symm ≪≫
      (rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} Λ) p).app ⟨G, hG.1.1⟩).symm
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_rightDerivedLowerStar_of_isProper Λ aX aY p hp hGt))

end AlgebraicGeometry.ProEtale
