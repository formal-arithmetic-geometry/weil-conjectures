/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-!
# Higher direct images and limits of affine étale schemes

A morphism `π : O ⟶ W` is a *limit of affine étale schemes* over `W` if `O` is the limit of a
cofiltered diagram of affine schemes `W_j` étale over `W` (`Scheme.Hom.IsEtaleAffineLimit`).
Higher direct images commute with base change along such a morphism: for a quasi-compact
quasi-separated `g : U ⟶ W` with base change `g' : U' ⟶ O`,

`π^* R^q g_* ℤ/ℓ ≅ R^q g'_* ℤ/ℓ`.

This is the limit theorem for base change maps
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall`, Stacks 0EZT) applied
to the base changes of `g` to the `W_j`, for which base change holds because `W_j ⟶ W` is étale
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale`).

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.IsEtaleAffineLimit`

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_upperStar_higherDirectImage_of_isEtaleAffineLimit`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

/-- `π : O ⟶ W` is a *limit of affine étale schemes over `W`*: there is a cofiltered diagram
`E` of affine schemes with étale morphisms `b_j : E_j ⟶ W` compatible with the transition maps,
and a limit cone of `E` with point `O` whose legs followed by the `b_j` are `π`. -/
def Scheme.Hom.IsEtaleAffineLimit {O W : Scheme.{u}} (π : O ⟶ W) : Prop :=
  ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (E : J ⥤ Scheme.{u})
    (b : E ⟶ (Functor.const J).obj W) (c : Cone E) (_ : IsLimit c) (e : c.pt ≅ O),
    (∀ j, AlgebraicGeometry.Etale (b.app j)) ∧ (∀ j, IsAffine (E.obj j)) ∧
      ∀ j, e.inv ≫ c.π.app j ≫ b.app j = π

/-- A limit of affine étale schemes stays one after base change along an affine morphism. -/
theorem Scheme.Hom.IsEtaleAffineLimit.of_isPullback {O W O' W' : Scheme.{u}} {π : O ⟶ W}
    (hπ : π.IsEtaleAffineLimit) (f : W' ⟶ W) [IsAffineHom f] (π' : O' ⟶ W') (f' : O' ⟶ O)
    (sq : IsPullback f' π' π f) : π'.IsEtaleAffineLimit := by
  sorry

namespace Etale

/-- **Base change along a limit of affine étale schemes.** Let `π : O ⟶ W` be a limit of affine
étale schemes over an affine scheme `W`, `g : U ⟶ W` quasi-compact and quasi-separated and
`g' : U' ⟶ O` its base change along `π`. For a prime `ℓ` invertible on `W`,

`π^* R^q g_* ℤ/ℓ ≅ R^q g'_* ℤ/ℓ`. -/
theorem nonempty_iso_upperStar_higherDirectImage_of_isEtaleAffineLimit {O W : Scheme.{u}}
    [IsAffine W] (π : O ⟶ W) (hπ : π.IsEtaleAffineLimit) {U U' : Scheme.{u}} (g : U ⟶ W)
    [QuasiCompact g] [QuasiSeparated g] (e : U' ⟶ U) (g' : U' ⟶ O)
    (sq : IsPullback e g' g π) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(W, ⊤))) (q : ℕ) :
    Nonempty ((π)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
        (Etale.higherDirectImage (ZModCoeff.{u} ℓ) g q (constantZModModule U ℓ)) ≅
      Etale.higherDirectImage (ZModCoeff.{u} ℓ) g' q (constantZModModule U' ℓ)) := by
  sorry

end Etale

end AlgebraicGeometry
