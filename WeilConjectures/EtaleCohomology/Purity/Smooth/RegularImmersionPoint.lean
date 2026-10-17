/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The fundamental class of a rational point

Let `a : X ⟶ Spec k` be smooth and proper of pure relative dimension `d` and `x : Spec k ⟶ X` a
`k`-point, a regular closed immersion of codimension `d` with `x ≫ a = 𝟙`. Part (c) of
`sk-thm-regular` identifies the fundamental class `[x ⊂ X] ∈ H^{2d}_x(X, Λ(d))` with the
isomorphism `Φ_x : Λ ≅ Rx^! Λ_X(d)[2d]` assembled from the smooth purity orientations of `a`
and of `a ∘ x = 𝟙` through the composition law `Rx^! Ra^! ≅ R(a ∘ x)^!`. Transported along the
orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ` of `a`, the class `[x ⊂ X]` is therefore the class
`1 ∈ Λ = H^0(Spec k, Rx^! Ra^! Λ)`.

## Main statements

- `AlgebraicGeometry.Etale.exists_dualizingComplexIso_fundamentalClass_point`: there is an
  orientation `γ` of `a` such that, for every `k`-point `x`, the class `[x ⊂ X]` transported along
  `γ` is `1 ∈ H^0(Spec k, Rx^! Ra^! Λ)`.

## Implementation notes

The repository has smooth purity, the composition law of `R^!` and `R(𝟙)_! ≅ 𝟭` only as the
existence of isomorphisms (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`), so `Φ_x` cannot be
written down. The statement therefore reads `1 ∈ H^0(Spec k, Rx^! Ra^! Λ)` through the composite
adjunction `Ra_! Rx_! ⊣ Rx^! Ra^!` and the identification `Λ ≅ Ra_! Rx_! Λ` given by the units
of the pullback-pushforward adjunctions (`Ra_! ≅ Ra_*` for the proper `a`): the class `c` is `1`
when the composite
```
Λ ──unit──▶ Ra_* La^* Λ = Ra_* Λ_X ──Ra_*(c)──▶ Ra_* Rx_! Rx^! Ra^! Λ ≅ Ra_! Rx_! Rx^! Ra^! Λ ──▶ Λ
```
with the counit of the composite adjunction is the identity. The orientation is the one of
`sk-thm-smooth-purity`, which is only known to exist, so the statement is existential in it.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] [PerfectField k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [HasInvertibleExponent Λ X] {d : ℕ}
  (a : X ⟶ Spec (.of k)) [IsProper a] [SmoothOfRelativeDimension d a]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(c) for rational points.** Let `a : X ⟶ Spec k` be smooth and proper of pure relative
dimension `d`. For the orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ` of `sk-thm-smooth-purity` and every
`k`-point `x : Spec k ⟶ X` (a regular closed immersion of codimension `d` with `x ≫ a = 𝟙`),
the fundamental class `[x ⊂ X] = cl_x(1)` equals `Φ_x(1)`, where `Φ_x` is assembled from the
orientations of `a` and of `a ∘ x = 𝟙` through `Rx^! Ra^! ≅ R(a ∘ x)^!`. Transported along `γ`,
`[x ⊂ X]` is thus `1 ∈ H^0(Spec k, Rx^! Ra^! Λ)`; this is stated through the composite
adjunction `Ra_! Rx_! ⊣ Rx^! Ra^!` and the identification `Λ ≅ Ra_! Rx_! Λ` given by the units
of `La^* ⊣ Ra_*` (see the module docstring). -/
theorem exists_dualizingComplexIso_fundamentalClass_point :
    haveI := SmoothOfRelativeDimension.smooth d a
    ∃ γ : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a,
      ∀ (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x], x ≫ a = 𝟙 _ →
        (derivedUpperStarLowerStarAdjunction _ a).unit.app
            (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) ≫
          (R((a)_*[ModuleCat.{u + 1} Λ])).map ((leftDerivedUpperStarConstantComplexIso Λ a).hom ≫
            fundamentalClass Λ d x a IsRegular.isRegularLocalRing_stalk ≫
              (R(x)_![ModuleCat.{u + 1} Λ]).map ((R(x)^![ModuleCat.{u + 1} Λ]).map γ.hom)) ≫
          (rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).inv.app _ ≫
          ((rightDerivedUpperShriekAdjunction _ x).comp
            (rightDerivedUpperShriekAdjunction _ a)).counit.app
              (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) = 𝟙 _ :=
  -- TODO: needs the canonical orientations of `sk-thm-smooth-purity` (of `a` and of `𝟙`), the
  -- composition law `Rx^! Ra^! ≅ R(a ∘ x)^!` as the mate of `Ra_! Rx_! ≅ R(a ∘ x)_!`, and Steps
  -- 1–2 of the proof of `sk-thm-regular` comparing `Φ_x` with the frame classes.
  sorry

end Etale

end AlgebraicGeometry
