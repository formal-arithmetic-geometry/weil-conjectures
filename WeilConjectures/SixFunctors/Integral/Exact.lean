/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Exactness of the direct image along an integral morphism

For an integral morphism `f : X ⟶ Y` the pushforward `f_*` on étale sheaves of `Λ`-modules is
exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`), and it
detects the zero sheaf (`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj`). Together these
make `f_*` conservative (`AlgebraicGeometry.Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom`).

The finite case of the exactness is
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`, proved through the
stalk formula `AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`. For an integral morphism the
geometric fibres need no longer be finite and the stalk of `f_* G` at a geometric point is
instead the sections of `G` over the integral base change of the strict henselisation, a
filtered colimit of finite products of stalks; that formula is not available yet.

## Main statements

- `AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`: the direct
  image along an integral morphism is exact.
- `AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj`: the direct image along an
  integral morphism detects the zero sheaf.
- `AlgebraicGeometry.Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom`: the direct
  image along an integral morphism is conservative.

## References

- Stacks Project, Lemma 59.43.5, <https://stacks.math.columbia.edu/tag/04C2>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- Blueprint `sbc-lem-integral-etale-direct-image-exact`: Étale direct image is exact for
integral morphisms.

The direct image `f_*` along an integral morphism `f` is exact on étale sheaves of
`Λ`-modules: it is left exact for every morphism, and it preserves finite colimits. The
blueprint records this as a classical input (Stacks 04C2) and gives no separate proof beyond
the finite case `AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`. -/
@[stacks 04C2]
theorem Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom :
    PreservesFiniteColimits (f)_*[ModuleCat.{u + 1} Λ] :=
  sorry

/-- The direct image along an integral morphism detects the zero sheaf: if `f_* G = 0` then
`G = 0`. This is the conservativity step of the proof of blueprint `sbc-lem-bc-integral-base`.
For a geometric point `x` of `X` over the geometric point `y` of `Y`, the stalk `G_x` is a
colimit of factors of the sections of `G` over the integral base change of the strict
henselisation at `y`, which is the stalk `(f_* G)_y`; so `G_x` is a quotient of `(f_* G)_y`. -/
theorem Etale.isZero_of_isZero_lowerStar_obj
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hG : IsZero ((f)_*[ModuleCat.{u + 1} Λ].obj G)) : IsZero G :=
  sorry

/-- The direct image along an integral morphism is conservative: being exact by
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`, it sends the
kernel and the cokernel of a morphism to those of its image, and it detects their vanishing by
`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj`. -/
theorem Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom :
    (f)_*[ModuleCat.{u + 1} Λ].ReflectsIsomorphisms where
  reflects {G G'} φ _ := by
    have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ f
    have : Mono φ := Preadditive.mono_of_isZero_kernel φ <|
      Etale.isZero_of_isZero_lowerStar_obj Λ f <|
      (isZero_kernel_of_mono ((f)_*[ModuleCat.{u + 1} Λ].map φ)).of_iso
        (PreservesKernel.iso _ φ)
    have : Epi φ := Preadditive.epi_of_isZero_cokernel φ <|
      Etale.isZero_of_isZero_lowerStar_obj Λ f <|
      (isZero_cokernel_of_epi ((f)_*[ModuleCat.{u + 1} Λ].map φ)).of_iso
        (PreservesCokernel.iso _ φ)
    exact isIso_of_mono_of_epi φ

end AlgebraicGeometry
