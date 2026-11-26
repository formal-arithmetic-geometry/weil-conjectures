/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Sf.SfRationalScalarExtensionHomBasisOfIntegral
import WeilConjectures.SmoothPurity.Rational.RationalScalarIntegralHomBasis

/-! # The finite free Hom formula for rational scalar extension

For a finite extension `F/E` of finite extensions of `ℚ_ℓ`, rational scalar extension
`T : D_cons(W, E) ⥤ D_cons(W, F)` satisfies `Hom_F(T N, T Z) ≅ F ⊗_E Hom_E(N, Z)`.
In basis coordinates: for an `E`-basis `v` of `F`, every morphism `T N ⟶ T Z` is uniquely
of the form `∑ i, v i • T(g i)`.

## Implementation details

The completed integer ring `𝒪_F` is finite free over `𝒪_E`. For complete integral `N`, the
completed scalar extension is the ordinary extension `𝒪_F ⊗_{𝒪_E} N`, and extension of scalars
is left adjoint to exact restriction of scalars, so
`Hom(𝒪_F ⊗ N, 𝒪_F ⊗ Z) ≅ 𝒪_F ⊗_{𝒪_E} Hom(N, Z)`
(`sfConstructibleIntegralScalarExtension_map_basis_bijective`). Tensoring with the localized
coefficient rings gives the rational formula
(`sfRationalScalarExtension_map_basis_bijective_of_integral`).

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.7.2, Proposition 6.8.14(2),
  Remark 6.8.15.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

/-- Finite free Hom formula for rational scalar extension, in basis coordinates.

Let `v` be an `E`-basis of `F` (via `ι`). For rational constructible `E`-objects `N`, `Z`,
the map `(g_i)_i ↦ ∑ i, v i • T(g i)` from `Fin d → (N ⟶ Z)` to `T N ⟶ T Z` is bijective,
where `T` is the rational scalar extension and `v i` acts through the canonical
identification of the localized coefficient ring of `F` with `F`. -/
theorem sfRationalScalarExtension_map_basis_bijective (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : AlgebraicGeometry.Scheme.{u}) (p : ℕ) (hl : l ≠ p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) {d : ℕ} (v : Fin d → F)
    (hv : ∀ x : F, ∃! c : Fin d → E, ∑ i, ι (c i) * v i = x)
    (N Z : sfRationalConstructibleCategory l E W) :
    Function.Bijective (fun g : Fin d → (N ⟶ Z) ↦
      ∑ i, (sfRationalCoefficientEquiv l F).symm (v i) •
        (sfRationalScalarExtension l E W p hl F ι).map (g i)) :=
  sfRationalScalarExtension_map_basis_bijective_of_integral l E W p hl F ι
    (sfConstructibleIntegralScalarExtension_map_basis_bijective l E F ι W p hl) v hv N Z

end WeilConjectures
