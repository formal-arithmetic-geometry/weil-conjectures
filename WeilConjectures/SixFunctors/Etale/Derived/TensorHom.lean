/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# The tensor–Hom exchange and the Verdier-duality exchange

Let `f : X ⟶ Y` be a morphism of schemes admitting a compactification, so that the pair
`Rf_! ⊣ Rf^!` is available. The *tensor–Hom form of the exchange* is the isomorphism

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`,

natural in `M` and `N`. It is the Yoneda consequence of the three adjunctions `Lf^* ⊣ Rf_*`,
`Rf_! ⊣ Rf^!` and `- ⊗ᴸ - ⊣ RHom`, together with the projection formula.

Specialising it to `N = ω_Y` and using `Rf^! ω_Y ≅ ω_X` gives the *Verdier-duality exchange*
`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`: the Verdier dual intertwines `Rf_!` and `Rf_*`. Note that this
route to the exchange goes through the tensor–Hom statement only, and so does not depend on
the duality theory itself.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`
  (`sk-thm-sf-tensor-hom`): `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`
  (`sk-thm-sf-verdier-exchange`): `Rf^! ω_Y ≅ ω_X`.
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek`
  (`sk-thm-sf-verdier-exchange`): `𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

section TensorHom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-thm-sf-tensor-hom`: Tensor–Hom form of the exchange.

For a morphism `f : X ⟶ Y` carrying the ambient datum — here, admitting a compactification,
so that `Rf_!` and its right adjoint `Rf^!` exist — and for `M` in `Dctf(X, A)` and `N` in
`Dctf(Y, A)`, the direct image of the internal hom from `M` into `Rf^! N` agrees with the
internal hom on `Y` from `Rf_! M` into `N`:

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`.

The isomorphism is natural in `M` and `N` and compatible with finite reduction, scalar
extension and shifts. It is obtained by Yoneda from the chain of adjunctions
`Rf_! ⊣ Rf^!`, `Lf^* ⊣ Rf_*` and `- ⊗ᴸ - ⊣ RHom`, the inverse of the projection formula
supplying the passage `Rf_! M ⊗ᴸ L ≅ Rf_! (M ⊗ᴸ Lf^* L)`. -/
theorem nonempty_iso_derivedHom_rightDerivedLowerShriek
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : DerivedCategory.boundedConstructible A X M ∧ DerivedCategory.finiteTorAmplitude A X M)
    (hN : DerivedCategory.boundedConstructible A Y N ∧ DerivedCategory.finiteTorAmplitude A Y N) :
    Nonempty ((R((f)_*[A])).obj ((RHom(X)[A].obj (op M)).obj ((R(f)^![A]).obj N)) ≅
      (RHom(Y)[A].obj (op ((R(f)_![A]).obj M))).obj N) :=
  sorry

end TensorHom

section VerdierExchange

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S) [HasCompactification f]
  [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `sk-thm-sf-verdier-exchange`: Verdier-duality exchange.

First half. If `f : X ⟶ Y` and the structure morphism `a_Y : Y ⟶ S` both carry the ambient
datum, then so does `a_X = f ≫ a_Y`, and the exceptional inverse image along `f` of the
dualizing complex of `Y` is the dualizing complex of `X`:

`Rf^! ω_Y ≅ ω_X`.

This is the mate, under the adjunctions `Rf_! ⊣ Rf^!`, of the composition isomorphism
`R(a_Y ∘ f)_! ≅ R a_{Y!} ∘ Rf_!`, evaluated at the monoidal unit `Λ_S`. -/
theorem nonempty_iso_rightDerivedUpperShriek_dualizingComplex :
    Nonempty ((R(f)^![A]).obj (dualizingComplex A aY) ≅ dualizingComplex A (f ≫ aY)) :=
  sorry

/-- Blueprint `sk-thm-sf-verdier-exchange`: Verdier-duality exchange.

Second half. With `a_Y : Y ⟶ S` the structure morphism of `Y` and `a_X = f ≫ a_Y` that of
`X`, the Verdier duals `𝔻_Y = RHom_Y(-, ω_Y)` and `𝔻_X = RHom_X(-, ω_X)` exchange the
extraordinary and the ordinary direct image: for `M` in `Dctf(X, A)`,

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`,

naturally in `M` and compatibly with finite reduction, scalar extension and shifts. It is
the tensor–Hom exchange `nonempty_iso_derivedHom_rightDerivedLowerShriek` at `N = ω_Y`,
combined with `Rf^! ω_Y ≅ ω_X`. -/
theorem nonempty_iso_verdierDual_rightDerivedLowerShriek
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hM : DerivedCategory.boundedConstructible A X M ∧ DerivedCategory.finiteTorAmplitude A X M) :
    Nonempty ((verdierDual A aY).obj (op ((R(f)_![A]).obj M)) ≅
      (R((f)_*[A])).obj ((verdierDual A (f ≫ aY)).obj (op M))) :=
  sorry

end VerdierExchange

end Etale

end AlgebraicGeometry
