/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!

# Orientations and the dual of a perfect complex

Let `A` be a monoidal Grothendieck abelian coefficient category. For a smooth separated
morphism `f : X ⟶ Y` of finite type and of pure relative dimension `d`, *smooth purity*
provides a canonical isomorphism `Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`. Its proof belongs to a
different blueprint block and is not formalised here; what is recorded in this file is the
interface it produces, packaged as a structure `AlgebraicGeometry.Etale.Orientation`, together
with the two consequences the six-functor formalism uses: for the structure morphism `a : X ⟶ S`
an orientation reads `ω_X ≅ Λ_X(d)[2d]`, and substituting that into `𝔻_X = RHom(-, ω_X)` turns
the Verdier dual of a perfect complex into its coefficient dual, twisted and shifted.

## Main definitions

- `AlgebraicGeometry.Etale.Orientation`: the interface record of an orientation of relative
  dimension `d`, namely a Tate twist together with `Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`.
- `AlgebraicGeometry.Etale.Orientation.dualizingComplexIso`: for the structure morphism, the
  isomorphism `Λ_X(d)[2d] ≅ ω_X` of an orientation.
- `AlgebraicGeometry.Etale.Orientation.ofDualizingComplexIso`: the orientation given by an
  isomorphism `T[2d] ≅ ω_X` with `T` invertible.

## Main statements

- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`
  (`sk-def-sf-orientation`): for the structure morphism the orientation reads
  `ω_X ≅ Λ_X(d)[2d]`.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`
  (`sk-thm-sf-dual-perfect`): `𝔻_X K ≅ K^∨(d)[2d]` for a perfect `K`.
- `AlgebraicGeometry.Etale.Orientation.isDualizable_verdierDual`
  (`sk-thm-sf-dual-perfect`): `𝔻_X` preserves the perfect objects.

## Implementation notes

As elsewhere in this folder a Tate twist `Λ_X(d)` is not constructed but carried as a datum: it
is an invertible object of `D(X_ét)` in the sense of `CategoryTheory.IsInvertible`, and
perfectness is `CategoryTheory.IsDualizable`; see the implementation note of
`WeilConjectures.SixFunctors.Etale.Derived.Perfect`.

`Orientation.nonempty_iso_dualizingComplex` is not blueprint content: it is `o.purity`
transported along `Lf^* Λ_S ≅ Λ_X` (`AlgebraicGeometry.Etale.Orientation.dualizingComplexIso`).
Conversely an isomorphism `T⟦2d⟧ ≅ ω_X` with `T` invertible is an orientation
(`AlgebraicGeometry.Etale.Orientation.ofDualizingComplexIso`).

Biduality of the Verdier dual on `Dctf(X, A)` is *not* restated here: it is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual` of
`WeilConjectures.SixFunctors.Etale.Derived.Dualizing`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-def-sf-orientation`: Orientation: an interface record.

An *orientation* of relative dimension `d` for a smooth separated morphism `f : X ⟶ Y` of
finite type is a Tate twist `Λ_X(d)` — an invertible object of `D(X_ét)` — together with an
isomorphism `γ : Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`.

In the blueprint an orientation is **not** an assumption: it is the smooth purity theorem
`sk-thm-smooth-purity`, which lives in a different blueprint block and is not formalised here.
This structure therefore records only the interface that purity produces and that the six
operations consume; the blueprint's naturality in `Y` and its compatibilities with composition,
étale base change, finite reduction, scalar extension and the pro-étale realization quantify
over data that this block does not have and are not among its fields.

For the structure morphism `f = a_X` the isomorphism reads `ω_X ≅ Λ_X(d)[2d]`; see
`AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`. -/
structure Orientation (f : X ⟶ Y) (d : ℕ) [HasCompactification f] where
  /-- The `d`-th Tate twist `Λ_X(d)`, an invertible object of `D(X_ét)`. -/
  twist : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)
  /-- A Tate twist is invertible for the derived tensor product. -/
  isInvertible_twist : IsInvertible twist
  /-- The purity isomorphism `γ : Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`. -/
  purity : (L((f)^*[A])).obj (𝟙_ _) ⊗ twist⟦(2 * d : ℤ)⟧ ≅ (R(f)^![A]).obj (𝟙_ _)

variable {S : Scheme.{u}} {d : ℕ} (a : X ⟶ S) [HasCompactification a]

variable {A a} in
/-- The isomorphism `Λ_X(d)[2d] ≅ ω_X` of an orientation `o` of the structure morphism
`a : X ⟶ S`, given an identification `e : La^* Λ_S ≅ Λ_X`: the purity isomorphism read through
`e` and the left unitor,
```
                   λ⁻¹                       e⁻¹ ⊗ 1                         o.purity
Λ_X(d)[2d] ──────────────▶ Λ_X ⊗ Λ_X(d)[2d] ─────────▶ La^* Λ_S ⊗ Λ_X(d)[2d] ──────────▶ Ra^! Λ_S
```
-/
noncomputable def Orientation.dualizingComplexIso (o : Orientation A a d)
    (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) :
    o.twist⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a :=
  (λ_ _).symm ≪≫ whiskerRightIso e.symm _ ≪≫ o.purity

variable {A a} in
/-- The orientation of the structure morphism `a : X ⟶ S` with twist an invertible object `T`,
built from an isomorphism `γ : T⟦2d⟧ ≅ ω_X` and an identification `e : La^* Λ_S ≅ Λ_X`: its
purity isomorphism is
```
                         e ⊗ 1                  λ                γ
La^* Λ_S ⊗ T⟦2d⟧ ───────────────▶ Λ_X ⊗ T⟦2d⟧ ─────▶ T⟦2d⟧ ─────▶ Ra^! Λ_S
```
This is how an orientation in the form `Λ_X(d)[2d] ≅ ω_X`, as produced by smooth purity for a
Tate twist (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), is turned
into an `AlgebraicGeometry.Etale.Orientation`. -/
noncomputable def Orientation.ofDualizingComplexIso
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (hT : IsInvertible T)
    (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a) :
    Orientation A a d where
  twist := T
  isInvertible_twist := hT
  purity := whiskerRightIso e _ ≪≫ λ_ _ ≪≫ γ

/-- Blueprint `sk-def-sf-orientation`: Orientation: an interface record.

The special case of the orientation at the structure morphism `a : X ⟶ S`. There
`La^* Λ_S ≅ Λ_X` is the monoidal unit
(`AlgebraicGeometry.Etale.nonempty_leftDerivedUpperStar_unit_iso`) and `Ra^! Λ_S` is by
definition the dualizing complex, so the purity isomorphism reads `ω_X ≅ Λ_X(d)[2d]`: the
dualizing complex of a smooth `X` of pure relative dimension `d` over `S` is a shifted Tate
twist. -/
theorem Orientation.nonempty_iso_dualizingComplex (o : Orientation A a d) :
    Nonempty (dualizingComplex A a ≅ o.twist⟦(2 * d : ℤ)⟧) :=
  let ⟨e⟩ := nonempty_leftDerivedUpperStar_unit_iso A a
  ⟨(o.dualizingComplexIso e).symm⟩

/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex.

Let `a : X ⟶ S` be a structure morphism admitting a compactification, let `o` be an
orientation of `a` of relative dimension `d`, and let `K` be perfect over `Λ_X`, i.e.
dualizable. Substituting `ω_X ≅ Λ_X(d)[2d]` into `𝔻_X K = RHom_X(K, ω_X)` and interchanging
the twist with the internal hom identifies the Verdier dual of `K` with the twisted, shifted
coefficient dual: `𝔻_X K ≅ K^∨(d)[2d]`. -/
theorem Orientation.nonempty_iso_verdierDual_coefficientDual (o : Orientation A a d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K) :
    Nonempty ((verdierDual A a).obj (op K) ≅
      (DerivedCategory.coefficientDual A X).obj (op K) ⊗ o.twist⟦(2 * d : ℤ)⟧) :=
  sorry

/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex.

Under an orientation the Verdier dual of a perfect complex is perfect, so that `𝔻_X`
restricts to a contravariant anti-equivalence of the perfect objects. -/
theorem Orientation.isDualizable_verdierDual (o : Orientation A a d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K) :
    IsDualizable ((verdierDual A a).obj (op K)) :=
  sorry

end Etale

end AlgebraicGeometry
