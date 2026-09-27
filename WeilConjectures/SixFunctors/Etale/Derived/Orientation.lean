/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

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

As elsewhere on this branch a Tate twist `Λ_X(d)` is not constructed but carried as a datum: it
is an invertible object of `D(X_ét)` in the sense of
`AlgebraicGeometry.Etale.DerivedCategory.invertible`.

## Main definitions

- `AlgebraicGeometry.Etale.Orientation`: the interface record of an orientation of relative
  dimension `d`, namely a Tate twist together with `Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`.

## Main statements

- `AlgebraicGeometry.Etale.Orientation.nonempty_dualizingComplex_iso`
  (`sk-def-sf-orientation`): for the structure morphism the orientation reads
  `ω_X ≅ Λ_X(d)[2d]`.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`
  (`sk-thm-sf-dual-perfect`): `𝔻_X K ≅ K^∨(d)[2d]` for a perfect `K`, so that `𝔻_X` is an
  anti-equivalence of the perfect objects with the coefficient-dual biduality.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

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
isomorphism `γ : Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`, natural in `Y` and compatible with composition,
étale base change, finite reduction, scalar extension and the pro-étale realization.

In the blueprint an orientation is **not** an assumption: it is the smooth purity theorem
`sk-thm-smooth-purity`, which lives in a different blueprint block and is not formalised here.
This structure therefore records only the interface that purity produces and that the six
operations consume, and the naturality and compatibility clauses — which quantify over data
that this block does not have — are not among its fields.

For the structure morphism `f = a_X` the isomorphism reads `ω_X ≅ Λ_X(d)[2d]`; see
`AlgebraicGeometry.Etale.Orientation.nonempty_dualizingComplex_iso`. -/
structure Orientation (f : X ⟶ Y) [HasCompactification f] (d : ℕ) where
  /-- The `d`-th Tate twist `Λ_X(d)`, an invertible object of `D(X_ét)`. -/
  twist : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)
  /-- A Tate twist is invertible for the derived tensor product. -/
  invertible_twist : Etale.DerivedCategory.invertible A X twist
  /-- The purity isomorphism `Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`. -/
  iso : (L((f)^*[A])).obj (𝟙_ _) ⊗ twist⟦(2 * d : ℤ)⟧ ≅ (R(f)^![A]).obj (𝟙_ _)

variable {S : Scheme.{u}} {d : ℕ} (a : X ⟶ S) [HasCompactification a]

/-- Blueprint `sk-def-sf-orientation`: Orientation: an interface record.

The special case of the orientation at the structure morphism `a : X ⟶ S`. There
`Lf^* Λ_S ≅ Λ_X` is the monoidal unit and `Ra^! Λ_S` is by definition the dualizing complex, so
the purity isomorphism reads `ω_X ≅ Λ_X(d)[2d]`: the dualizing complex of a smooth `X` of pure
relative dimension `d` over `S` is a shifted Tate twist. -/
theorem Orientation.nonempty_dualizingComplex_iso (o : Orientation A a d) :
    Nonempty (dualizingComplex A a ≅ o.twist⟦(2 * d : ℤ)⟧) :=
  sorry

/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex.

Let `X` be separated of finite type with admissible structure morphism `a : X ⟶ S`, and let `K`
be perfect over `Λ_X`, i.e. site-perfect in the sense of
`AlgebraicGeometry.Etale.DerivedCategory.sitePerfect`. Given an orientation `o` of `a` of
relative dimension `d`, substituting `ω_X ≅ Λ_X(d)[2d]` into `𝔻_X K = RHom_X(K, ω_X)` and
interchanging the twist with the internal hom identifies the Verdier dual of `K` with the
twisted, shifted coefficient dual: `𝔻_X K ≅ K^∨(d)[2d]`.

Consequently `𝔻_X` preserves the perfect objects, so it restricts to a contravariant
anti-equivalence of them, and under the above identification the double-dual morphism
`K ⟶ 𝔻_X 𝔻_X K` becomes the coefficient-dual biduality
`AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_coefficientDual`, the two
twists `Λ_X(d)[2d]` cancelling. -/
theorem Orientation.nonempty_iso_verdierDual_coefficientDual (o : Orientation A a d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.sitePerfect A X K) :
    Nonempty ((verdierDual A a).obj (op K) ≅
        (DerivedCategory.coefficientDual A X).obj (op K) ⊗ o.twist⟦(2 * d : ℤ)⟧) ∧
      DerivedCategory.sitePerfect A X ((verdierDual A a).obj (op K)) ∧
      Nonempty (K ≅ (verdierDual A a).obj (op ((verdierDual A a).obj (op K)))) :=
  sorry

end Etale

end AlgebraicGeometry
