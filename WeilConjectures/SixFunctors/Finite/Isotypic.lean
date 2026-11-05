/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.AddChar
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Finite.ConstantSheafEnd

/-!
# Isotypic components of `f_* Λ` for a finite covering with a group action

Let `f : Y ⟶ X` be a finite morphism and let a finite abelian group `G` act on `Y` over `X`
through endomorphisms `τ_g`, so that `τ_g ≫ f = f` and `τ_{a + b} = τ_a ≫ τ_b`. Pulling back
sections along `τ_g` makes `G` act on the pushforward `f_* Λ` of the constant sheaf. For a
character `χ` of `G` with `|G|` invertible in `Λ`, the endomorphism
`e_χ = |G|⁻¹ ∑_g χ(-g) τ_g^♯` of `f_* Λ` is an idempotent cutting out the `χ`-isotypic
component.

If `G` acts transitively on the geometric fibres of `f`, a morphism `φ : F ⟶ f_* Λ` on which
`G` acts through `χ`, and whose adjoint `f^* F ⟶ Λ` is an isomorphism, identifies `F` with the
isotypic component. In particular two such sheaves are isomorphic as soon as `f` is surjective.
This is how the Artin–Schreier sheaf and its relatives are compared: a sheaf which becomes
trivial on the covering `f`, with descent datum given by `χ`, is determined by `χ`.

## Main definitions

- `AlgebraicGeometry.Etale.isotypicIdempotent`: the idempotent `e_χ` of `f_* Λ`.

## Main results

- `AlgebraicGeometry.Etale.isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent`: for
  `φ : F ⟶ f_* Λ` of type `χ` with invertible adjoint, `f^*` of the induced morphism from `F`
  to the image of `e_χ` is an isomorphism.
- `AlgebraicGeometry.Etale.nonempty_iso_of_isotypic`: for `f` surjective, two sheaves with
  such morphisms to `f_* Λ` are isomorphic.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

section Stalk

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω]
  [IsAlgClosed Ω]

end Stalk

section Idempotent

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {G : Type*} [AddCommGroup G] [Fintype G]
  (τ : G → (Y ⟶ Y)) (hτ : ∀ g, τ g ≫ f = f)

variable [Invertible (Fintype.card G : Λ)] (χ : AddChar G Λ)

variable (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b)

end Idempotent

section Finite

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] {G : Type*} [AddCommGroup G] [Fintype G]
  (τ : G → (Y ⟶ Y)) (hτ : ∀ g, τ g ≫ f = f) [∀ g, IsFinite (τ g)]
  [Invertible (Fintype.card G : Λ)] (χ : AddChar G Λ) (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

end Finite

end AlgebraicGeometry.Etale

end
