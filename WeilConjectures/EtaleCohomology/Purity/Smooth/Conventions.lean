/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Conventions for smooth purity

This file fixes the twist-side vocabulary the smooth-purity chapter runs on: the Tate twist
`(m)`, the twist-and-shift `K ↦ K(m)[2m]`, the dualizing complex `ω_f = Rf^! Λ_Y`, and the
*section invariant* `𝒞(g, s) = Ls^* ω_g` of a morphism with a section. The constant complex
`Λ_X`, finite Tor amplitude, `D^b_{ctf}` and ⊗-invertibility are framework-level notions and
live in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.

The coefficient stage is the finite one: a commutative ring `Λ` and the abelian category
`ModuleCat Λ`, so that `D(X_ét, Λ)` is
`DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat Λ))`. Every statement of the chapter
assumes moreover that `Λ` is finite and that its exponent is invertible on the schemes in
sight (`AlgebraicGeometry.HasInvertibleExponent`); without that hypothesis smooth purity is
false, already for `Λ = ℤ/p` over a base of characteristic `p`. The remaining stages `𝒪_E`,
`E` and `ℚ̄_ℓ` are the derived-complete and rationalized categories of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete`; purity is transported to them in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`.

## Implementation notes

The Tate twist is the one place where a genuinely missing object had to be named. Its
blueprint home is the framework chapter (`def:coefficient-twists`), not this block, and the
sheaf of roots of unity `μ_n` it is built from belongs to the Kummer block. It is therefore
taken as a *parameter*: `AlgebraicGeometry.Etale.HasTateTwist` bundles the twisting objects
`Λ_X(m)` with the normalization `Λ_X(0) = Λ_X`, multiplicativity in `m`, compatibility with
pullback, and ⊗-invertibility. Every statement of the chapter carries `[HasTateTwist Λ]`, and
becomes an unconditional theorem once the Kummer block supplies the instance.

Invertibility is a field rather than a consequence of the other two: `Λ_X(m) ⊗ Λ_X(-m) ≅
Λ_X(0) ≅ Λ_X` is a two-line proof, but checking it forces the kernel to unfold
`AlgebraicGeometry.Etale.derivedTensor`, and that does not terminate in reasonable time.

## Main definitions

- `AlgebraicGeometry.Etale.HasTateTwist`: the Tate twist datum.
- `AlgebraicGeometry.Etale.tateObject`: the twisting object `Λ_X(m)`.
- `AlgebraicGeometry.Etale.tateTwist`: the twist `K ↦ K(m)`.
- `AlgebraicGeometry.Etale.twistShift`: `K ↦ K(m)[2m]`.
- `AlgebraicGeometry.Etale.dualizingComplex`: `ω_f = Rf^! Λ_Y`.
- `AlgebraicGeometry.Etale.sectionInvariant`: `𝒞(g, s) = Ls^* ω_g`.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_tateObject`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

A *Tate twist datum* for the coefficient ring `Λ`: for every scheme `X` and every `m : ℤ` a
⊗-invertible twisting object `Λ_X(m) ∈ D(X_ét, Λ)`, normalized by `Λ_X(0) = Λ_X`,
multiplicative in `m`, and compatible with pullback.

The sheaf of roots of unity `μ_n` that `Λ(1)` is built from belongs to the Kummer block and
the twist itself to the framework chapter, so the datum is taken as a parameter here rather
than constructed. -/
-- TODO(unify): def:coefficient-twists
class HasTateTwist where
  /-- The twisting object `Λ_X(m)`. -/
  twistObject (X : Scheme.{u}) (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- `Λ_X(0)` is the constant complex. -/
  nonempty_iso_twistObject_zero (X : Scheme.{u}) :
    Nonempty (twistObject X 0 ≅ constantComplex Λ X)
  /-- `Λ_X(m) ⊗^L Λ_X(m') ≅ Λ_X(m + m')`, which is what makes `Λ(c)[2c]` the `c`-th tensor
  power of `Λ(1)[2]` in the Künneth iteration of `sk-prop-an`. -/
  nonempty_iso_twistObject_add (X : Scheme.{u}) (m m' : ℤ) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (twistObject X m)).obj
      (twistObject X m') ≅ twistObject X (m + m'))
  /-- The twist is compatible with pullback, `Lf^* Λ_Y(m) ≅ Λ_X(m)`; this is what makes the
  purity isomorphisms compatible with base change. -/
  nonempty_iso_leftDerivedUpperStar_twistObject {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℤ) :
    Nonempty ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (twistObject Y m) ≅ twistObject X m)
  /-- Every twisting object is ⊗-invertible, with inverse `Λ_X(-m)`. Mathematically this is
  the conjunction of the previous two fields; it is a field of its own because deriving it
  forces the kernel to unfold `AlgebraicGeometry.Etale.derivedTensor`, which is prohibitively
  expensive. -/
  isInvertible_twistObject (X : Scheme.{u}) (m : ℤ) :
    DerivedCategory.isInvertible Λ X (twistObject X m)

variable [HasTateTwist Λ] (X : Scheme.{u})

/-- The twisting object `Λ_X(m) ∈ D(X_ét, Λ)` of a Tate twist datum. -/
noncomputable def tateObject (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  HasTateTwist.twistObject (Λ := Λ) X m

/-- Every Tate twisting object is ⊗-invertible, `Λ_X(m) ⊗^L Λ_X(-m) ≅ Λ_X`. -/
theorem isInvertible_tateObject (m : ℤ) :
    DerivedCategory.isInvertible Λ X (tateObject Λ X m) :=
  HasTateTwist.isInvertible_twistObject X m

/-- The Tate twist `(m) : D(X_ét, Λ) ⥤ D(X_ét, Λ)`, tensoring with the twisting object
`Λ_X(m)`. -/
noncomputable def tateTwist (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (tateObject Λ X m)

/-- The twist-and-shift functor `K ↦ K(m)[2m]` in which every purity statement is phrased. -/
noncomputable def twistShift (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  tateTwist Λ X m ⋙ shiftFunctor _ (2 * m)

variable {X}
variable {Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *dualizing complex* `ω_f = Rf^! Λ_Y ∈ D(X_ét, Λ)` of a morphism `f : X ⟶ Y` admitting a
compactification. Smooth purity is the assertion that `ω_f ≅ Λ_X(d)[2d]` for `f` smooth of
pure relative dimension `d`. -/
noncomputable def dualizingComplex :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj (constantComplex Λ Y)

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *section invariant* `𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` of a morphism `g : V ⟶ B`
together with a section `s : B ⟶ V`. For `g` smooth of pure relative dimension `d` with `s` a
closed section, smooth purity identifies it with `Λ_B(d)[2d]`; the deformation to the normal
cone of the section reduces the general case to the standard pair `(𝔸^d_B → B, 0)`. -/
noncomputable def sectionInvariant {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g]
    (s : B ⟶ V) : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (L((s)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g)

end Etale

end AlgebraicGeometry
