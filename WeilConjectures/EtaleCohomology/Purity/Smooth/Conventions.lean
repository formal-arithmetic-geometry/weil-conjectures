/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Conventions for smooth purity

This file fixes the coefficient-side vocabulary the smooth-purity chapter runs on: the
constant complex `Λ_X`, the Tate twist `(m)`, finite Tor amplitude and the category
`D^b_{ctf}`, ⊗-invertible objects, the dualizing complex `ω_f = Rf^! Λ_Y`, and the *section
invariant* `𝒞(g, s) = Ls^* ω_g` of a smooth morphism with a closed section.

The coefficient stage is the finite one: a commutative ring `Λ` and the abelian category
`ModuleCat Λ`, so that `D(X_ét, Λ)` is
`DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat Λ))`. The remaining stages
`𝒪_E`, `E` and `ℚ̄_ℓ` are the derived-complete and rationalized categories of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete`; purity is transported to them in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`.

## Implementation notes

The Tate twist is the one place where a genuinely missing object had to be named. Its
blueprint home is the framework chapter (`def:coefficient-twists`), not this block, and the
sheaf of roots of unity `μ_n` it is built from belongs to the Kummer block; so
`AlgebraicGeometry.Etale.tateTwist` is an `opaque` placeholder, carrying a `TODO(unify)`
marker. It depends genuinely on its arguments and introduces no `sorryAx`, but it satisfies
no equations.

## Main definitions

- `AlgebraicGeometry.Etale.constantComplex`: the constant complex `Λ_X`.
- `AlgebraicGeometry.Etale.tateTwist`: the Tate twist `(m)` (placeholder).
- `AlgebraicGeometry.Etale.twistShift`: `K ↦ K(m)[2m]`.
- `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`,
  `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor`: finite Tor
  amplitude and `D^b_{ctf}(X, Λ)`.
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible`: ⊗-invertible objects.
- `AlgebraicGeometry.Etale.dualizingComplex`: `ω_f = Rf^! Λ_Y`.
- `AlgebraicGeometry.Etale.sectionInvariant`: `𝒞(g, s) = Ls^* ω_g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace Etale

variable (X : Scheme.{u})

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

The constant complex `Λ_X ∈ D(X_ét, Λ)`: the constant sheaf with value `Λ` placed in degree
zero. It is the unit for the derived tensor product, and the coefficient object every
statement of the purity chapter is normalized against. -/
noncomputable def constantComplex :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

/-- The Tate twist `(m) : D(X_ét, Λ) ⥤ D(X_ét, Λ)`, tensoring with the `m`-th power of the
invertible object `Λ(1) = μ_{ℓ^N} ⊗ Λ`.

The sheaf of roots of unity `μ_n` belongs to the Kummer block and the twist itself to the
framework chapter, so this is an `opaque` placeholder here; it satisfies no equations. -/
-- TODO(unify): def:coefficient-twists
noncomputable opaque tateTwist (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  𝟭 _

/-- The twist-and-shift functor `K ↦ K(m)[2m]` in which every purity statement is phrased. -/
noncomputable def twistShift (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  tateTwist Λ X m ⋙ shiftFunctor _ (2 * m)

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

An object `K` of `D(X_ét, Λ)` has *Tor amplitude in `[a, b]`* if for every sheaf `F` of
`Λ`-modules on `X_ét` the derived tensor product `K ⊗^L F` has vanishing cohomology outside
`[a, b]`. -/
def DerivedCategory.hasTorAmplitudeIn (a b : ℤ) :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < a ∨ b < q →
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- An object of `D(X_ét, Λ)` has *finite Tor amplitude* if it has Tor amplitude in some
bounded interval. -/
def DerivedCategory.finiteTorAmplitude :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Λ X a b K

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

The category `D^b_{ctf}(X, Λ)` of the purity chapter, as an object property: bounded with
constructible cohomology sheaves and of finite Tor amplitude. -/
def DerivedCategory.boundedConstructibleFiniteTor :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ⊓
    DerivedCategory.finiteTorAmplitude Λ X

/-- An object `L` of `D(X_ét, Λ)` is *invertible* if it has a tensor inverse: there is an `M`
with `L ⊗^L M ≅ Λ_X`. A lisse rank-one sheaf placed in any degree and twisted by any power of
the Tate object is invertible in this sense, and these are the only invertible objects that
occur in the purity chapter. -/
def DerivedCategory.isInvertible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun L ↦ ∃ M, Nonempty
    (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj M ≅ constantComplex Λ X)

variable {X}
variable {Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *dualizing complex* `ω_f = Rf^! Λ_Y ∈ D(X_ét, Λ)` of a morphism `f : X ⟶ Y` admitting a
compactification. Smooth purity is the assertion that `ω_f ≅ Λ_X(d)[2d]` for `f` smooth of
pure relative dimension `d`. -/
noncomputable def dualizingComplex :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj (constantComplex Λ Y)

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
