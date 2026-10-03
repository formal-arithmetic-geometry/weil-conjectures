/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Conventions for smooth purity

This file fixes the twist-side vocabulary the smooth-purity chapter runs on: the Tate twist
`(m)`, the twist-and-shift `K ↦ K(m)[2m]`, the dualizing complex `ω_f = Rf^! Λ_Y`, and the
*section invariant* `𝒞(g, s) = Ls^* ω_g` of a morphism with a section. The constant complex
`Λ_X`, finite Tor amplitude, `D^b_{ctf}` and ⊗-invertibility are framework-level notions and
live in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The dualizing complex
`ω_f = Rf^! Λ_Y` is the framework's `AlgebraicGeometry.Etale.dualizingComplex` for
`A = ModuleCat Λ`, the constant complex `Λ_Y` being the monoidal unit.

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
pullback, ⊗-invertibility, and the Kummer classes of units (the rank-one datum). Every
statement of the chapter carries `[HasTateTwist Λ]`, and becomes an unconditional theorem
once the Kummer block supplies the instance.

Invertibility is a field rather than a consequence of the zero and addition isomorphisms:
`Λ_X(m) ⊗ Λ_X(-m) ≅ Λ_X(0) ≅ Λ_X` is a two-line proof, but checking it forces the kernel to unfold
`AlgebraicGeometry.Etale.derivedTensor`, and that does not terminate in reasonable time.

## Main definitions

- `AlgebraicGeometry.Etale.HasTateTwist`: the Tate twist datum.
- `AlgebraicGeometry.Etale.tateObject`: the twisting object `Λ_X(m)`.
- `AlgebraicGeometry.Etale.tateTwist`: the twist `K ↦ K(m)`.
- `AlgebraicGeometry.Etale.twistShift`: `K ↦ K(m)[2m]`.
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
multiplicative in `m`, and compatible with pullback, together with the *rank-one datum*: the
Kummer class `κ(u) ∈ H¹(X, Λ(1))` of every unit `u`, natural under pullback and multiplicative
in `u`.

The identifications `Λ_X(0) ≅ Λ_X`, `Λ_X(m) ⊗ Λ_X(m') ≅ Λ_X(m + m')` and
`Lf^* Λ_Y(m) ≅ Λ_X(m)` are *data*, not mere existence statements: the fundamental class of a
regular immersion is glued from local classes built out of them, and the gluing is only
meaningful when the identifications used on overlapping pieces are the canonical ones.

**The concrete model.** Let `ℓ` be the prime with `ℓ^N Λ = 0`, `N ≥ 1`, and `ℓ` invertible on
the schemes in sight. Then `Λ_X(1) = μ_{ℓ^N} ⊗_{ℤ/ℓ^N} Λ`, which does not depend on the choice
of `N`, and `κ(u)` is the image of `u` under the boundary `Γ(X, 𝔾_m) ⟶ H¹(X, μ_{ℓ^N})` of the
Kummer sequence `0 → μ_{ℓ^N} → 𝔾_m → 𝔾_m → 0`
(`AlgebraicGeometry.Scheme.kummerSequence` with `n = ℓ^N`), tensored with `Λ`. Equivalently
`κ(u)` is the class of the `μ_{ℓ^N}`-torsor `Spec 𝒪_X[T]/(T^{ℓ^N} − u)`. For `u = t` the
coordinate of `𝔾_{m,Y}` this is the class `κ(t)` of `sk-def-purity-conv`.

The sheaf of roots of unity belongs to the Kummer block and the twist itself to the framework
chapter, so the datum is taken as a parameter here rather than constructed. -/
-- TODO(unify): def:coefficient-twists
class HasTateTwist where
  /-- The twisting object `Λ_X(m)`. -/
  twistObject (X : Scheme.{u}) (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- `Λ_X(0)` is the constant complex. -/
  twistObjectZeroIso (X : Scheme.{u}) : twistObject X 0 ≅ constantComplex Λ X
  /-- `Λ_X(m) ⊗^L Λ_X(m') ≅ Λ_X(m + m')`, which is what makes `Λ(c)[2c]` the `c`-th tensor
  power of `Λ(1)[2]` in the Künneth iteration of `sk-prop-an`. -/
  twistObjectAddIso (X : Scheme.{u}) (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (twistObject X m)).obj (twistObject X m') ≅
      twistObject X (m + m')
  /-- `Λ_X(m)[2m] ⊗^L Λ_X(m')[2m'] ≅ Λ_X(m + m')[2(m + m')]`: the identification
  `twistObjectAddIso` moved through the even shifts. All shifts are even, so no sign
  convention is involved. It is a field of its own because the compatibility of the derived
  tensor product with shifts is not yet available in the framework. -/
  shiftTwistObjectAddIso (X : Scheme.{u}) (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((twistObject X m)⟦2 * m⟧)).obj
        ((twistObject X m')⟦2 * m'⟧) ≅
      (twistObject X (m + m'))⟦2 * (m + m')⟧
  /-- The twist is compatible with pullback, `Lf^* Λ_Y(m) ≅ Λ_X(m)`; this is what makes the
  purity isomorphisms compatible with base change. -/
  leftDerivedUpperStarTwistObjectIso {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj (twistObject Y m) ≅ twistObject X m
  /-- Every twisting object is ⊗-invertible, with inverse `Λ_X(-m)`. Mathematically this is
  a consequence of `twistObjectZeroIso` and `twistObjectAddIso`; it is a field of its own
  because deriving it forces the kernel to unfold `AlgebraicGeometry.Etale.derivedTensor`,
  which is prohibitively expensive. -/
  isInvertible_twistObject (X : Scheme.{u}) (m : ℤ) :
    DerivedCategory.isInvertible Λ X (twistObject X m)
  /-- The *Kummer class* `κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of a unit
  `u ∈ Γ(X, 𝒪_X)ˣ`. -/
  kummerClass (X : Scheme.{u}) (u : Γ(X, ⊤)ˣ) :
    constantComplex Λ X ⟶ (twistObject X 1)⟦(1 : ℤ)⟧
  /-- The Kummer class is natural under pullback, `Lf^* κ(u) = κ(f^* u)`, along the
  identifications `Lf^* Λ_Y ≅ Λ_X` and `Lf^* Λ_Y(1) ≅ Λ_X(1)` of the datum. -/
  leftDerivedUpperStar_map_kummerClass {X Y : Scheme.{u}} (f : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Y u) ≫
        ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app (twistObject Y 1) ≫
          (leftDerivedUpperStarTwistObjectIso f 1).hom⟦(1 : ℤ)⟧' =
      ((L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (twistObjectZeroIso Y).symm ≪≫
          leftDerivedUpperStarTwistObjectIso f 0 ≪≫ twistObjectZeroIso X).hom ≫
        kummerClass X (Units.map f.appTop.hom.toMonoidHom u)
  /-- The Kummer class is multiplicative, `κ(uv) = κ(u) + κ(v)`: the Kummer boundary is a
  group homomorphism. -/
  kummerClass_mul (X : Scheme.{u}) (u v : Γ(X, ⊤)ˣ) :
    kummerClass X (u * v) = kummerClass X u + kummerClass X v

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

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *section invariant* `𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` of a morphism `g : V ⟶ B`
together with a section `s : B ⟶ V`. For `g` smooth of pure relative dimension `d` with `s` a
closed section, smooth purity identifies it with `Λ_B(d)[2d]`; the deformation to the normal
cone of the section reduces the general case to the standard pair `(𝔸^d_B → B, 0)`. -/
noncomputable def sectionInvariant {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g]
    (s : B ⟶ V) : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (L((s)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g)

end Etale

end AlgebraicGeometry
