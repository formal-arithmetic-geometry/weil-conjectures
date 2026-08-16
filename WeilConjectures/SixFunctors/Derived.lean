/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.DerivedCategory.HomotopyCategory.GrothendieckAbelian
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived six-functor layer and compactly supported cohomology

For an abelian coefficient category `A` admitting sheafification on the small étale sites,
the categories of `A`-valued étale sheaves are abelian, the pushforward
`g_* = Etale.lowerStar` along an arbitrary morphism `g` and the lower shriek
`f_! = Etale.lowerShriek` along a morphism `f` admitting a compactification are additive,
and this file records their total right derived functors
`Rg_* : D(Z_ét) ⥤ D(Y_ét)` and `Rf_! : D(X_ét) ⥤ D(Y_ét)` on the unbounded
derived categories, implemented via `CategoryTheory.Functor.rightDerivedFunctor`.

On top of these, this file defines compactly supported cohomology. The small étale site
of `X` has a terminal object, so the global sections functor
`Γ(X, -) = CategoryTheory.Sheaf.Γ` exists; it is additive, being right adjoint to the
additive constant sheaf functor, and its total right derived functor is the derived
global sections `RΓ(X, -) : D(X_ét) ⥤ D(A)`. For a morphism `f : X ⟶ Y` admitting a
compactification, the compactly supported derived global sections are *defined* as the
composite

`RΓc(X/Y, -) := RΓ(Y, Rf_! -) : D(X_ét) ⥤ D(A)`,

and the compactly supported cohomology is `Hᶜⁱ(X/Y, K) := Hⁱ(RΓc(X/Y, K))`. The
intermediate object `Rf_! K ∈ D(Y_ét)` and the coefficient complex `RΓc(X/Y, K) ∈ D(A)`
are not definitionally the same; the composite is the definition. For a scheme `X₀`
separated of finite type over a finite field, applying this to the structure morphism
of the geometric fiber recovers `RΓc(X, K) = RΓ(s, Ra_{X!} K)` and `H_c^i(X, K)` of the
trace-formula interface.

The chosen localized categories `HasDerivedCategory` are inputs with a general universe.
The construction of the unbounded right derived functor requires the source abelian
category to have K-injective resolutions (`CategoryTheory.Abelian.HasKInjectiveResolutions`).
The sheaf categories are Grothendieck abelian
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`) whenever the
coefficient category `A` is a concrete Grothendieck abelian category (with hom types and
underlying types in the universe `u` of the base schemes, and the forgetful functor
preserving limits and filtered colimits and reflecting isomorphisms); this covers the
intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`. That Grothendieck abelian
categories have K-injective resolutions is a theorem of Alonso Tarrío–Jeremías
López–Souto Salorio and Serpé; it is recorded here as the sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStar`: the total right derived functor
  `Rg_*` of the pushforward on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriek`: the total right derived functor
  `Rf_!` of the lower shriek on unbounded derived categories of étale sheaves.
- `CategoryTheory.Sheaf.Γ_additive`: the global sections functor on sheaves with values
  in an abelian category is additive.
- `AlgebraicGeometry.Etale.rightDerivedGlobalSections`: the derived global sections
  `RΓ(X, -) : D(X_ét) ⥤ D(A)`.
- `AlgebraicGeometry.Etale.compactlySupportedGlobalSections`: the compactly supported
  derived global sections `RΓc(X/Y, -) := RΓ(Y, Rf_! -)`.
- `AlgebraicGeometry.Etale.compactlySupportedCohomology`: the compactly supported
  cohomology `Hᶜⁱ(X/Y, -) := Hⁱ(RΓc(X/Y, -))`.

-/

@[expose] public section

universe w w' w'' v' u' u

open CategoryTheory Abelian Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (B : Type*) [Category* B] [Abelian B] [HasSheafify J B]

/-- The global sections functor on sheaves with values in an abelian category is
additive, being right adjoint to the additive constant sheaf functor. -/
instance Sheaf.Γ_additive [HasGlobalSectionsFunctor J B] : (Sheaf.Γ J B).Additive :=
  (constantSheafΓAdj J B).right_adjoint_additive

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

section DerivedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctor

end DerivedLowerStar

section DerivedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The total right derived functor `Rf_! : D(X_ét) ⥤ D(Y_ét)` of the lower shriek
`f_!` along a morphism `f : X ⟶ Y` admitting a compactification on the unbounded
derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctor

end DerivedLowerShriek

section DerivedGlobalSections

variable (X : Scheme.{u})
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w''} A]

/-- The derived global sections `RΓ(X, -) : D(X_ét) ⥤ D(A)`: the total right derived
functor of the global sections functor on étale sheaves, which exists since the small
étale site has a terminal object. -/
noncomputable def Etale.rightDerivedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor

end DerivedGlobalSections

section CompactlySupportedCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]
variable [HasDerivedCategory.{w''} A]

/-- The compactly supported derived global sections along a morphism `f : X ⟶ Y`
admitting a compactification, *defined* as the composite

`RΓc(X/Y, -) := RΓ(Y, Rf_! -) : D(X_ét) ⥤ D(A)`.

The intermediate object `Rf_! K ∈ D(Y_ét)` and the coefficient complex
`RΓc(X/Y, K) ∈ D(A)` are not definitionally the same. For the structure morphism of the
geometric fiber of a scheme separated of finite type over a finite field this is the
`RΓc(X, K) = RΓ(s, Ra_{X!} K)` of the trace-formula interface. -/
noncomputable def Etale.compactlySupportedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  Etale.rightDerivedLowerShriek A f ⋙ Etale.rightDerivedGlobalSections A Y

/-- The compactly supported cohomology along a morphism `f : X ⟶ Y` admitting a
compactification, `Hᶜⁱ(X/Y, K) := Hⁱ(RΓc(X/Y, K))`: the `i`-th homology object of the
compactly supported derived global sections. Finiteness is a theorem, not part of the
definition. -/
noncomputable def Etale.compactlySupportedCohomology (i : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  Etale.compactlySupportedGlobalSections A f ⋙ DerivedCategory.homologyFunctor A i

end CompactlySupportedCohomology

end AlgebraicGeometry
