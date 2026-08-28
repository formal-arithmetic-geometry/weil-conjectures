/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Derived.HasDerivedCategory
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived Lower Shriek

# Main Results

- `AlgebraicGeometry.Compactification.rightDerivedLowerShriek` : `Rf_!` with respect to a
  compcatification.

- `AlgebraicGeometry.Compactification.rightDerivedLowerShriekPlus` : `Rf_!`
  on bounded below derived category with respect to a compcatification.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriek` : `Rf_!`
  specifying to the chosen compcatification `HasCompactification.compactification`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriek` : `Rf_!` on bounded below derived category
  specifying to the chosen compcatification `HasCompactification.compactification`.

- `AlgebraicGeometry.Etale.compactlySupportedCohomology` : `H_c`

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerShriek

variable {X Y : Scheme.{u}}

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves: the
functor `Di_!` induced on derived categories by the *exact* extension by zero `i_!`, followed
by the total right derived pushforward `Rg_*`.

This is how `Rf_!` is defined in the six functor formalism: `i_!` is exact
(`Etale.preservesFiniteLimits_openImmersionLowerShriek` and the fact that it is a left
adjoint), so it needs no derivation and induces `Di_! = Functor.mapDerivedCategory` termwise;
only the pushforward is derived.

It is deliberately *not* the total right derived functor of the composite
`i_! ⋙ g_* = Etale.lowerShriek`. The two agree exactly when `i_!` sends injective sheaves to
`g_*`-acyclic ones, which is a theorem, not a definitional matter, and is not proved here. -/
noncomputable def Compactification.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctor

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of étale sheaves:
the bounded below counterpart of `Compactification.rightDerivedLowerShriek`, with `Di_!` the
functor `Functor.mapDerivedCategoryPlus` induced by the exact `i_!` and `R⁺g_*` the bounded
below right derived pushforward. -/
noncomputable def Compactification.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctorPlus

end OfCompactification

variable (f : X ⟶ Y) [HasCompactification f]

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `Compactification.rightDerivedLowerShriek` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def Etale.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (HasCompactification.compactification f).rightDerivedLowerShriek A

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the *bounded below* derived
categories of étale sheaves: the functor `Compactification.rightDerivedLowerShriekPlus`
attached to the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def Etale.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (HasCompactification.compactification f).rightDerivedLowerShriekPlus A

lemma Etale.rightDerivedLowerShriek_eq : Etale.rightDerivedLowerShriek A f =
    (HasCompactification.compactification f).rightDerivedLowerShriek A := rfl

lemma Etale.rightDerivedLowerShriekPlus_eq : Etale.rightDerivedLowerShriekPlus A f =
    (HasCompactification.compactification f).rightDerivedLowerShriekPlus A := rfl

end DerivedLowerShriek

end AlgebraicGeometry

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (B : Type*) [Category* B] [Abelian B] [HasSheafify J B]

/-- The global sections functor on sheaves with values in an abelian category is
additive, being right adjoint to the additive constant sheaf functor. -/
instance Sheaf.Γ_additive [HasGlobalSectionsFunctor J B] : (Sheaf.Γ J B).Additive :=
  (constantSheafΓAdj J B).right_adjoint_additive

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

@[instance_reducible]
noncomputable def hasDerivedCategory_coefficient : HasDerivedCategory.{u + 1} A :=
  HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _

end CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

attribute [local instance] CategoryTheory.hasDerivedCategory_coefficient

section DerivedGlobalSections

variable (X : Scheme.{u})

/-- The derived global sections `RΓ(X, -) : D(X_ét) ⥤ D(A)`: the total right derived
functor of the global sections functor on étale sheaves, which exists since the small
étale site has a terminal object. -/
noncomputable def Etale.rightDerivedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor

end DerivedGlobalSections

section CompactlySupportedCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

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
