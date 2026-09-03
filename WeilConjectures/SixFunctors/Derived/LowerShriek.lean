/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived Lower Shriek

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` : `Rf_!` with respect
  to a compactification `c`, with scoped notation `Rf_!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlus` : `Rf_!`
  on bounded below derived category with respect to a compactification `c`, with scoped
  notation `Rf_!(c)[A]+`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriek` : `Rf_!`
  specifying to the chosen compactification `HasCompactification.compactification`, with
  scoped notation `R(f)_![A]`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus` : `Rf_!` on bounded below derived
  category specifying to the chosen compactification `HasCompactification.compactification`,
  with scoped notation `R(f)_![A]+`.

- `AlgebraicGeometry.Etale.compactlySupportedCohomology` : `H_c`, with scoped notation
  `H_c(f)[A](i)`.

The hypothesis `HasCompactification f` of `rightDerivedLowerShriek` and of the functors
built from it is discharged by Nagata's compactification theorem (the instance registered in
`WeilConjectures.Compactification.NagataCompactification`, which this file imports through
`WeilConjectures.SixFunctors.LowerShriek.Defs`): `Rf_!` is available for every separated,
quasi-compact morphism locally of finite type over a quasi-compact quasi-separated base,
with no compactification supplied by hand. The `example` after
`rightDerivedLowerShriekPlus_eq` records this.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section DerivedLowerShriek

variable {X Y : Scheme.{u}}

section OfCompactification

namespace Etale

variable {f : X ⟶ Y} (c : Compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves: the
functor `Di_!` induced on derived categories by the *exact* extension by zero `i_!`, followed
by the total right derived pushforward `Rg_*`.

Warning: It is deliberately *not* the total right derived functor of the composite
`i_! ⋙ g_* = Etale.lowerShriek`. In general, `i_!` does not sends injective sheaves to
`g_*`-acyclic ones, and `Rf_!` is not the derived functor of `f_!`, through its zeroth
homology is `f_!`. Deligne made explicit calculations on $A^1$, see SGA. -/
noncomputable def rightDerivedLowerShriekOfCompactification :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (c.i)_!open[A].mapDerivedCategory ⋙ (c.g)_*[A].rightDerivedFunctor

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of étale sheaves:
the bounded below counterpart of `rightDerivedLowerShriekOfCompactification`, with `Di_!` the
functor `Functor.mapDerivedCategoryPlus` induced by the exact `i_!` and `R⁺g_*` the bounded
below right derived pushforward. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (c.i)_!open[A].mapDerivedCategoryPlus ⋙ (c.g)_*[A].rightDerivedFunctorPlus

@[inherit_doc rightDerivedLowerShriekOfCompactification]
scoped notation "Rf_!("c")[" A "]" =>
  rightDerivedLowerShriekOfCompactification A c

@[inherit_doc rightDerivedLowerShriekOfCompactificationPlus]
scoped notation "Rf_!("c")[" A "]+" =>
  rightDerivedLowerShriekOfCompactificationPlus A c

end Etale

end OfCompactification

variable (f : X ⟶ Y) [HasCompactification f]

namespace Etale

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `rightDerivedLowerShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(HasCompactification.compactification f)[A]

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_![" A "]" =>
  rightDerivedLowerShriek A f

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the *bounded below* derived
categories of étale sheaves: the functor `rightDerivedLowerShriekOfCompactificationPlus`
attached to the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(HasCompactification.compactification f)[A]+

@[inherit_doc rightDerivedLowerShriekPlus]
scoped notation "R(" f ")_![" A "]+" =>
  rightDerivedLowerShriekPlus A f

lemma rightDerivedLowerShriek_eq : R(f)_![A] =
    Rf_!(HasCompactification.compactification f)[A] := rfl

lemma rightDerivedLowerShriekPlus_eq : R(f)_![A]+ =
    Rf_!(HasCompactification.compactification f)[A]+ := rfl

section Nagata

/-- `Rf_!` exists for every separated, quasi-compact morphism locally of finite type to a
quasi-compact quasi-separated base, by Nagata's compactification theorem: the instance
`HasCompactification f` needed by `rightDerivedLowerShriek` is found by instance search, so
no compactification has to be supplied. -/
noncomputable example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  R(f)_![A]

end Nagata

end Etale

end DerivedLowerShriek

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section DerivedGlobalSections

namespace Etale

variable (X : Scheme.{u})

/-- The derived global sections `RΓ(X, -) : D(X_ét) ⥤ D(A)`: the total right derived
functor of the global sections functor on étale sheaves, which exists since the small
étale site has a terminal object. -/
noncomputable def rightDerivedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor

end Etale

end DerivedGlobalSections

section CompactlySupportedCohomology

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The compactly supported derived global sections along a morphism `f : X ⟶ Y`
admitting a compactification, *defined* as the composite

`RΓc(X/Y, -) := RΓ(Y, Rf_! -) : D(X_ét) ⥤ D(A)`.

The intermediate object `Rf_! K ∈ D(Y_ét)` and the coefficient complex
`RΓc(X/Y, K) ∈ D(A)` are not definitionally the same. For the structure morphism of the
geometric fiber of a scheme separated of finite type over a finite field this is the
`RΓc(X, K) = RΓ(s, Ra_{X!} K)` of the trace-formula interface. -/
noncomputable def compactlySupportedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  R(f)_![A] ⋙ rightDerivedGlobalSections A Y

/-- The compactly supported cohomology along a morphism `f : X ⟶ Y` admitting a
compactification, `Hᶜⁱ(X/Y, K) := Hⁱ(RΓc(X/Y, K))`: the `i`-th homology object of the
compactly supported derived global sections. Finiteness is a theorem, not part of the
definition. -/
noncomputable def compactlySupportedCohomology (i : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  compactlySupportedGlobalSections A f ⋙ DerivedCategory.homologyFunctor A i

@[inherit_doc compactlySupportedCohomology]
scoped notation "H_c(" f ")[" A "](" i ")" =>
  compactlySupportedCohomology A f i

end Etale

end CompactlySupportedCohomology

end AlgebraicGeometry
