/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *defined* here as a chosen right adjoint of the derived lower shriek `Rf_!`, both on the
unbounded and on the bounded below derived categories of étale sheaves.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint
  on `D(X_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)`, with scoped
  notation `R(f)^![A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekPlus` : `Rf_!` is a left
  adjoint on `D⁺(X_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlus` : `Rf^! : D⁺(Y_ét) ⥤ D⁺(X_ét)`, with
  scoped notation `R(f)^![A]+`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlusAdjunction` : the adjunction
  `Rf_! ⊣ Rf^!` on the bounded below derived categories.

## Implementation notes

* The two `IsLeftAdjoint` instances are `sorry` by design: this file only *states* that `Rf_!`
  has a right adjoint and packages that right adjoint, the proof is left to a later file. The
  adjoint exists by Brown representability, `Rf_!` being a colimit preserving functor between
  compactly generated triangulated categories.
* `Rf^!` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint extracted from
  the instance, not a construction. Only the adjunctions `rightDerivedUpperShriekAdjunction`
  and `rightDerivedUpperShriekPlusAdjunction` should be used about it; it has no definitional
  content.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R(g)_*[A]`, to mark that it lives on derived categories rather than on sheaves.
* The bounded below `Rf^!` is *not* known to restrict from the unbounded one along
  `DerivedCategory.Plus.ι`, so the two sections below are independent rather than the second
  one being a compatibility statement. The comparison is a `TODO`.

## TODO

* Compare `R(f)^![A]+` with `R(f)^![A]` on `D⁺`.
* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section Unbounded

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` is a left adjoint; its right adjoint
is the exceptional inverse image `Rf^!`. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint := sorry

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: *by
definition* a chosen right adjoint of the derived lower shriek `R(f)_![A]`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (R(f)_![A]).rightAdjoint

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  Adjunction.ofIsLeftAdjoint _

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

end Unbounded

section BoundedBelow

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the bounded below derived
categories is a left adjoint; its right adjoint is the exceptional inverse image `Rf^!`. -/
instance isLeftAdjoint_rightDerivedLowerShriekPlus : (R(f)_![A]+).IsLeftAdjoint := sorry

/-- The exceptional inverse image `Rf^! : D⁺(Y_ét) ⥤ D⁺(X_ét)` on the *bounded below* derived
categories of étale sheaves: *by definition* a chosen right adjoint of the derived lower
shriek `R(f)_![A]+`. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  (R(f)_![A]+).rightAdjoint

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^![" A "]+" =>
  rightDerivedUpperShriekPlus A f

/-- The adjunction `Rf_! ⊣ Rf^!` on the bounded below derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekPlusAdjunction : R(f)_![A]+ ⊣ R(f)^![A]+ :=
  Adjunction.ofIsLeftAdjoint _

instance : (R(f)^![A]+).IsRightAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction A f).isRightAdjoint

end BoundedBelow

end Etale

end AlgebraicGeometry
