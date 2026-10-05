/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *defined* here as a chosen right adjoint of the derived lower shriek `Rf_!` on the
unbounded derived categories of étale sheaves. On the bounded below derived categories,
`Rf^!` is *not* defined by another adjoint-functor argument: it is the restriction of the
unbounded `Rf^!` along the inclusion `DerivedCategory.Plus.ι`, which makes sense because
`Rf^!` preserves bounded below objects. That the restriction is again a right adjoint, now
of the bounded below `Rf_!`, is then a theorem.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint
  on `D(X_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)`, with scoped
  notation `R(f)^![A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlus` : `Rf^! : D⁺(Y_ét) ⥤ D⁺(X_ét)`, the
  restriction of `R(f)^![A]` to the bounded below derived categories, with scoped notation
  `R(f)^![A]+`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlusAdjunction` : the adjunction
  `Rf_! ⊣ Rf^!` on the bounded below derived categories.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekPlus` : `Rf_!` is a left
  adjoint on `D⁺(X_ét)`, a consequence of the previous item.

## Implementation notes

* `isLeftAdjoint_rightDerivedLowerShriek` is `sorry` by design: this file only *states* that
  `Rf_!` has a right adjoint and packages that right adjoint, the proof is left to a later
  file. The adjoint exists by Brown representability, `Rf_!` being a colimit preserving
  functor between compactly generated triangulated categories.
* `plus_rightDerivedUpperShriek_obj`, that `Rf^!` preserves bounded below objects, is also
  `sorry` for now.
* `Rf^!` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint extracted from
  the instance, not a construction. Only the adjunctions `rightDerivedUpperShriekAdjunction`
  and `rightDerivedUpperShriekPlusAdjunction` should be used about it; it has no definitional
  content.
* By contrast, the bounded below `R(f)^![A]+` *is* a construction out of `R(f)^![A]`: by
  `rightDerivedUpperShriekPlusCompatibility` (which is `Iso.refl`) it is compatible with the
  inclusions of the bounded below derived categories by definition. In particular there is no
  ambiguity between "the right adjoint of `Rf_!` on `D⁺`" and "the restriction to `D⁺` of the
  right adjoint of `Rf_!` on `D`".
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.

## TODO

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

variable (R : Type*) [Ring R] [Linear R A] in
/-- If `A` is `R`-linear, the exceptional inverse image `Rf^!` is `R`-linear, being right
adjoint to the `R`-linear functor `Rf_!`. -/
instance linear_rightDerivedUpperShriek : (R(f)^![A]).Linear R :=
  (rightDerivedUpperShriekAdjunction A f).right_adjoint_linear (R := R)

end Unbounded

section BoundedBelow

/-- The exceptional inverse image `Rf^!` preserves bounded below objects: if `K ∈ D(Y_ét)`
is bounded below, then so is `Rf^! K ∈ D(X_ét)`.

This is what makes the bounded below `Rf^!` the restriction of the unbounded one. Note that
`Rf^!` is not left t-exact: the bound it produces is shifted by the cohomological amplitude
of `Rf_!`, which is why the statement is about `t.plus` rather than about `IsGE n` for a
fixed `n`. -/
lemma plus_rightDerivedUpperShriek_obj
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((R(f)^![A]).obj K) := sorry

/-- The exceptional inverse image `Rf^! : D⁺(Y_ét) ⥤ D⁺(X_ét)` on the *bounded below* derived
categories of étale sheaves: the restriction of the unbounded `R(f)^![A]` along the inclusions
of the bounded below derived categories, which is well defined by
`plus_rightDerivedUpperShriek_obj`. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ R(f)^![A])
    (fun K ↦ plus_rightDerivedUpperShriek_obj A f K.obj K.property)

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^![" A "]+" =>
  rightDerivedUpperShriekPlus A f

/-- The bounded below `R(f)^![A]+` is compatible with the inclusions of the bounded below
derived categories, by construction. -/
noncomputable def rightDerivedUpperShriekPlusCompatibility :
    R(f)^![A]+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)^![A] :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `Rf_! ⊣ Rf^!` on the bounded below derived categories of étale sheaves:
the unbounded adjunction `rightDerivedUpperShriekAdjunction` restricted along the fully
faithful inclusions `DerivedCategory.Plus.ι`, which is legitimate since both `Rf_!` and
`Rf^!` preserve bounded below objects. -/
noncomputable def rightDerivedUpperShriekPlusAdjunction : R(f)_![A]+ ⊣ R(f)^![A]+ :=
  Adjunction.restrictFullyFaithful (rightDerivedUpperShriekAdjunction A f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (rightDerivedLowerShriekPlusCompatibility A f).symm
    (rightDerivedUpperShriekPlusCompatibility A f).symm

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the bounded below derived
categories is a left adjoint, its right adjoint being `R(f)^![A]+`. -/
instance isLeftAdjoint_rightDerivedLowerShriekPlus : (R(f)_![A]+).IsLeftAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction A f).isLeftAdjoint

instance : (R(f)^![A]+).IsRightAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction A f).isRightAdjoint

end BoundedBelow

end Etale

end AlgebraicGeometry
