/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!

# Derived upper shriek on module objects over `C(-, T)`

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek`, for the
coefficient ring objects `A_X(T) = C(-, T)` of a commutative topological ring `T`.

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *defined* as a chosen right adjoint of the derived lower shriek `Rf_!` on the unbounded
derived categories of module objects. On the bounded below derived categories, `Rf^!` is the
restriction of the unbounded `Rf^!` along the inclusion `DerivedCategory.Plus.ι`, which makes
sense because `Rf^!` preserves bounded below objects; that the restriction is again right
adjoint to the bounded below `Rf_!` is then a theorem.

The alternative description `f^! = Coext_{α_f} ∘ (linear f^!)`, by coextension of scalars along
`α_f` (`Mod.coextendScalars`), is available once an `Ab`-level `f^!` with a coherent projection
formula is, and is not formalized here.

## Main definitions

- `ProEtale.ContinuousMapRing.rightDerivedUpperShriek` :
  `Rf^! : D(Mod_{A_Y(T)}) ⥤ D(Mod_{A_X(T)})`, with scoped notation `R(f)^!⟦T⟧`, and
  `ProEtale.ContinuousMapRing.rightDerivedUpperShriekPlus`, its restriction to the bounded
  below derived categories, with scoped notation `R(f)^!⟦T⟧+`.

## Main results

- `ProEtale.ContinuousMapRing.rightDerivedUpperShriekAdjunction` and
  `ProEtale.ContinuousMapRing.rightDerivedUpperShriekPlusAdjunction` : the adjunctions
  `Rf_! ⊣ Rf^!` on the unbounded and on the bounded below derived categories.

## Sorried input

* `ProEtale.ContinuousMapRing.isLeftAdjoint_rightDerivedLowerShriek`: `Rf_!` has a right
  adjoint. As in the finite-coefficient case, the adjoint exists by Brown representability,
  `Rf_!` being a colimit preserving functor between compactly generated triangulated categories.
* `ProEtale.ContinuousMapRing.plus_rightDerivedUpperShriek_obj`: `Rf^!` preserves bounded below
  objects.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section Unbounded

/-- The derived lower shriek `Rf_! : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_Y(T)})` on module objects is a
left adjoint; its right adjoint is the exceptional inverse image `Rf^!`. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_!⟦T⟧).IsLeftAdjoint := sorry

/-- The exceptional inverse image `Rf^! : D(Mod_{A_Y(T)}) ⥤ D(Mod_{A_X(T)})` along a morphism
`f : X ⟶ Y` admitting a compactification, on the unbounded derived categories of module objects
over `C(-, T)`: *by definition* a chosen right adjoint of the derived lower shriek
`R(f)_!⟦T⟧`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (continuousMapRingObj T X)) :=
  (R(f)_!⟦T⟧).rightAdjoint

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^!⟦" T "⟧" => rightDerivedUpperShriek T f

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of module objects. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_!⟦T⟧ ⊣ R(f)^!⟦T⟧ :=
  Adjunction.ofIsLeftAdjoint _

instance : (R(f)^!⟦T⟧).IsRightAdjoint := (rightDerivedUpperShriekAdjunction T f).isRightAdjoint

end Unbounded

section BoundedBelow

/-- The exceptional inverse image `Rf^!` on module objects preserves bounded below objects. -/
lemma plus_rightDerivedUpperShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (continuousMapRingObj T Y)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((R(f)^!⟦T⟧).obj K) := sorry

/-- The exceptional inverse image `Rf^! : D⁺(Mod_{A_Y(T)}) ⥤ D⁺(Mod_{A_X(T)})` on the *bounded
below* derived categories of module objects: the restriction of the unbounded `R(f)^!⟦T⟧` along
the inclusions of the bounded below derived categories, which is well defined by
`plus_rightDerivedUpperShriek_obj`. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (continuousMapRingObj T Y)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (continuousMapRingObj T X)) :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ R(f)^!⟦T⟧)
    (fun K ↦ plus_rightDerivedUpperShriek_obj T f K.obj K.property)

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^!⟦" T "⟧+" => rightDerivedUpperShriekPlus T f

/-- The bounded below `R(f)^!⟦T⟧+` is compatible with the inclusions of the bounded below
derived categories, by construction. -/
noncomputable def rightDerivedUpperShriekPlusCompatibility :
    R(f)^!⟦T⟧+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)^!⟦T⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `Rf_! ⊣ Rf^!` on the bounded below derived categories of module objects:
the unbounded adjunction restricted along the fully faithful inclusions
`DerivedCategory.Plus.ι`, which is legitimate since both `Rf_!` and `Rf^!` preserve bounded
below objects. -/
noncomputable def rightDerivedUpperShriekPlusAdjunction : R(f)_!⟦T⟧+ ⊣ R(f)^!⟦T⟧+ :=
  Adjunction.restrictFullyFaithful (rightDerivedUpperShriekAdjunction T f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (rightDerivedLowerShriekPlusCompatibility T f).symm
    (rightDerivedUpperShriekPlusCompatibility T f).symm

/-- The derived lower shriek `Rf_!` on the bounded below derived categories of module objects
is a left adjoint, its right adjoint being `R(f)^!⟦T⟧+`. -/
instance isLeftAdjoint_rightDerivedLowerShriekPlus : (R(f)_!⟦T⟧+).IsLeftAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction T f).isLeftAdjoint

instance : (R(f)^!⟦T⟧+).IsRightAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction T f).isRightAdjoint

end BoundedBelow

end AlgebraicGeometry.ProEtale.ContinuousMapRing
