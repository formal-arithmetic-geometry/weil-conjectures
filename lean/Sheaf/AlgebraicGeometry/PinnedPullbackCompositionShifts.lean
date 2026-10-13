/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PinnedPullbackCounitShifts

/-! # Shift compatibility of the selected pullback composition comparison
Source: Stacks Project, Tags 08HY and 0D5S. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The composition comparison selected by its left-derived universal property.
Source: Stacks Project, Tag 0D5S. -/
abbrev pinnedPullbackComposition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) f g

/-- The selected pullback composition comparison commutes with the counit-compatible shifts.
Source: Stacks Project, Tag 0D5S, canonical derived pullback composition.
(blueprint: lem-pc-pinned-pullback-composition-shifts).
Proof: precompose both proposed shift equations with the localization functor Qh
and then postcompose with the selected counit of the composite pullback. The
factorization of the selected left-derived lift identifies each side with the
successive counits followed by the termwise composition comparison. The assumed
shift equations for the counits and the shift equation for termwise tensor
reassociation identify these expressions. The left-derived universal property
makes the two lifted maps equal. This proves the equation for each integer;
no cartesian, flatness or boundedness hypothesis enters. -/
theorem pinnedPullbackComposition_commShift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    (hs : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      letI := s f
      NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI := s f
    letI := s g
    letI := s (f ≫ g)
    NatTrans.CommShift (pinnedPullbackComposition.{u, w} f g).hom ℤ := by sorry

end AlgebraicGeometry
