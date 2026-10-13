/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PinnedPullbackCounitShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Shift compatibility of the selected derived adjunction
Source: Stacks Project, Tags 08HY and 0D5S. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The adjunction selected with the composition-pinned left-derived counit.
Source: Stacks Project, Tag 08HY, canonical derived adjunction. -/
abbrev pinnedDerivedAdjunction
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Classical.choose (exists_schemeDerivedAdjunction.{u, w} f
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) f)
    (pinnedPullbackCounit.{u, w} f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f))

/-- The selected derived adjunction respects the counit-compatible pullback shifts
and the recorded right-derived direct-image shifts.
Source: Stacks Project, Tag 08HY, canonical derived adjunction; Tag 079W.
(blueprint: lem-pc-pinned-derived-adjunction-shifts).
Proof: the normalization equation of exists_schemeDerivedAdjunction identifies
its Hom equivalence on localized representatives with the termwise tensor-pullback
adjunction, the selected left-derived counit and the right-derived unit. The
termwise adjunction commutes with shifts. On K-injective representatives the
right-derived unit commutes with the shift structure transported from the
K-injective equivalence. Combine this with the assumed shift equation for the
selected left-derived counit to obtain the shifted Hom-equivalence equation.
K-flat and K-injective resolutions represent every object, so naturality extends
this equation to arbitrary derived objects. Apply it to identity morphisms to
obtain the shift equations for the derived unit and counit, precisely the two
fields of Adjunction.CommShift. This concerns one morphism, independently of
any base-change square or pullback composition comparison. -/
theorem pinnedDerivedAdjunction_commShift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    (hs : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      letI := s f
      NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := s f
    (pinnedDerivedAdjunction.{u, w} f).CommShift ℤ := by sorry

end AlgebraicGeometry
