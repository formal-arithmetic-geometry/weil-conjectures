/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PinnedPullbackCounitShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Shift compatibility of the canonical derived base-change mate
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-pinned-base-change-mate-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The base-change components form a natural transformation commuting with shift,
when pullback shifts are transported using the selected left-derived counits.
Source: Stacks Project, Tag 08HY, canonical base-change mate.
(blueprint: lem-pc-pinned-base-change-mate-shifts).
Proof: the Hom equivalences of the selected derived adjunctions are pinned to the
underived adjunction and the selected left-derived counits, as recorded in
exists_schemeDerivedAdjunction. Hence their units and counits commute with the
shift comparisons transported through these counits and the right-derived units.
The composition comparison is the unique left-derived lift of termwise tensor
reassociation, which commutes with shift. Its inverse does too. Equality
transport along the square is compatible with these comparisons. Naturality of
all these maps and of the adjunction Hom equivalence first constructs the stated
natural transformation. The shift equations for the composition comparison,
adjunction counit and transpose then prove NatTrans.CommShift for this
transformation. This is a statement about arbitrary derived objects, before
restriction to singles and before the final tensor counit or H. -/
theorem exists_pinned_base_change_mate_shifts
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    (hs : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      letI := s f
      NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ)
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g) :
    letI := s g
    letI := s g'
    ∃ τ : schemeDerivedDirectImage.{u, w, w} f ⋙ derivedPullback.{u, w} g ⟶
        derivedPullback.{u, w} g' ⋙ schemeDerivedDirectImage.{u, w, w} f',
      (∀ E, τ.app E = schemeDerivedBaseChangeMap.{u, w} f f' g g' h E) ∧
        NatTrans.CommShift τ ℤ := by sorry

end AlgebraicGeometry
