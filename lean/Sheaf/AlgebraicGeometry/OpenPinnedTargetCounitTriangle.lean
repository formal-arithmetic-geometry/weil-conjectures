/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import Sheaf.AlgebraicGeometry.PinnedPullbackCompositionShifts

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

/-- Termwise comparison for restricting the target of a composite tensor pullback.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-target-counit-triangle). -/
def openPinnedHomotopyTargetCompositionIso
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U' : X'.Opens) :
    (Scheme.Modules.tensorPullback (U'.ι ≫ k)).mapHomotopyCategory (.up ℤ) ≅
      (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        (schemeOpenRestriction X' U').mapHomotopyCategory (.up ℤ) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact (Functor.mapHomotopyCategoryCompIso
    (Functor.isoWhiskerLeft _ (openPinnedTensorOpenIso X' U').symm ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm)
    (.up ℤ)).symm

/-- The target-open leg of the derived counit composition calculation.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-target-counit-triangle).
Proof: naturality of the open-pullback comparison moves the counit for k
past its component. The factorization equation of leftDerivedUnique identifies
that comparison followed by the exact restriction factor with the counit for
U' inclusion followed by the localized underived open tensor comparison.
The selected composition comparison factors the successive counits through
its composite counit. Combine these two equations and functoriality of Qh.
This uses no source open or commuting square, and applies to every complex,
including zero complexes and the empty open. -/
theorem open_pinned_target_counit_triangle
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U' : X'.Opens)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (singleComplexOpenPullbackIso X' U').hom.app
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) =
    (pinnedPullbackComposition.{u, w} U'.ι k).hom.app (DerivedCategory.Qh.obj P) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) := by
  sorry

end AlgebraicGeometry
