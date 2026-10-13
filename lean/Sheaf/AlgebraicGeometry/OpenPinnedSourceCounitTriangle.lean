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

/-- Termwise comparison for restricting the source before tensor pullback.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-source-counit-triangle). -/
def openPinnedHomotopySourceCompositionIso
    {X : Scheme.{u}} (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme) :
    (Scheme.Modules.tensorPullback (j ≫ U.ι)).mapHomotopyCategory (.up ℤ) ≅
      (schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact (Functor.mapHomotopyCategoryCompIso
    (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).symm)
    (.up ℤ)).symm

/-- The source-open leg of the derived counit composition calculation.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-source-counit-triangle).
Proof: factor the selected composition comparison followed by the composite
counit into the counit of U inclusion, then the counit of j, then the
underived composition comparison. Cancel that last comparison against its
inverse in the displayed source comparison. Naturality of the counit for j
moves the underived open tensor comparison to its source. The factorization
of leftDerivedUnique for the open inclusion replaces the counit for U and
the open tensor comparison by the open derived comparison and the exact
restriction factor. Cancel the inverse open derived comparison. Every step
is natural in P and requires no target open or commuting square. -/
theorem open_pinned_source_counit_triangle
    {X : Scheme.{u}} (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
        (DerivedCategory.Qh.obj P)) ≫
      (pinnedPullbackComposition.{u, w} j U.ι).hom.app (DerivedCategory.Qh.obj P) ≫
      (pinnedPullbackCounit.{u, w} (j ≫ U.ι)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopySourceCompositionIso U j).hom.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u, w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P) := by
  sorry

end AlgebraicGeometry
