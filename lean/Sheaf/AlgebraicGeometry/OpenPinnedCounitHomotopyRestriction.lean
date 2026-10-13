/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import Sheaf.AlgebraicGeometry.PinnedPullbackCounitShifts

/-! # Pinned counit restriction on homotopy complexes
Source: Stacks Project, Tags 08DW, 08HY and 0D5S.
(blueprint: lem-pc-open-pinned-counit-homotopy-restriction). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The pinned counit restriction equation for an arbitrary homotopy complex.
Source: Stacks Project, Tags 08DW, 08HY and 0D5S.
(blueprint: lem-pc-open-pinned-counit-homotopy-restriction).
Proof: expand the two composition comparisons in the restricted coefficient.
Their left-derived factorization equations identify their composites with the
pinned counits with the localized underived tensor composition comparisons.
The open-pullback comparison is leftDerivedUnique, so its factorization equation
identifies the open counit with the exact restriction factorization followed by
the underived open tensor comparison. Substituting these identities cancels the
inverse open and composition comparisons. What remains is the image in the
homotopy category of the four factors of openPinnedTensorRestrictionIso.
One can check these equalities on K-flat resolutions, where the counits are
invertible, and descend by their left-derived universal property. No flatness
of P is needed, and empty opens and zero complexes use the same identities. -/
theorem open_pinned_counit_homotopy_restriction
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    singleComplexRestrictedCoefficient k (DerivedCategory.Qh.obj P)
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) (𝟙 _) U U' j hj ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u, w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P) := by sorry

end AlgebraicGeometry
