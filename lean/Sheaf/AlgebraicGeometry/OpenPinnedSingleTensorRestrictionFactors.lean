/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso

/-! # Single-complex identities for exact restriction and tensor reassociation
Source: Stacks Project, Tags 08DW and 08HY; Mathlib exact single comparison.
(blueprint: lem-pc-open-pinned-single-tensor-restriction-factors). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- Termwise identities specializing the homotopy counit square to singles.
Source: Stacks Project, Tags 08DW and 08HY; Mathlib ExactFunctor.
(blueprint: lem-pc-open-pinned-single-tensor-restriction-factors).
Proof: expand mapDerivedCategorySingleFunctor and mapDerivedCategoryFactorsh.
The quotientCompQhIso factors cancel, leaving Qh applied to the quotient of
singleMapHomologicalComplex for exact restriction; this proves the first
identity. For the second expand the target isomorphism and the homotopy
composition comparisons. Naturality of the restriction factorization moves
the mapped tensor single comparison past it. Naturality of the single
comparison for the tensor restriction isomorphism and its compatibility with
composition identify the rest. In degree zero both paths are the same tensor
restriction map; in every other degree the maps are between zero objects.
Apply the homotopy quotient and Qh and reassociate. The identities use only
additive tensor pullback and exact restriction, without any derived counit. -/
theorem open_pinned_single_tensor_restriction_factors
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) (M : X.Modules) :
    let P := (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := (schemeOpenRestriction X U).obj M
    let qR := (HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (schemeOpenRestriction X U) (.up ℤ) 0).hom.app M)
    let qk := (HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback k) (.up ℤ) 0).hom.app M)
    let qj := (HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback j) (.up ℤ) 0).hom.app H)
    (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map qR =
      ((schemeOpenRestriction X U).mapDerivedCategorySingleFunctor 0).hom.app M ∧
    (schemeOpenRestriction X' U').mapDerivedCategory.map (DerivedCategory.Qh.map qk) ≫
        (openPinnedSingleTargetRestrictionIso k U U' j hj).hom.app M =
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
          ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) ≫
        DerivedCategory.Qh.map
          ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) ≫
        DerivedCategory.Qh.map
          ((Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ) |>.map qR) ≫
        DerivedCategory.Qh.map qj := by sorry

end AlgebraicGeometry
