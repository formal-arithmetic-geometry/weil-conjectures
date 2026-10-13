/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData

/-! # Restriction of the pinned single tensor counit
Source: Stacks Project, Tags 08DW, 08IB and 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The degree-zero counit selected by the pullback composition structure.
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit). -/
def openPinnedSingleDegreeZeroCounit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) :
    (derivedPullback k).obj ((DerivedCategory.singleFunctor.{w} _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor.{w} _ 0).obj ((Scheme.Modules.tensorPullback k).obj M) :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback k) (ComplexShape.up ℤ) 0).hom.app M))

/-- Restriction of the pinned counit, before applying any direct image.
Source: Stacks Project, Tags 08DW, 08IB and 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit).
Proof: compare the tensor pullback of a restricted module with restriction of its
pullback by the underived composition comparisons and uniqueness of open pullback
as left adjoint to pushforward. Apply the exact single-complex restriction
comparison. On K-flat representatives the pinned left-derived counit is the
localization of this underived tensor map. Its factorization equation, and the
factorization equations for the pinned composition comparisons and the constructed
open-pullback isomorphisms, identify the two paths. Thus the equality holds before
localization and descends. The source path is exactly the constructed
singleComplexRestrictedCoefficient with the identity coefficient map. Every factor is natural in M,
so the target comparisons
assemble to a natural isomorphism. The construction applies to empty opens and zero
modules, with no flatness assumption on M. -/
theorem open_pinned_single_degree_zero_counit_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) :
    ∃ t : (Scheme.Modules.tensorPullback k ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0) ⋙
          (schemeOpenRestriction X' U').mapDerivedCategory ≅
        schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j ⋙
          DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace)) 0,
      ∀ M : X.Modules,
        let K := (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
        let H := (schemeOpenRestriction X U).obj M
        let s := ((schemeOpenRestriction X U).mapDerivedCategorySingleFunctor 0).hom.app M
        singleComplexRestrictedCoefficient k K ((derivedPullback k).obj K)
            (𝟙 _) U U' j hj ≫
          (schemeOpenRestriction X' U').mapDerivedCategory.map
            (openPinnedSingleDegreeZeroCounit k M) ≫ t.hom.app M =
          (derivedPullback j).map s ≫ openPinnedSingleDegreeZeroCounit j H := by sorry

end AlgebraicGeometry
