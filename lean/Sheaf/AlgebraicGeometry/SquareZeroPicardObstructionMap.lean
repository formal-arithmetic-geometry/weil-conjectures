module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Sheaf.AlgebraicGeometry.SquareZeroUnitsBoundary
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-! # The canonical square-zero Picard obstruction map

Source: Stacks Project, More on Morphisms, Tag 0C6R, proof, and Cohomology, Tag 03FD
(blueprint: def-sfb-square-zero-picard-obstruction-map).

The ideal on the closed subscheme is the tensor pullback of the defining ideal.
The map is the boundary of the units sequence, normalized by `a ↦ 1 + a`, transported
by the canonical closed-immersion and resolution comparisons to ordinary module cohomology.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.RingedSpace.moduleCohomology
attribute [local irreducible]
  AlgebraicGeometry.Scheme.unitsPushforwardCohomologyComparison
  AlgebraicGeometry.Scheme.Pic.toH1UnitsAddEquiv

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The normalized module-cohomology comparison for the ideal, Stacks Tag 03FD.
(blueprint: def-sfb-square-zero-picard-obstruction-map). -/
noncomputable def squareZeroIdealModuleCohomology {Z X : Scheme.{u}} (j : Z ⟶ X) :
    Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj j.ker.toModules) 2 ≃+
      (RingedSpace.moduleCohomology X.toRingedSpace 2).obj j.ker.toModules :=
  (Modules.moduleCohomologyExtResolutionEquiv X j.ker.toModules 2).symm

/-- The canonical map to cohomology on the thickening's closed subscheme, Stacks 0C6R.
(blueprint: def-sfb-square-zero-picard-obstruction-map). -/
noncomputable def squareZeroIdealCohomologyPullback {Z X : Scheme.{u}} (j : Z ⟶ X) :
    (RingedSpace.moduleCohomology X.toRingedSpace 2).obj j.ker.toModules →+
      (RingedSpace.moduleCohomology Z.toRingedSpace 2).obj
        ((Modules.tensorPullback j).obj j.ker.toModules) :=
  (Modules.moduleCohomologyFMap j
    ((Modules.tensorPullbackSectionAdjunction j).unit.app j.ker.toModules) 2).hom

attribute [local irreducible] squareZeroIdealModuleCohomology squareZeroIdealCohomologyPullback
  squareZeroUnitsBoundary squareZeroUnitsIdealCohomology

/-- The composite defining the obstruction, Stacks 0C6R.
(blueprint: def-sfb-square-zero-picard-obstruction-map). -/
noncomputable def squareZeroPicardObstructionFun {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) (L : Additive Z.Pic) :
    (RingedSpace.moduleCohomology Z.toRingedSpace 2).obj
      ((Modules.tensorPullback j).obj j.ker.toModules) :=
  letI : IsClosedImmersion j := hj.1
  squareZeroIdealCohomologyPullback j (squareZeroIdealModuleCohomology j
    (squareZeroUnitsIdealCohomology j hj (squareZeroUnitsBoundary j hj
      (Function.surjInv
        (bijective_unitsPushforwardCohomologyComparison_of_isClosedImmersion j 1).2
        (Pic.toH1UnitsAddEquiv Z L)))))

attribute [local irreducible] squareZeroPicardObstructionFun

/-- Additivity of the explicitly constructed obstruction function.
Source: Stacks Project, Tag 0C6R, exact sequence of abelian groups
(blueprint: def-sfb-square-zero-picard-obstruction-map).

Proof: Hilbert 90 is additive. The closed-immersion comparison is an additive bijection,
so its inverse preserves zero and addition. The Yoneda boundary, the map induced by
1+a, the resolution comparison, and the tensor-unit cohomology map are all additive.
Compose these identities to obtain the zero and addition identities below. -/
theorem squareZeroPicardObstructionFun_additive {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) :
    squareZeroPicardObstructionFun j hj 0 = 0 ∧
      ∀ L M : Additive Z.Pic,
        squareZeroPicardObstructionFun j hj (L + M) =
          squareZeroPicardObstructionFun j hj L + squareZeroPicardObstructionFun j hj M := by
  sorry

/-- The canonical Picard obstruction, with ordinary module cohomology as target.
The ideal on Z is j*I = I/I², canonically I with its quotient O_Z-action since I²=0.
Compose Hilbert 90, the inverse closed-immersion comparison, the Yoneda boundary of the
units sequence, the inverse of a ↦ 1+a, the resolution-normalized comparison with module
cohomology, and module cohomology pullback along the section-normalized tensor unit.
Source: Stacks Project, Tag 0C6R, middle and final rows and proof; Tag 03FD
(blueprint: def-sfb-square-zero-picard-obstruction-map). -/
noncomputable def squareZeroPicardObstruction {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) :
    Additive Z.Pic →+
      (RingedSpace.moduleCohomology Z.toRingedSpace 2).obj
        ((Modules.tensorPullback j).obj j.ker.toModules) where
  toFun := squareZeroPicardObstructionFun j hj
  map_zero' := (squareZeroPicardObstructionFun_additive j hj).1
  map_add' := (squareZeroPicardObstructionFun_additive j hj).2

end AlgebraicGeometry.Scheme
