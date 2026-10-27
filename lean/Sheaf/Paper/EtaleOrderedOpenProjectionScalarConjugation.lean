/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.Paper.ExceptionalCoefficientMaps
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Sheaf.SixFunctors.EtaleOpenTensorDefs
public import Sheaf.SixFunctors.EtaleHomComparisonModels
import Sheaf.SixFunctors.EtaleOpenScalarCoherence
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- The ordered scalar square after postcomposition by the signed symmetry.
Source: Stacks 0E8I, 0GL6 and 07A4
(blueprint: lem-pur-etale-ordered-open-projection-scalar-postcomp).

The mixed scalar/open equation is transported through the normalized open and tensor
comparisons, then conjugated by the signed tensor symmetries.  Both routes agree on
flat K-flat representatives by the degree-zero scalar balancing formula and the
Koszul sign; localization and naturality extend this postcomposed equality to all
inputs.  The final symmetry is an isomorphism, so the original equation is recovered
by cancellation in the item theorem. -/
theorem etaleOrderedOpenProjectionScalar_postcomp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (T : DerivedCategoryModule A Z) (M : DerivedCategoryModule A X)
    (oA : ((derivedTensor (ModuleCat.{u + 1} A) Z).obj T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T)).obj M))
    (oB : ((derivedTensor (ModuleCat.{u + 1} B) Z).obj ((scalarExtension φ Z).obj T)).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
          ((scalarExtension φ X).obj M)) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} B) X).obj
          ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
            ((scalarExtension φ Z).obj T))).obj ((scalarExtension φ X).obj M)))
    (h : canonicalGammaExact (ModuleCat.{u + 1} B) j
          ((scalarExtension φ X).obj M) ((scalarExtension φ Z).obj T) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) Z).map
          ((openScalarExtension φ j).inv.app M)).app ((scalarExtension φ Z).obj T) ≫
        (etaleHomTensorComparison Z φ ((derivedExtension j).obj M) T).hom =
      (derivedExtension (A := B) j).map
          (((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
              ((openScalarRestriction φ j).inv.app T) ≫
            (etaleHomTensorComparison X φ M ((derivedRestriction j).obj T)).hom) ≫
        (openScalarExtension φ j).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
            ((derivedRestriction j).obj T)) ≫
        (scalarExtension φ Z).map (canonicalGammaExact (ModuleCat.{u + 1} A) j M T)) :
    ((scalarExtension φ Z).map oA ≫
      (ExceptionalCoefficients.openIso φ j).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T)).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((ExceptionalCoefficients.tensorIso φ X).hom.app
            ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T, M) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) X).map
            ((scalarPullbackIso φ j).inv.app T)).app ((scalarExtension φ X).obj M))) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
            ((scalarExtension φ Z).obj T))).app ((scalarExtension φ X).obj M)) =
    ((ExceptionalCoefficients.tensorIso φ Z).hom.app
        (T, (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) Z).obj
        ((scalarExtension φ Z).obj T)).map
          ((ExceptionalCoefficients.openIso φ j).hom.app M) ≫
      oB) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
            ((scalarExtension φ Z).obj T))).app ((scalarExtension φ X).obj M)) := by
  sorry
end AlgebraicGeometry.Etale
