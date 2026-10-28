/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.Paper.RationalP1ScalarChernMaps
import all Sheaf.Paper.DerivedExchangeExactNormalization
public import Sheaf.Paper.AmbientSquareAssembly
public import Sheaf.Paper.DerivedCalculationInstances
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing


attribute [local instance 30000] cachedModuleClosed
attribute [local instance 30000] CategoryTheory.sheafIsAbelian
attribute [local instance] CondensedRing.pullback_commShift
attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
  condensedAmbientPullbackComparison
attribute [local irreducible] CondensedRing.upperStar Functor.leftDerivedFunctor
  Functor.singleFunctorCompLeftDerivedFunctorIso lineComparison
  CondensedRing.upperStarComp CondensedRing.leftDerivedUpperStarComp
  shiftedLineComparison secondLineComparison
  DerivedCategory.singleFunctors Mod.monoidalClosed Mod.monoidalCategory
  Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.mapDerivedCategory Functor.rightDerivedFunctor


/-- The shifted line square follows from the unshifted comparison equation,
exact single-complex functoriality, and compatibility of the canonical shift.
(blueprint: lem-sfb-shifted-line-square) -/
theorem shifted_line_square
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (condensedAmbientPullbackComparison (coefficient l c).X (square Y)).hom.app
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X Y) 0).obj
          (line l c Y)) ⟦(2 : ℤ)⟧) ≫
        (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).map
          (scalarQLineIso l c k p hpl Y).hom ≫
        (firstLineComparisonForTrace l c k p hpl Y).hom =
      (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y)).map
          (scalarQLineIso l c k p hpl Y).hom ≫
        (secondLineComparison l c k p hpl Y).hom := by sorry
end AlgebraicGeometry.ProEtale.RationalP1


