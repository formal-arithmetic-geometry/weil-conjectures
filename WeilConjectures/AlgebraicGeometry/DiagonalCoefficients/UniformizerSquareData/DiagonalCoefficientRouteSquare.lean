/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteEquations
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalExtMateSquare

/-! # The proved endpoint criterion for the concrete coefficient routes
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v u' v'
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

attribute [local irreducible] geoCartierConstant geoCartierLine
  quotientLine quotientLineMap cyclicLine cyclicLineMap
  derivedScalars QuotientLineRealization finiteRealizedClass CyclicCartierFrame.reduce
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor Endpoint.shift
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  DerivedCategory.singleFunctorIsoCompQ
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
attribute [local semireducible] CyclicCartierFrame.reduce

/-- The fully proved endpoint criterion specialized to the supplied coefficient
routes. Its four arguments are the independent source comparison, target
comparison, and two realization identities. -/
theorem UniformizerSquareData.endpointSquare
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    (∃! i : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight,
        q.RestrictionNormalized i ∧
          (q.comparison i).app
                ((DerivedCategory.singleFunctor
                    (Modules (Profinite.continuousMapRingObj ℤ_[l]) (diagonalSurface Y)) 0).obj
                  (source (Profinite.continuousMapRingObj ℤ_[l]) Y)) ≫
              q.restriction.mapDerivedCategory.map q.quotientSource.hom ≫
                (q.restriction.mapDerivedCategorySingleFunctor 0).hom.app
                  ((diagonalImmersion Y)_*[ModuleCat A].obj
                    (geoCartierConstant A (ProjectiveLine Y))) =
            q.cyclicSource.hom ≫
              (DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology (diagonalSurface Y))
                  (ModuleCat (diagonalResidue l n))) 0).map q.sourceMap) →
      (∀ i : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight,
          q.RestrictionNormalized i →
            (q.comparison i).app
                  ((shiftFunctor (DerivedCategory
                      (Modules (Profinite.continuousMapRingObj ℤ_[l]) (diagonalSurface Y))) 2).obj
                    ((DerivedCategory.singleFunctor
                        (Modules (Profinite.continuousMapRingObj ℤ_[l]) (diagonalSurface Y)) 0).obj
                      (zlLine l (diagonalSurface Y)))) ≫
                q.restriction.mapDerivedCategory.map q.quotientTarget ≫
                  (q.restriction.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
                      ((DerivedCategory.singleFunctor
                          (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat A)) 0).obj
                        (geoCartierLine A (l ^ (n + 1)) hA (diagonalSurface Y))) ≫
                    (shiftFunctor (DerivedCategory
                        (Sheaf (Scheme.ProEt.topology (diagonalSurface Y))
                          (ModuleCat (diagonalResidue l n)))) 2).map
                      ((q.restriction.mapDerivedCategorySingleFunctor 0).hom.app
                        (geoCartierLine A (l ^ (n + 1)) hA (diagonalSurface Y))) =
              q.cyclicTarget ≫
                (shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology (diagonalSurface Y))
                    (ModuleCat (diagonalResidue l n)))) 2).map
                  ((DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology (diagonalSurface Y))
                      (ModuleCat (diagonalResidue l n))) 0).map q.lineMap)) →
        q.cyclicSource.hom ≫
              Ext.hom (CyclicCartierFrame.reduce l Y n q.cyclic q.route.initial.delta) =
            q.cyclicFunctor.map q.route.initial.delta ≫ q.cyclicTarget →
          q.quotientSource.hom ≫
                Ext.hom
                  (finiteRealizedClass (l ^ (n + 1)) hA Y q.eW q.lineW.endpoint.iso
                    q.sourceComparison.iso q.route.final.delta) =
              q.quotientFunctor.map q.route.initial.delta ≫ q.quotientTarget →
            (Ext.mk₀ q.sourceMap).comp
                (Ext.mapExactFunctor q.restriction
                  (finiteRealizedClass (l ^ (n + 1)) hA Y q.eW q.lineW.endpoint.iso
                    q.sourceComparison.iso q.route.final.delta))
                (zero_add 2) =
              Ext.comp (CyclicCartierFrame.reduce l Y n q.cyclic q.route.initial.delta)
                (Ext.mk₀ q.lineMap) (add_zero 2) :=
  finiteCoefficient_extSquare_of_endpoints q.restriction
    q.cyclicFunctor q.quotientFunctor
    (fun s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight ↦ q.comparison s)
    (fun s ↦ q.RestrictionNormalized s)
    q.cyclicSource q.quotientSource q.cyclicTarget q.quotientTarget
    q.route.initial.delta
    (q.cyclic.reduce l Y n q.route.initial.delta)
    (finiteRealizedClass (L := quotientLine l E π n) (l ^ (n + 1)) hA Y
      q.eW q.lineW.endpoint.iso q.sourceComparison.iso q.route.final.delta)
    q.sourceMap q.lineMap

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
