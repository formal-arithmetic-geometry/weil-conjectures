/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCoefficientComputation
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleCompactificationBoundedModels
import all WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility

/-! # Graph-derived boundary equals the inverse normalized compact-support comparison

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-normalization-boundary).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

/-- Graph-derived boundary equals the inverse normalized compact-support comparison.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-normalization-boundary).

Proof: Apply the normalization equation on arbitrary complexes, using the normalization datum for
the sheaf graph comparison and its derived inverse.
The graph normalization theorem identifies the sheaf comparison with the actual graph map. The
acyclic comparison equals the derived unit on these exact compactified models. Substitute these
equalities and expand the model boundary to obtain the required equation. -/
theorem ordinaryChartNormalizationBoundary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (M : EtaleCompactSupportNormalization A)
    (e : X ⟶ Y) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryFactors.hom.app
        P ≫ etaleSumCompactifiedModelBoundary A e c P =
      (M.comparison e c).inv.app (DerivedCategory.Q.obj P) := by
  have h := normalization_complex
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (lowerStar (ModuleCat.{u + 1} A) c.g)
    (M.sheafComparison e c) (M.comparison e c).inv (M.derived_normalization e c) P
  rw [normalization_graph A M e c] at h
  have hu := acyclic_eq_unit (lowerStar (ModuleCat.{u + 1} A) c.g)
    (compactifiedEtaleOpenComplex A c P)
  simpa only [etaleSumCompactifiedModelBoundary, properAcyclicComparison,
    etaleSumCompactifiedComplexMap, hu, Category.assoc,
    compactifiedEtaleOpenComplex, rightDerivedLowerShriekOfCompactification,
    rightDerivedLowerStar, Functor.comp_obj] using h

end AlgebraicGeometry.Etale
