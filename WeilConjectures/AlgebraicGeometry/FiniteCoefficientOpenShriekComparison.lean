/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek

/-! # Extension by zero under the canonical finite coefficient equivalence
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]

private def openShriekFiniteCoefficientModEquivalenceIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj A) j ⋙
        (finiteCoefficientModEquivalence X A).functor ≅
      (finiteCoefficientModEquivalence U A).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let EX := finiteCoefficientModEquivalence X A
  let EU := finiteCoefficientModEquivalence U A
  let i := upperStarFiniteCoefficientModEquivalenceIso j A
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EX) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (Profinite.continuousMapRingObj A) j).comp EX.toAdjunction
  let b := EU.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- The canonical finite coefficient equivalence commutes with derived open extension. -/
theorem finiteCoefficientDerivedOpenShriekComparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (
      (CondensedRing.openImmersionLowerShriek
        (Profinite.continuousMapRingObj A) j).mapDerivedCategory ⋙
          (finiteCoefficientDerivedEquivalence X A).functor ≅
        (finiteCoefficientDerivedEquivalence U A).functor ⋙
          (openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory) := by
  exact ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (openShriekFiniteCoefficientModEquivalenceIso A j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm⟩

end AlgebraicGeometry.ProEtale
