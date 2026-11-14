/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison

/-! # Iterated strict étale inverse-image transitions

Source: Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- The ordinary inverse image respects every normalized iterated transition.
Source: Zheng, Construction 4.1 and Lemma 4.10. -/
theorem strictEtaleInverseTransition (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) (I : StrictEtaleOrdinaryImage O t j)
    (PX : StrictEtaleEvaluation X O t) (PZ : StrictEtaleEvaluation Z O t)
    {m n : ℕ} (h : n ≤ m) (N : strictEtaleCoefficientSystem Z O t) :
    (PX.strictTransition h).app (I.inverse.obj N) ≫
        (coefficientRestriction (J := X.smallEtaleTopology) O t h).map
          ((I.inverseEvaluation n).hom.app N) =
      (I.inverseEvaluation m).hom.app N ≫
        (I.lift m).modules.map ((PZ.strictTransition h).app N) ≫
          (I.restrictInverse h).hom.app (N.level n) := by
  exact SheafOfModules.ordinaryInverseTransition O t _ _ _ I PZ PX h N

end AlgebraicGeometry
