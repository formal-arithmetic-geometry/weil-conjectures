/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.Integral.IntegralPositiveReductionConstructible
import WeilConjectures.AlgebraicGeometry.Integral.IntegralReductionUnderlyingDirectImage
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Classical models for finite integral reductions and their proper images -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private noncomputable def encodingForgetIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A X) :
    (e.ordinary.functor ⋙ e.fixed.functor) ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ≅
      Mod.forget (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X) := by
  rw [e.ordinary_functor, e.fixed_functor]
  exact NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by rfl)

end AlgebraicGeometry.ProEtale
