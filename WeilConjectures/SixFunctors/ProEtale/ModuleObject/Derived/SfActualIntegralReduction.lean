/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SfNativeDerivedMonoidal
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients

/-! # The actual integral quotient scalar functor, constructed once
Source: thm-sf-biduality-class, integral coefficient reduction.
(blueprint: def-sf-actual-integral-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 50000] sfNativeDerivedMonoidal sfNativeCoefficientComm
  sfNativeTensorFour sfNativeGoodTensor12 sfNativeGoodTensor23
  sfNativeTensorLeftInt sfNativeTensorRightInt sfNativeFlatResolution sfNativeScalarsKFlat
  sfNativeModuleClosed sfNativeModuleBraided

/-- Actual reduction along the pi^(m+1) quotient, transported by the specified
integral coefficient isomorphism and pulled back to X.
Source: thm-sf-biduality-class, integral paragraph
(blueprint: def-sf-actual-integral-reduction).
Construct the given composite monoid map and apply the existing K-flat derived
scalar extension. This names its full data once and makes no new choice. -/
def sfActualIntegralReduction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1))
    (X : Scheme.{u}) (m : ℕ) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj
          (Profinite.continuousMapRingObj (completedResidue ℓ E π m)) X)) :=
  sfNativeDerivedScalars Λ
    (Profinite.continuousMapRingObj (completedResidue ℓ E π m)) X
    ((upperStarFromPoint X).map
      (e.hom.hom ≫ (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (completedReduction ℓ E π m)))


end AlgebraicGeometry.ProEtale.CondensedRing
