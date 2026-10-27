/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleBrownProjectionRealization

/-! Derived part of the normalized image realization.

(blueprint: lem-pur-etale-brown-image-realization-derived)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- Construction of the normalized derived direct-image comparison.
Source: Zheng, Lemma 5.16; Stacks 07A4.
(blueprint: lem-pur-etale-brown-image-realization-derived).

The universal right-derived unit determines the comparison and its representative
equation after transport through the supplied Brown realizations.
-/
theorem etaleBrownImageRealization_right_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (ordinaryRight : A.right n ⋙ strictEtaleBrownConstant O t W n ≅
      strictEtaleBrownConstant O t V n ⋙
        Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (hordinary : ∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
      (x : ((A.right n).obj M).val.obj U),
      (ordinaryRight.hom.app M).hom.app U x =
        ((A.rightUnderlying n).hom.app M).hom.app U x) :
    ∃ right : B.direct ⋙ RW.derived n ≅ RV.derived n ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).rightDerivedFunctor,
      (letI := RV.val.ordinaryAdditive
       letI := RW.val.ordinaryAdditive
       ∀ K : CochainComplex (strictEtaleLevel V O t n) ℤ,
         (RW.derived n).map (B.directUnit.app K) ≫
             right.hom.app (DerivedCategory.Q.obj K) ≫
             (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
               g).rightDerivedFunctor.map ((RV.factors n).hom.app K) =
           (RW.factors n).hom.app (((A.right n).mapHomologicalComplex (.up ℤ)).obj K) ≫
             DerivedCategory.Q.map
               ((NatTrans.mapHomologicalComplex ordinaryRight.hom (.up ℤ)).app K) ≫
             strictEtaleBrownRightUnit O t g n
               (((strictEtaleBrownConstant O t V n).mapHomologicalComplex
                 (.up ℤ)).obj K)) := by
  sorry

end AlgebraicGeometry
