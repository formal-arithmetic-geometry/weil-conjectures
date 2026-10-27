/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleBrownProjectionRealization

/-! Ordinary part of the normalized image realization.

(blueprint: lem-pur-etale-brown-image-realization-ordinary)
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

/-- Construction of the section-normalized ordinary comparison.
Source: Zheng, Construction 5.15; Stacks 03CY and 07A4.
(blueprint: lem-pur-etale-brown-image-realization-ordinary).

The comparison is induced by the ordinary right-underlying comparison and its
section formula. The construction is independent of properness and finiteness.
-/
theorem etaleBrownImageRealization_ordinaryRight_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW) :
    ∃ ordinaryRight : A.right n ⋙ strictEtaleBrownConstant O t W n ≅
        strictEtaleBrownConstant O t V n ⋙
          Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g,
      ∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
        (x : ((A.right n).obj M).val.obj U),
        (ordinaryRight.hom.app M).hom.app U x =
          ((A.rightUnderlying n).hom.app M).hom.app U x := by
  sorry

end AlgebraicGeometry
