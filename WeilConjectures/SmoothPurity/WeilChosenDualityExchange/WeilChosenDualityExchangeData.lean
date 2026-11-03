/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PodConstructibleMate.ConstructibleMateCoherence
public import WeilConjectures.SixFunctors.CompactSupportPbcTransport.CompactSupportProjectionFormula
public import WeilConjectures.SixFunctors.CoefVerdierWeil.CoefVerdierWeilData
import WeilConjectures.PoincareDuality.SemilinearFieldOperationLifts
import WeilConjectures.SixFunctors.SemilinearFieldOperationLiftsLegacy
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
/-! # Interfaces for specified Weil exchange

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md;
thm-sf-verdier-exchange.proof.md, Step 1; lem-sf-tensor-hom.proof.md, Step 1
(blueprint: lem-sf-weil-chosen-duality-exchange).

The operation datum and its normalized common-stage lifts fix the operations.
The conclusion supplies the full constructible Hom domains and the restrictions
of the original adjunctions. All subsequent choices of structure right adjoints
are arbitrary. The displayed transposes are defined from the specified maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c va vb vc
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
namespace WeilConjectures.WeilChosenDualityExchange
open PodConstructibleMate

section Geometric
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

/-- The model point, in the already existing finite-type model category.
Source: cor-coef-verdier-weil-equivariance.proof.md, structure morphisms
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def point : Models D :=
  ⟨CoefVerdierWeil.pointModel D, inferInstance, inferInstance⟩

/-- The original carrier category, with no completion or new objects.
Source: common-stage coefficient convention
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
abbrev Carrier (X : Models D) :=
  generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar (D.geometricFiber X.obj).left

/-- The existing fixed-pair category; commonFrobenius is the named standard pullback.
Source: def-weil-weil-sheaf-complex
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
abbrev Pair (X : Models D) := IsoAlgebra (commonFrobenius D C X)

variable {D C}
variable {A : CommonStage D C} (L : CommonLifts D C A)

/-- The standard coefficient pair at the model point. Its underlying constant
object is fixed, and the Frobenius isomorphism is normalized by the tensor unit.
Source: cor-coef-verdier-weil-equivariance.proof.md, dualizing object paragraph
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
structure Constant where
  theta : (sfCommonStageWeilFrobeniusPullback D C.l C.different
      (CoefVerdierWeil.pointModel D) C.Qbar).obj
        (CoefVerdierWeil.commonUnit D C.l C.different C.Qbar
          (CoefVerdierWeil.pointModel D)) ≅
    CoefVerdierWeil.commonUnit D C.l C.different C.Qbar (CoefVerdierWeil.pointModel D)
  normalized (M : Carrier D C (point D)) :
    (CoefVerdierWeil.commonMu D C.l C.different C.Qbar (CoefVerdierWeil.pointModel D)
      (CoefVerdierWeil.commonUnit D C.l C.different C.Qbar
        (CoefVerdierWeil.pointModel D)) M).hom ≫
      (@commonStageDerivedTensor C.l _ C.Qbar _ _ _
        (D.geometricFiber (CoefVerdierWeil.pointModel D)).left
        (fun x ↦ sfWeilPrimeInvertible D C.l C.different
          (CoefVerdierWeil.pointModel D) x)).map
        (Prod.mkHom theta.hom (𝟙 _)) ≫
      (CoefVerdierWeil.commonUnitor D C.l C.different C.Qbar
        (CoefVerdierWeil.pointModel D)
        ((sfCommonStageWeilFrobeniusPullback D C.l C.different
          (CoefVerdierWeil.pointModel D) C.Qbar).obj M)).hom =
    (sfCommonStageWeilFrobeniusPullback D C.l C.different
      (CoefVerdierWeil.pointModel D) C.Qbar).map
        (CoefVerdierWeil.commonUnitor D C.l C.different C.Qbar
          (CoefVerdierWeil.pointModel D) M).hom

/-- The coefficient pair with its normalized constant structure.
Source: dualizing-object convention
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def Constant.pair (U : Constant (D := D) (C := C)) : Pair D C (point D) := by
  unfold Pair commonFrobenius point
  exact IsoAlgebra.mk _ U.theta

variable (D C)
variable (A : SixFunctorCommonStages D C) (W : CommonLifts D C A.commonStage)
variable (X Y : Models D) (f : X ⟶ Y)
variable (cf : Compactification f.hom.left)
variable (cy : Compactification (structureMap D Y).hom.left)
variable (cx : Compactification (f ≫ structureMap D Y).hom.left)

end Geometric
end WeilConjectures.WeilChosenDualityExchange
