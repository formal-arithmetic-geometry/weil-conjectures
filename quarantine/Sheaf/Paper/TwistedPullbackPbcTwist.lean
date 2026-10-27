/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module
public import Sheaf.Paper.TwistedPullbackPbcCoordinates
public import Sheaf.Paper.TwistedPullbackScalarShifts
public import Sheaf.Paper.PbcCoefficientTwists

/-! # PBC coordinates of the tensor Tate twist

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
tensor/twist constituent of q and z
(blueprint: def-pur-twisted-pullback-pbc-twist-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open Opposite CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Additivity of the specified twist followed by coefficient restriction.
Source: exact tensor with the degree-zero line
(blueprint: def-pur-twisted-pullback-pbc-twist-coordinates). -/
instance twistCoefficientAdditive (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)] (d : ℕ) :
    (integralSheafTwist l E W (d : ℤ) ⋙ fdCoefficientTransport l E W).Additive := by
  have := integralSheafTwist_additive l E W (d : ℤ)
  have := fdCoefficientTransportAdditive l E W
  infer_instance

/-- Additivity of coefficient restriction followed by the actual PBC twist.
Source: exact coefficient relabeling and tensor with the line
(blueprint: def-pur-twisted-pullback-pbc-twist-coordinates). -/
instance coefficientTwistAdditive (W : Scheme.{u})
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    [∀ x : W, Invertible (l : W.residueField x)] (d : ℕ) :
    (fdCoefficientTransport l E W ⋙ pbcTateSheafTensor l W E (d : ℤ)).Additive := by
  have := fdCoefficientTransportAdditive l E W
  have := pbcTateSheafTensor_additive l W E (d : ℤ)
  infer_instance

/-- Identification of the actual PBC twist with the completed tensor twist.
The two scalar restrictions are pinned on every section, so the sheaf comparison
is exactly coefficient relabeling. The derived equation fixes it on every complex,
and beta fixes removal of completion on every good representative.
Source: purity transport, canonical tensor/twist constituent of q and z
(blueprint: def-pur-twisted-pullback-pbc-twist-coordinates). -/
structure TwistCoordinates (W : Scheme.{u}) [IsNoetherian W]
    [dW : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [iW : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    [∀ x : W, Invertible (l : W.residueField x)] (d : ℕ)
    (J : Presentation l E W) (s : ShiftData l E W d) where
  label : fdCoefficientTransport l E W ≅ pbcRestrict (purCoefficientIso l E W).hom
  label_sections : ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U), HEq ((label.hom.app M).val.app U x) x
  roundtrip : fdCoefficientTransport l E W ⋙ purOrdinaryCoefficientModel l E W ≅ 𝟭 _
  roundtrip_sections : ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U), HEq ((roundtrip.hom.app M).val.app U x) x
  sheaf : integralSheafTwist l E W (d : ℤ) ⋙ fdCoefficientTransport l E W ≅
    fdCoefficientTransport l E W ⋙ pbcTateSheafTensor l W E (d : ℤ)
  sheaf_normalization : ∀ M,
    sheaf.app M = label.app ((integralSheafTwist l E W (d : ℤ)).obj M) ≪≫
      (pbcRestrict (purCoefficientIso l E W).hom).mapIso
        ((integralSheafTwist l E W (d : ℤ)).mapIso (roundtrip.app M).symm)
  ambient : (sfIntegralConstructible l E W).ι ⋙ sfIntegralTwistingFunctor l E W (d : ℤ) ⋙
      integralDetailedTransport W l E ≅
    (sfIntegralConstructible l E W).ι ⋙ integralDetailedTransport W l E ⋙
      pbcTateAmbient l W E (d : ℤ)
  derived_normalization : ∀ (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : sfIntegralConstructible l E W (DerivedCategory.Q.obj P)),
    ambient.hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≫
      (pbcTateAmbient l W E (d : ℤ)).map ((fdCoefficientTransportFactors l E W).hom.app P) ≫
      ((pbcTateSheafTensor l W E (d : ℤ)).mapDerivedCategoryFactors.hom.app
        (((fdCoefficientTransport l E W).mapHomologicalComplex (.up ℤ)).obj P)) =
    (integralDetailedTransport W l E).map
        ((integralSheafTwist l E W (d : ℤ)).mapDerivedCategoryFactors.hom.app P) ≫
      (fdCoefficientTransportFactors l E W).hom.app
        (((integralSheafTwist l E W (d : ℤ)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((letI :
          (fdCoefficientTransport l E W ⋙ pbcTateSheafTensor l W E (d : ℤ)).Additive :=
            coefficientTwistAdditive l E W d
        NatTrans.mapHomologicalComplex sheaf.hom (.up ℤ)).app P)
  tensor : integralTwist l E W d ⋙ (sfIntegralConstructible l E W).ι ⋙
      integralDetailedTransport W l E ≅
    (sfIntegralConstructible l E W).ι ⋙ integralDetailedTransport W l E ⋙
      pbcTateAmbient l W E (d : ℤ)
  tensor_normalization : ∀ K,
    tensor.hom.app K = (integralDetailedTransport W l E).map (s.beta K).hom ≫
      ambient.hom.app K
  integral : J.integral.functor ⋙
      pbcConditionalIntegral (pbcIntegralDatum l E) (pbcTateAmbient l W E (d : ℤ))
        (pbcTateAmbient_mem l W E dW.out (d : ℤ)) ≅
    integralTwist l E W d ⋙ J.integral.functor
  integral_lift : ∀ K, HEq (integral.hom.app K).hom (tensor.inv.app K)
  rational : J.rational.functor ⋙
      pbcConditionalRational (pbcIntegralDatum l E) (pbcTateAmbient l W E (d : ℤ))
        (pbcTateAmbient_mem l W E dW.out (d : ℤ)) (pbcUniformizer l E) ≅
    sfRationalTwistingFunctor l E W (d : ℤ) ⋙ J.rational.functor
  rationalization : ∀ K,
    HEq (rational.hom.app ((sfRationalConstructibleLocalization l E W).obj K))
      ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (integral.hom.app K))

end WeilConjectures.TwistedPullbackScalars
