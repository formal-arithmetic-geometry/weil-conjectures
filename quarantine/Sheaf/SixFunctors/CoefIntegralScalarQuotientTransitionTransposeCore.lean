/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefScalarReductionExchange
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels

/-! # Core mate calculation for scalar quotient transitions

Source: current blueprint, lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

attribute [local irreducible] scalarReductionDerivedExtension
  integralScalarExtensionOfUniverses quotient normalizedDVRReductionTransition
  scalarReductionExchange

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The residual finite reduction comparison, with the completion transport removed.

This is the finite tensor and reduction part of the transpose calculation.  The
remaining mate calculation is supplied by the theorem below.  It is separated
from the completion isomorphism because the latter is handled by adjunction
naturality in the parent theorem.

Source: lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose-core)
-/
def quotientResidual (K : IntegralVerdier.Ambient l E X) (j : ℕ) :
    (scalarReductionDerivedExtension l L X j).obj
        ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K) ≅
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X j)).obj
        ((scalarReductionDerivedExtension l E X j).obj K) :=
  (PurCompactSupport.finiteReductionIso l L X j).symm.app _ ≪≫
    (PurCompactSupport.tensorSquare (completedCoefficientMap l E L ι X)
      (integralScalarQuotientSheafMap l E L ι X j)
      (completedIntegralCommRingProjectionUnrestricted l E X j)
      (completedIntegralCommRingProjectionUnrestricted l L X j)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec j)).app K ≪≫
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X j)).mapIso
      ((PurCompactSupport.finiteReductionIso l E X j).app K)

/-- The residual mate identity used after exposing completion naturality.

It is the coefficient restriction square calculation: expand the quotient
comparison into the finite reduction isomorphisms and tensor square, use the
unit/counit triangles for the normalized adjunctions, and use the defining mate
identity of `scalarReductionExchange`.  This is strictly below the displayed
transpose theorem because completion transport has already been removed.

Source: lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose-core)
-/
theorem quotient_reduction_transition_transpose_core
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K)
    {m n : ℕ} (h : n ≤ m) :
    (completion l E L ι X K hK).inv ≫
        (normalizedDVRIntegralAdjunction l L X m).homEquiv
          ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K)
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
            normalizedDVRRes l L X h).obj ((scalarReductionDerivedExtension l E X n).obj K))
          ((quotientResidual l E L ι X K m).hom ≫
            (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
              (normalizedDVRReductionTransition l E X D hl h K) ≫
            (scalarReductionExchange l E L ι X h).app
              ((scalarReductionDerivedExtension l E X n).obj K)) =
      (normalizedDVRIntegralAdjunction l L X n).unit.app
          ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
        (normalizedDVRIntegralAdjunction l L X m).homEquiv
          ((scalarReductionDerivedExtension l L X n ⋙
            scalarReductionDerivedRestriction l L X n).obj
              ((integralScalarExtensionOfUniverses l E L ι X).obj K))
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
            normalizedDVRRes l L X h).obj ((scalarReductionDerivedExtension l E X n).obj K))
          ((scalarReductionDerivedExtension l L X m).map
              ((normalizedDVRResCompletedComp l L X D hl h).inv.app
                ((scalarReductionDerivedExtension l L X n).obj
                  ((integralScalarExtensionOfUniverses l E L ι X).obj K))) ≫
            (normalizedDVRIntegralAdjunction l L X m).counit.app
              ((normalizedDVRRes l L X h).obj
                ((scalarReductionDerivedExtension l L X n).obj
                  ((integralScalarExtensionOfUniverses l E L ι X).obj K))) ≫
            (normalizedDVRRes l L X h).map
              ((scalarReductionDerivedExtension l L X n).map (completion l E L ι X K hK).inv ≫
                (quotientResidual l E L ι X K n).hom)) := by
  sorry

end WeilConjectures.IntegralFiniteExtension
