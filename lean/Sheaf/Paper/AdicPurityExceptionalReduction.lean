/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicPurityObjects
public import Sheaf.Paper.ExceptionalDerivedSiteRealization
/-! # Canonical finite reduction of the integral exceptional inverse image
Source: blueprint thm-pur-adic-reconstruction, canonical target reduction.
(blueprint: def-pur-adic-exceptional-reduction).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Evaluation of the actual exceptional system in fixed finite coefficients.
Every factor is a coordinate counit, normalized site comparison, or the mate of the
specified compact-support comparison. Source: blueprint target normalization
(blueprint: def-pur-adic-exceptional-reduction). -/
def purAdicExceptionalEvaluation
    (K : DerivedCategory (scalarReductionSource C.l E Y)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation C.l E X n).obj
      ((integralExceptionalSystem C.l E D C.different f).obj K) ≅
    (Scheme.sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E (n +
      1))).functor.obj
      (((purAdicFiniteSetting D C E n).smoothPurityExceptionalOver f
        (Y ↘ Spec (.of D.k))).obj
          ((Scheme.sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing C.l E (n +
            1))).inverse.obj
            ((scalarReductionDerivedExtension C.l E Y n).obj K))) :=
  letI := hasCompactification_of_finiteType_over_field D.k X Y f
  let P := purAdicFiniteSetting D C E n
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f P.Coefficient
  let S := integralExceptionalSupport C.l E D C.different f
  let G := integralExceptionalAdjoint C.l E D C.different f
  let BX := integralExceptionalComparison C.l E X S.PX
  let BY := integralExceptionalComparison C.l E Y S.PY
  let RY := (integralExceptionalEtaleRealization C.l E Y n).mapDerivedCategory
  let RX := (integralExceptionalEtaleRealization C.l E X n).mapDerivedCategory
  let NX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let DY := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let H := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f
  let input := (integralExceptionalDerivedCoordinates C.l E Y).obj
    ((pullbackTensorCalculus C.l E Y).reduction.obj K)
  let A := BY.derived.system.direct.obj input
  let B := G.right.obj A
  let N := BX.derived.system.inverse.obj B
  let eY := RY.mapIso ((BY.derived.directEvaluation n).app input) ≪≫
    (integralExceptionalSiteDerivedRight C.l E Y S.PY BY n).app _ ≪≫
    DY.mapIso (integralExceptionalCoordinatesFixed C.l E Y BY.evaluation
      ((pullbackTensorCalculus C.l E Y).reduction.obj K) n ≪≫
      (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.mapIso
        (((pullbackTensorCalculus C.l E Y).reductionEvaluation n).app K))
  let eX := integralExceptionalCoordinatesInvFixed C.l E X BX.evaluation N n ≪≫
    (integralExceptionalProRealization C.l E X n).mapDerivedCategory.mapIso
      ((BX.derived.inverseEvaluation n).app B) ≪≫
    (integralExceptionalSiteDerivedInverse C.l E X S.PX BX n).app _ ≪≫
    NX.mapIso (RX.mapIso ((G.evaluation n).app A) ≪≫
      (integralExceptionalEtaleRightAdjoint C.l E f (integralExceptionalCompactification D f)
        S n G H (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f)).app
          _ ≪≫
      H.mapIso eY)
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).counitIso.symm.app _ ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso eX

/-- The target reduction map b^V_n is the actual limit/reduction counit, followed
by the normalized evaluation comparison. No isomorphism of arbitrary endpoints is
chosen. Source: blueprint target normalization (blueprint: def-pur-adic-exceptional-reduction). -/
def purAdicTargetReduction (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    (scalarReductionDerivedExtension C.l E X n).obj (purAdicTarget D C E f K) ⟶
      (purAdicFiniteArrow D C E f d K hK n).right :=
  ((pullbackTensorCalculus C.l E X).reductionEvaluation n).inv.app _ ≫
    (coefficientSequenceDerivedEvaluation C.l E X n).map
      ((pullbackTensorCalculus C.l E X).adjunction.counit.app
        ((integralExceptionalSystem C.l E D C.different f).obj K)) ≫
    (purAdicExceptionalEvaluation D C E f K n).hom
end WeilConjectures
