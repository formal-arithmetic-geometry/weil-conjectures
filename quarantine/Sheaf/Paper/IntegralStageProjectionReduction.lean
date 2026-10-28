/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Paper.ConstructibleProjectionMates
import Sheaf.Paper.ConcreteIntegralProjectionCone
import Sheaf.Paper.IntegralProjectionOperationPresentation
import Sheaf.Paper.FiniteProjectionOperationPresentation

/-! # Finite reduction of the normalized integral-stage projection

Source: the reduction and adic reconstruction steps of the compact-support
projection formula (blueprint: lem-sf-integral-stage-projection-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

/-- Reduction of the specified integral projection is conjugate to the specified
finite projection. This comparison asserts no invertibility of either projection.
Source: fix-prop-projection-formula.proof.md, the successive-reduction and adic
reconstruction sentences; lem-sf-projection-integral-stage-laws, proof step 1.
(blueprint: lem-sf-integral-stage-projection-reduction).

Proof: choose ordinary tensor models using the proved tensorModel_exists.
The integral operation-presentation comparison gives an arrow isomorphism to the
completed ordinary integralMap. Apply reduction.mapArrow to this isomorphism.
The concrete integral projection cone theorem supplies invertible source and
target comparisons and their commuting reduction square. Arrow.isoMk turns this
square into an isomorphism to the concrete finiteArrow. The finite operation-
presentation comparison identifies that arrow with the prescribed finite
component after rewriting the underlying second input by hLₘ. Compose the three
arrow isomorphisms. The main proof assumes neither projection is invertible.
The argument includes arbitrary integral bounded constructible first inputs,
every positive exponent m+1, zero inputs and empty schemes. -/
theorem integralStageProjection_reduction
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (_hL : S.integralFiniteTorDomain Y L) (m : ℕ)
    (Lₘ : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left)
    (hLₘ : Lₘ.obj = ((sixFunctorIntegralReduction D C E m Y).obj L).obj) :
    Nonempty (Arrow.mk
      ((scalarReductionDerivedExtension C.l E Y.obj.left m).map
        (compactSupportProjectionComponent S.higher.integralExchange f c K L).hom) ≅
      Arrow.mk (CompactSupportFiniteProjection.component
        (S.integralNormalization.finiteLevels m) f c
        ((sixFunctorIntegralReduction D C E m X).obj K) Lₘ).hom) := by
  obtain ⟨aX⟩ := PurCompactSupport.tensorModel_exists X.obj.left
    ((PurCompactSupport.completed C.l E).ring X.obj.left)
  obtain ⟨aZ⟩ := PurCompactSupport.tensorModel_exists c.Z
    ((PurCompactSupport.completed C.l E).ring c.Z)
  obtain ⟨aY⟩ := PurCompactSupport.tensorModel_exists Y.obj.left
    ((PurCompactSupport.completed C.l E).ring Y.obj.left)
  obtain ⟨eIntegral⟩ := integralProjection_operationPresentation S.higher f c aX aZ aY K L
  have hcone := ConcreteIntegralProjection.concreteIntegralProjectionCone C.l E c D
    C.different C.Qbar n hn S aX aZ aY K L _hL
  obtain ⟨hUnit, hReduction, _⟩ := hcone.2.2.2.2.2.2
  obtain ⟨hSource, hTarget, hSquare⟩ := hReduction m
  have := hSource
  have := hTarget
  let eReduction : Arrow.mk
      ((scalarReductionDerivedExtension C.l E Y.obj.left m).map
        (SfProEtaleProjection.integralMap C.l E D C.different f.hom.left c
          aX aZ aY K L).hom) ≅
      ConcreteIntegralProjection.finiteArrow C.l E c K.obj L.obj m := Arrow.isoMk
    (asIso (ConcreteIntegralProjection.sourceComparison C.l E c D C.different aX aY K L m))
    (asIso (ConcreteIntegralProjection.targetComparison C.l E c aX K.obj L.obj m
      (hUnit m))) hSquare.symm
  obtain ⟨eFinite⟩ := finiteProjection_operationPresentation
    (S.integralNormalization.finiteLevels m) f c
    ((sixFunctorIntegralReduction D C E m X).obj K) Lₘ
  have hFinite : ConcreteIntegralProjection.finiteArrow C.l E c K.obj L.obj m =
      Arrow.mk (finiteReductionProjection C.l E m c
        ((sixFunctorIntegralReduction D C E m X).obj K).obj Lₘ.obj) := by
    exact congrArg (fun T ↦ Arrow.mk (finiteReductionProjection C.l E m c
      ((sixFunctorIntegralReduction D C E m X).obj K).obj T)) hLₘ.symm
  exact ⟨(scalarReductionDerivedExtension C.l E Y.obj.left m).mapArrow.mapIso eIntegral ≪≫
    eReduction ≪≫ eqToIso hFinite ≪≫ eFinite⟩

end WeilConjectures
