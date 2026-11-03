/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink

/-! # Coefficient-compatible transport of one proper leg

Source: the exceptional-adjunction paragraph of the current blueprint,
cor-coef-verdier-weil-equivariance.proof.md.
(blueprint: lem-sf-compact-support-rational-target-transport) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
open GeneralAlgebraicallyClosedCoefficients

/-- Coefficient-compatible target transport with the compactification held fixed.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence and its proper/open realization
(blueprint: lem-sf-compact-support-rational-target-transport).

Proof: on every strict positive quotient use the derived proper compositor for
c.g followed by e and the inverse-image/direct-image equivalence of e. Whisker by
the unchanged open extension. Its scalar square is naturality of the proper
counit and the coefficient pullback map; no common refinement occurs. Apply the
completed system realization and then localize at the uniformizer. The object
representatives remain integral representatives; functoriality preserves the square,
and tensor induction proves naturality on rational Hom groups. Conjugate by the
rational-left realizations of R and R'; their scalar normalizations and the
normalized pullback comparison identify the square with the one below. Identity
target isomorphisms, empty schemes and zero objects use the same compositors.
Unlike a claim for an arbitrary family, this is an existence statement for the
family produced by this single proper-leg construction. -/
theorem compact_support_rational_target_transport
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y Z : Scheme.{max u v}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Y ≅ Z) (h : f ≫ e.hom = g)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (R : RingSystem.{u, v} l Ω D hl (f := f))
    (F : FieldSystem.{u, v} l Ω D hl R) (c : Compactification f)
    (R' : RingSystem.{u, v} l Ω D hl (f := g))
    (F' : FieldSystem.{u, v} l Ω D hl R') :
    let c' := (c.postcomp e.hom).copy h.symm
    ∃ a : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      (R.operation c (.rational (commonField.{u, v} l Ω i))).F ≅
        (R'.operation c' (.rational (commonField.{u, v} l Ω i))).F ⋙
          rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{max u v}
            l Ω i) e.hom,
      ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))),
      ((stageSystem l Ω Y).T hij).map ((a i).hom.app K) ≫
          (commonStagePullbackTransition l Ω e.hom hij).hom.app
            ((R'.operation c' (.rational (commonField.{u, v} l Ω i))).F.obj K) ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{max u v} l Ω j) e.hom).map
              ((Functor.isoWhiskerLeft
                (R'.operation c' (.rational (commonField.{u, v} l Ω i))).F
                (operationStageTransitionIso l Ω Z i j hij) ≪≫
              (F'.rationalComparison c' (commonField.{u, v} l Ω i)
                (commonField.{u, v} l Ω j)
                (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j hij)).q ≪≫
              Functor.isoWhiskerRight
                (operationStageTransitionIso l Ω X i j hij).symm
                (R'.operation c' (.rational (commonField.{u, v} l Ω j))).F).hom.app K) =
        (Functor.isoWhiskerLeft
            (R.operation c (.rational (commonField.{u, v} l Ω i))).F
            (operationStageTransitionIso l Ω Y i j hij) ≪≫
          (F.rationalComparison c (commonField.{u, v} l Ω i)
            (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j hij)).q ≪≫
          Functor.isoWhiskerRight
            (operationStageTransitionIso l Ω X i j hij).symm
            (R.operation c (.rational (commonField.{u, v} l Ω j))).F).hom.app K ≫
          (a j).hom.app (((stageSystem l Ω X).T hij).obj K) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
