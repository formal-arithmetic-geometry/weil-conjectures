/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Compact.CompactSupportTargetRationalCoherence
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink

/-! Finite rational geometric comparison before common-stage descent. -/

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

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local irreducible] ScalarLocalization.category HasDerivedCategory.standard
  Padic.coefficientExtensionIntegers rationalDerivedPullback sfRationalScalarExtension
  ObjectProperty.FullSubcategory.category
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage category Shrink.instField Shrink.instAlgebra

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

/-- The rational coefficient comparison expressed in the recorded stage transitions.
Source: the coefficient comparison in the exceptional-adjunction construction
(blueprint: lem-sf-compact-support-target-rational-comparison). -/
def rationalOperationTransition
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem.{u, v} l Ω D hl (f := f))
    (F : FieldSystem.{u, v} l Ω D hl R) (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j) :
    (R.operation c (.rational (commonField.{u, v} l Ω i))).F ⋙ (stageSystem l Ω Y).T hij ≅
      (stageSystem l Ω X).T hij ⋙ (R.operation c (.rational (commonField.{u, v} l Ω j))).F :=
  Functor.isoWhiskerLeft (R.operation c (.rational (commonField.{u, v} l Ω i))).F
      (operationStageTransitionIso l Ω Y i j hij) ≪≫
    (F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{max u v} l Ω i j hij)).q ≪≫
    Functor.isoWhiskerRight (operationStageTransitionIso l Ω X i j hij).symm
      (R.operation c (.rational (commonField.{u, v} l Ω j))).F

/-- Finite rational compact-support comparisons commute with coefficient extension.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence; proper/open comparison and scalar compatibility.
(blueprint: lem-sf-compact-support-target-rational-comparison).

Proof: transport the proper leg of c along e, leaving its open leg fixed.
The normalized proper derived compositor and inverse-image equivalence for e
identify the two proper/open functors. Compare the transported compactification
with c' through a common refinement; the proper/open refinement cocycle makes
this independent of the refinement. Make these maps on the strict positive
quotient systems, where the scalar square is naturality of the proper counit
and open unit. Apply total derived limit to the entire comparison of systems,
including its augmentation and transition maps, to obtain the completed integral
comparison. Its inverse comes from the inverse proper/open comparison on systems.
Localize both maps at the uniformizer. Integral naturality gives rational
naturality on pure tensors, hence on every rational arrow by tensor induction.
The normalized scalar squares persist under localization. Conjugate them by
R.rationalLeft, R'.rationalLeft and the rational normalization equations of F,F'.
This gives exactly the displayed square with the actual stage transitions.
The construction uses no closed-coefficient operation or common-stage descent;
zero inputs, identity target isomorphisms and the first positive quotient use
the same units and counits.
-/
theorem compact_support_target_rational_comparison
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
    (F' : FieldSystem.{u, v} l Ω D hl R') (c' : Compactification g) :
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
                ((rationalOperationTransition l Ω D hl R' F' c' hij).hom.app K) =
          (rationalOperationTransition l Ω D hl R F c hij).hom.app K ≫
            (a j).hom.app (((stageSystem l Ω X).T hij).obj K) := by
  exact compact_support_target_rational_coherence l Ω D hl f g e h R F c R' F' c'
    (fun hij ↦ rationalOperationTransition l Ω D hl R F c hij)
    (fun hij ↦ rationalOperationTransition l Ω D hl R' F' c' hij)
    (fun {i j} hij ↦ rfl) (fun {i j} hij ↦ rfl)

end WeilConjectures.ConstructibleExceptionalCoefficients
