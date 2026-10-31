/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Compact.CompactSupportTargetRationalCanonicalSquare
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink

/-! Coherence of a stagewise rational compact-support comparison. -/

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

attribute [local irreducible] Compactification.postcomp Compactification.copy
  operationStageTransitionIso commonStagePullbackTransition
  ScalarLocalization.composition ScalarLocalization.preadditive ScalarLocalization.linear
  sfIntegralConstructible sfIntegralConstructibleLinear sfIntegralCoefficientLinear
  Padic.coefficientExtensionUniformizer

/-- The transition square for a stagewise rational target comparison.
Source: the final scalar-compatibility paragraph of the exceptional-adjunction
construction (blueprint: lem-sf-compact-support-target-rational-coherence).

Proof: function extensionality identifies the two transition families with their
canonical comparison composites using hb and hb'. Substitute those equalities,
then apply the existential canonical-square theorem. The family is returned
together with its coherence. No claim is made for arbitrary component isomorphisms.
-/
theorem compact_support_target_rational_coherence
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
    (F' : FieldSystem.{u, v} l Ω D hl R') (c' : Compactification g)
    (b : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j),
      (R.operation c (.rational (commonField.{u, v} l Ω i))).F ⋙
          (stageSystem l Ω Y).T hij ≅
        (stageSystem l Ω X).T hij ⋙
          (R.operation c (.rational (commonField.{u, v} l Ω j))).F)
    (b' : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j),
      (R'.operation c' (.rational (commonField.{u, v} l Ω i))).F ⋙
          (stageSystem l Ω Z).T hij ≅
        (stageSystem l Ω X).T hij ⋙
          (R'.operation c' (.rational (commonField.{u, v} l Ω j))).F)
    (hb : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j),
      b hij =
        Functor.isoWhiskerLeft
            (R.operation c (.rational (commonField.{u, v} l Ω i))).F
            (operationStageTransitionIso l Ω Y i j hij) ≪≫
          (F.rationalComparison c (commonField.{u, v} l Ω i)
            (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j hij)).q ≪≫
          Functor.isoWhiskerRight
            (operationStageTransitionIso l Ω X i j hij).symm
            (R.operation c (.rational (commonField.{u, v} l Ω j))).F)
    (hb' : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j),
      b' hij =
        Functor.isoWhiskerLeft
            (R'.operation c' (.rational (commonField.{u, v} l Ω i))).F
            (operationStageTransitionIso l Ω Z i j hij) ≪≫
          (F'.rationalComparison c' (commonField.{u, v} l Ω i)
            (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j hij)).q ≪≫
          Functor.isoWhiskerRight
            (operationStageTransitionIso l Ω X i j hij).symm
            (R'.operation c' (.rational (commonField.{u, v} l Ω j))).F) :
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
              ((b' hij).hom.app K) =
        (b hij).hom.app K ≫
          (a j).hom.app (((stageSystem l Ω X).T hij).obj K) := by
  have eb : @b = _ := funext fun i ↦ funext fun j ↦ funext fun hij ↦ @hb i j hij
  have eb' : @b' = _ := funext fun i ↦ funext fun j ↦ funext fun hij ↦ @hb' i j hij
  subst b b'
  exact compact_support_target_rational_canonical_square.{u, v}
    l Ω D hl f g e h R F c R' F' c'

end WeilConjectures.ConstructibleExceptionalCoefficients
