/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.CommonStagePullbackNormalizedDescent
import all Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages
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

/-- Canonical transition square for a stagewise rational target comparison.
Source: the final scalar-compatibility paragraph of the exceptional-adjunction
construction (blueprint: lem-sf-compact-support-target-rational-comparison).

Proof: first evaluate the normalized integral proper/open comparison on a strict
positive quotient and use its naturality square. Passing to the completed limit
preserves the square, and localization at the uniformizer preserves both the
components and their composition. Conjugate the localized square by the two
rational-left normalizations. The canonical scalar comparison is exactly the
field-system `rationalComparison` whiskered by the stage-transition isomorphisms;
conjugating the pullback side by `commonStagePullbackTransition` gives the
left-hand composite displayed below. Naturality of each functor map and the
associativity law for composition identify the resulting two paths componentwise.
The supplied family `a` is used at stages `i` and `j`, so this proves the square
for every `hij` and every object `K`.
-/
theorem compact_support_target_rational_canonical_square
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
    (a : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      (R.operation c (.rational (commonField.{u, v} l Ω i))).F ≅
        (R'.operation c' (.rational (commonField.{u, v} l Ω i))).F ⋙
          rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{max u v}
            l Ω i) e.hom)
    : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j)
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
