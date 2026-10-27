/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.PodReconstructionCommonStageData
/-! # Normalization of the actual finite-stage scalar comparisons

Source: blueprint opening sentence of lem-pod-point-dualizing-complex.proof.md.
(blueprint: lem-pod-reconstruction-scalar-realizations).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PodCommonStageReconstruction
open PodCompletionScalar PodRawReconstruction
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem stageTransition integralTransition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (A : ∀ E : Index l Ω,
    CoefficientDerivedSystemCalculus l (Coefficient.{u} l Ω E) (point D))

/-- The same-index quotient-cone scalar comparison can be normalized simultaneously
against any fixed family of the actual integral and raw rational reconstructions.
Source: blueprint opening sentence, Step 1 of common-stage coherence;
Bhatt--Scholze, Definitions 3.5.2--3.5.3, Lemmas 3.5.7 and 6.8.2(1).
(blueprint: lem-pod-reconstruction-scalar-realizations).

Proof: For each inclusion E ≤ L use completionUnitScalarIntertwining to construct
the quotient-model chain map with its specified same-index residue formula and
both signed Roos coordinates. Compare its reconstruction calculus with A E and
A L through the normalized adjunction units; uniqueness of the quotient-tower
realization transports the comparison and all its augmentation formulas to these
fixed calculi. Restrict the resulting map to complete constructible objects.
The completed scalar comparison is invertible there, and its conjugation is the
integral comparison. Its composite with the inverse target unit is scalar
extension of the inverse source unit. Transport this restriction along the
underlying-object identifications in integral_actual; this transport retains the
same-index formula and gives b. Raw rational localization of b is semilinearly
balanced and natural, hence gives beta on all rational arrows. Apply localization
to the integral inverse-unit equation, using the localized unit components in
rational_actual and scalar extension's localization comparison. Finally transport
from the published scalar functors to integralTransition and stageTransition.
The comparisons are uniquely determined by the inverse-unit equation, so the
pairwise construction applies to the fixed family R without further choices or
compatibility assumptions. Identity and associator coherence and common-stage
descent are not asserted here and are proved separately by cancellation. -/
theorem reconstructionScalarRealizations (hl : l ≠ D.p)
    (R : ∀ E, Realization D l Ω E (A E)) :
    ∃ (b : ∀ (E L : Index l Ω) (h : E ≤ L),
        (R E).integral ⋙ integralTransition l Ω (point D) E L h ≅
          integralTransition l Ω (point D) E L h ⋙ (R L).integral)
      (β : ∀ (E L : Index l Ω) (h : E ≤ L),
        (R E).rational ⋙ stageTransition l Ω (point D) E L h ≅
          stageTransition l Ω (point D) E L h ⋙ (R L).rational),
      (∀ (E L : Index l Ω) (h : E ≤ L), SameIndexRealization D l Ω A R E L h (b E L h)) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L)
        (C : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) (point D)),
        (b E L h).hom.app C ≫ (R L).integralUnit.inv.app
            ((integralTransition l Ω (point D) E L h).obj C) =
          (integralTransition l Ω (point D) E L h).map ((R E).integralUnit.inv.app C)) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L) (C : Stage l Ω (point D) E),
        HEq ((β E L h).hom.app C)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) (point D)).map
            ((b E L h).hom.app C.obj))) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L) (C : Stage l Ω (point D) E),
        (β E L h).hom.app C ≫ (R L).rationalUnit.inv.app
            ((stageTransition l Ω (point D) E L h).obj C) =
          (stageTransition l Ω (point D) E L h).map ((R E).rationalUnit.inv.app C)) := by sorry

end WeilConjectures.PodCommonStageReconstruction
