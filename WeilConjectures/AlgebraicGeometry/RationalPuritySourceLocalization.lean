/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonData

/-! # Normalized rational smooth-purity comparison: an intermediate step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.RationalScalarComparisonIdentification
open AdicPurityScalarNaturality
attribute [local irreducible] O G H T Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (I : Data D C f d S)

/-- The actual normalized localization of the twisted integral pullback, with exactness.
Source: current blueprint smooth purity transport, Step 2, and rational adjunction,
Step 1 (localizing the source); parent proof Steps 1 and 3.
(blueprint: lem-pur-rational-source-localization).
Proof: write the integral twist as tensor by its degree-zero Tate line, using
siteSheafTensorRightIso and tensor symmetry. On a good pullback representative,
the single-summand totalization and first-factor shift give twistToShiftedTensor.
The shifted single flat Tate line is good. Compose with the strict quotient tensor
augmentation and the completed tensor representative comparison. Derived localization
and the literal object clauses for rational pullback and tensor identify the target
with H. Naturality and independence of good resolutions descend this comparison
and its inverse. Extend the map equations from integral arrows to pure tensors and
then sums. Localize sourceShift through qYShift and qXShift; its zero and addition
identities descend. The resulting comparison is shift compatible. Exactness follows
by representing distinguished rational triangles by integral triangles and applying
the supplied exact source functor. The displayed normalization is the actual map
on every good representative, so also fixes its sign and shift convention. -/
theorem rationalPuritySourceLocalization (I : Data D C f d S) :
  ∃ (hShift : ∀ (E : AdicPurityScalarNaturality.Field D C),
      (H D C f d E).CommShift ℤ),
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      (fun [_cs : (H D C f d E).CommShift ℤ] ↦ (H D C f d E).IsTriangulated)
      (_cs := hShift E)) ∧
  ∃ (hLocalization : ∀ (E : AdicPurityScalarNaturality.Field D C),
      source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E),
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      SourceLocalizationNormalization D C f d E (hLocalization E)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      ShiftCompatibility (source D C f d E ⋙ Q D C E X) (Q D C E Y ⋙ H D C f d E)
      (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (hShift E)) (hLocalization E)) := by sorry

end WeilConjectures.RationalScalarComparisonIdentification
