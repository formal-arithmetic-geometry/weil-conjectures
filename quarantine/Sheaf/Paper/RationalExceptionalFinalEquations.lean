module

public import Sheaf.Paper.RationalScalarComparisonData

/-! # Exceptional coefficient equations in the rational comparison coordinates -/

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

/-- The fixed exceptional coefficient system supplies its remaining rational equations:
its localization shift, counit-transpose comparison, repeated-field unit, and three-field
composition. These are exactly the corresponding fields of the normalized rational system.
Source: smooth purity transport coefficient-change proof, parts (2)-(3)
(blueprint: lem-pur-rational-exceptional-final-equations).
Proof: the system rationalization comparison is the specified gLocalization, so its
bShift equation gives the first clause, after identifying the target and quotient shift
structures. For the second clause apply the rational adjunction Hom bijection: its counit
formula turns the desired equation into the comparison counit equation after cancellation
of the compact-support comparison and its inverse. The rational identity comparison gives
the unit equation after composing with the scalar unitor. For a chain E ≤ F ≤ L, the right
component of the rational coefficient cocycle gives the composition equation with the
specified scalar associators. All comparisons are the fixed normalized system comparisons;
no new exceptional comparison is chosen. -/
theorem rationalExceptionalFinalEquations :
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      ShiftCompatibility (target D C f S E ⋙ Q D C E X)
      (Q D C E Y ⋙ G D C f S E)
      (composeShift _ _ (targetShift D C f S E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (gShift D C f S E)) (gLocalization D C f S E)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (K : RCat D C E Y),
      (b D C f S E F h).hom.app K = coefficientTranspose D C f S E F h K) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      UnitEquation (b D C f S E E le_rfl) (unit D C E X) (unit D C E Y)) ∧
  (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (b D C f S E F h) (b D C f S F L k)
      (b D C f S E L (h.trans k)) (alpha D C E F L h k X) (alpha D C E F L h k Y)) := by
  sorry

end WeilConjectures.RationalScalarComparisonIdentification
