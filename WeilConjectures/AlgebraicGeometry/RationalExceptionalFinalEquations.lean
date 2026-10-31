/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonData

/-! # Exceptional coefficient equations in the rational comparison coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Keep the original section hypotheses even though the projection proof does not need them.
set_option linter.unusedSectionVars false
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

/-- The counit equation characterizes the transpose of an inverse left comparison. -/
private theorem transpose_of_counit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    {TX : A ⥤ A'} {TY : B ⥤ B'}
    (adj : F ⊣ G) (adj' : F' ⊣ G')
    (q : F ⋙ TY ≅ TX ⋙ F') (b : G ⋙ TX ≅ TY ⋙ G') (K : B)
    (hc : q.hom.app (G.obj K) ≫ F'.map (b.hom.app K) ≫
      adj'.counit.app (TY.obj K) = TY.map (adj.counit.app K)) :
    b.hom.app K = (adj'.homEquiv (TX.obj (G.obj K)) (TY.obj K))
      (q.inv.app (G.obj K) ≫ TY.map (adj.counit.app K)) := by
  apply (adj'.homEquiv (TX.obj (G.obj K)) (TY.obj K)).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  apply (Iso.cancel_iso_hom_left (q.app (G.obj K)) _ _).mp
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc] using hc

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E
    let r := S.fields.rationalizationComparison (integralExceptionalCompactification D f)
      (fieldStage D C E)
    let _ := r.shiftX
    let _ := r.shiftY
    with_unfolding_all exact r.comparison.bShift
  · intro E F h K
    let r := S.fields.rationalComparison (integralExceptionalCompactification D f)
      (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)
    let _ := r.shiftX
    let _ := r.shiftY
    unfold b coefficientTranspose c G O T
    exact transpose_of_counit
      (S.ring.operation (integralExceptionalCompactification D f)
        (.rational (fieldStage D C E))).adjunction
      (S.ring.operation (integralExceptionalCompactification D f)
        (.rational (fieldStage D C F))).adjunction
      r.q r.b K (r.comparison.counit K)
  · intro E
    unfold UnitEquation b G O T unit
    exact S.fields.rationalIdentityRight (integralExceptionalCompactification D f)
      (fieldStage D C E)
  · intro E F L h k
    unfold CompositionEquation b G O T alpha
    intro K
    have hc := S.fields.rationalCocycle (integralExceptionalCompactification D f)
      (fieldStage D C E) (fieldStage D C F) (fieldStage D C L)
      (IntermediateField.inclusion h) (IntermediateField.inclusion k)
    obtain ⟨_, hright⟩ := hc
    exact (hright K).symm

end WeilConjectures.RationalScalarComparisonIdentification
