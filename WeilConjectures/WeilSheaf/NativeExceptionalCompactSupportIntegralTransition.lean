/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeExceptionalCompactSupportFinite

/-! # Integral transition equation for the specified compact-support scalar map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard Padic
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients

/-- Negating both directions of an isomorphism preserves its inverse equations. -/
private def signIso {A B : Type*} [Category A] [Category B] [Preadditive B]
    {F H : A ⥤ B} (e : F ≅ H) : F ≅ H where
  hom := -e.hom
  inv := -e.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- Negation preserves the shift equation when the target shifts are additive. -/
private theorem signShift {A B : Type*} [Category A] [Category B] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive]
    {F H : A ⥤ B} [F.CommShift ℤ] [H.CommShift ℤ]
    (t : F ⟶ H) (ht : t.CommShift ℤ) : (-t).CommShift ℤ := by
  constructor
  intro n
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.app_neg, Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp] using
    congrArg Neg.neg (congr_app (ht.shift_comm n) K)

/-- The adjunction comparison permits simultaneous sign changes of q and b. -/
private def signFieldComparison (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {A : Operation.{u, 0} l (PadicAlgCl l) X Y s}
    {B : Operation.{u, 0} l (PadicAlgCl l) X Y t}
    {TX : C.{u, 0} l (PadicAlgCl l) X s ⥤ C.{u, 0} l (PadicAlgCl l) X t}
    {TY : C.{u, 0} l (PadicAlgCl l) Y s ⥤ C.{u, 0} l (PadicAlgCl l) Y t}
    (d : FieldComparison.{u, 0} l (PadicAlgCl l) A B TX TY) :
    FieldComparison.{u, 0} l (PadicAlgCl l) A B TX TY := by
  letI := d.shiftX
  letI := d.shiftY
  exact {
    shiftX := d.shiftX
    shiftY := d.shiftY
    comparison := {
      q := signIso d.comparison.q
      b := signIso d.comparison.b
      unit := fun K ↦ by
        simpa only [signIso, NatTrans.app_neg, Functor.map_neg, Preadditive.comp_neg,
          Preadditive.neg_comp, neg_neg] using d.comparison.unit K
      counit := fun K ↦ by
        simpa only [signIso, NatTrans.app_neg, Functor.map_neg, Preadditive.comp_neg,
          Preadditive.neg_comp, neg_neg] using d.comparison.counit K
      qShift := signShift d.comparison.q.hom d.comparison.qShift
      bShift := signShift d.comparison.b.hom d.comparison.bShift } }

variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (source : Realization l X) (target : Realization l Y)
  (S : System.{u, 0} l (PadicAlgCl l) D hl (f := f)) (c : Compactification f)

/-- Each rationalLeft can be signed independently without changing operations. -/
private def signedRing (sign : FieldStage.{u} l → Bool) :
    RingSystem.{u, 0} l (PadicAlgCl l) D hl (f := f) :=
  { S.ring with
    rationalLeft := fun c E ↦ if sign E then signIso (S.ring.rationalLeft c E)
      else S.ring.rationalLeft c E }

/-- The compensating sign of rationalizationComparison preserves its only normalization. -/
private def signedFields (sign : FieldStage.{u} l → Bool) :
    FieldSystem.{u, 0} l (PadicAlgCl l) D hl (signedRing l D hl S sign) :=
  { rationalizationComparison := fun c E ↦ if sign E then
      signFieldComparison l (S.fields.rationalizationComparison c E)
      else S.fields.rationalizationComparison c E
    rationalization_normalized := fun c E K ↦ by
      cases hs : sign E
      · simp only [signedRing, hs, Bool.false_eq_true, ↓reduceIte]
        exact S.fields.rationalization_normalized c E K
      · simp only [signedRing, hs, ↓reduceIte]
        simpa only [signFieldComparison, FieldComparison.q, signIso, NatTrans.app_neg,
          Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using
          S.fields.rationalization_normalized c E K
    rationalComparison := S.fields.rationalComparison
    rational_normalized := S.fields.rational_normalized
    rationalCocycle := S.fields.rationalCocycle
    rationalIdentityLeft := S.fields.rationalIdentityLeft
    rationalIdentityRight := S.fields.rationalIdentityRight }

/-- All common-stage and refinement laws survive independent finite-field signs. -/
private def signedSystem (sign : FieldStage.{u} l → Bool) :
    System.{u, 0} l (PadicAlgCl l) D hl (f := f) where
  ring := signedRing l D hl S sign
  fields := signedFields l D hl S sign
  common := {
    commonComparison := S.common.commonComparison
    common_normalized := S.common.common_normalized
    commonCocycleLeft := S.common.commonCocycleLeft
    commonCocycleRight := S.common.commonCocycleRight }
  refinements := {
    refinement := S.refinements.refinement
    refinement_normalized := S.refinements.refinement_normalized
    refinementRational := S.refinements.refinementRational
    refinementCommon := S.refinements.refinementCommon
    refinementIdentity := S.refinements.refinementIdentity
    refinementComposition := S.refinements.refinementComposition }

/-- The free sign can also be inserted in the family of finite isomorphisms. -/
private def signedAlpha (sign : FieldStage.{u} l → Bool)
    (alpha : ∀ E : Index l (PadicAlgCl l),
      systemFiniteSource l D hl target S c E ≅ systemFiniteTarget l source c E)
    (E : Index l (PadicAlgCl l)) :
    systemFiniteSource l D hl target (signedSystem l D hl S sign) c E ≅
      systemFiniteTarget l source c E :=
  if sign (commonField l (PadicAlgCl l) E) then signIso (alpha E) else alpha E

/-- Changing the sign at just the enlarged endpoint contradicts compatibility on
any arrow whose normalized image is not its own negative. -/
private theorem transition_sign_obstruction
    {B : Type*} [Category B] [Preadditive B] {P Q R T : B}
    (u : P ⟶ Q) (v : R ⟶ T) (a : P ⟶ R) (b : Q ⟶ T)
    (hn : a ≫ v ≠ -(a ≫ v))
    (h : u ≫ b = a ≫ v) : u ≫ (-b) ≠ a ≫ v := by
  intro h'
  rw [Preadditive.comp_neg, h] at h'
  exact hn h'.symm

/-- On any input whose image is not its own negative, the unsigned and signed
systems cannot both satisfy the proposed transition equality. -/
private theorem signedAlpha_transition_fails
    (sign : FieldStage.{u} l → Bool)
    (alpha : ∀ E : Index l (PadicAlgCl l),
      systemFiniteSource l D hl target S c E ≅ systemFiniteTarget l source c E)
    (A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
    (E : Index l (PadicAlgCl l)) (h : A.stage ≤ E)
    (h₀ : sign (commonField l (PadicAlgCl l) A.stage) = false)
    (h₁ : sign (commonField l (PadicAlgCl l) E) = true)
    (hn : (alpha A.stage).hom.app A.obj ≫ (source.J ⋙ actual l c).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom ≠
      -((alpha A.stage).hom.app A.obj ≫ (source.J ⋙ actual l c).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom))
    (hc : ((S.ring.operation c .closed).F ⋙ target.J).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom ≫
        (alpha E).hom.app (A.toStage h) =
      (alpha A.stage).hom.app A.obj ≫ (source.J ⋙ actual l c).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom) :
    ((S.ring.operation c .closed).F ⋙ target.J).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom ≫
        (signedAlpha l D hl source target S c sign alpha E).hom.app (A.toStage h) ≠
      (signedAlpha l D hl source target S c sign alpha A.stage).hom.app A.obj ≫
        (source.J ⋙ actual l c).map
          (StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom := by
  simp only [signedAlpha, h₀, h₁, Bool.false_eq_true, ↓reduceIte,
    signIso, NatTrans.app_neg]
  exact transition_sign_obstruction _ _ _ _ hn hc

/-- Integral-normalized finite scalar comparisons commute with field transitions.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, common-field comparison;
step 3 of lem-sf-native-exceptional-compact-support-realization.
(blueprint: lem-sf-native-exceptional-compact-support-integral-transition).

Proof: represent the rational input by its unchanged underlying integral object.
Integral residue Tor regards this object as finite-Tor without changing it. Apply
faithful derived sections and insert the supplied integral component formulas.
The image of each integral map is its defining composite of inverse commonComparison,
rationalLeft, target integral realization, inverse completed compact-support
realization, the proper/open scalar mate, inverse source integral realization, and
inverse operationTransport. Insert S.common.commonCocycleLeft to move the closed
operation across the transition. The source and target common_field equations,
S.fields.rational_normalized and integralLeft_normalized identify the remaining
terms with the integral scalar square. The coefficient_scalar equations identify
successive integral-to-native maps with the direct one. The balanced tensor
associator, completion comparison and proper counit triangle identities identify
the proper scalar mates with their composite, as in comparison_composition. The
open comparison is the tensor-unit-normalized extension-by-zero map. Cancel the
intervening realization boundaries and reflect equality through faithful sections.
The integral component formula then gives precisely the displayed equality for
alpha. Repeated fields use the same tensor unit; zero inputs and empty schemes use
the same equations. This statement asserts only transition compatibility for a
supplied normalized family, not existence, invertibility, localization or descent. -/
-- STATEMENT-DISPUTED: System permits independent signs of rationalLeft at each field.
-- The signedSystem construction above preserves every System law, but changes the
-- prescribed integral component by that sign, by linearity of its defining composite.
-- At two fields
-- with different signs the equality cannot hold for both families when the
-- displayed right-hand composite is unequal to its negative.
-- transition_sign_obstruction isolates this conditional failure.
-- CoefficientConstructionNormalization.localizationIdentity would exclude this
-- freedom, but exists_system does not retain it in FieldSystem or System.
-- The checked obstruction above is conditional on distinct endpoint signs and a
-- component that is not its own negative; it does not construct a concrete scheme.
theorem systemFiniteTransition [G : NativeGeometry.{u} l]
    [∀ x : X, Invertible (l : X.residueField x)]
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (E : Index l (PadicAlgCl l)) (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      (change E).map T = C.integralMap l T)
    (alpha : ∀ E : Index l (PadicAlgCl l),
      systemFiniteSource l D hl target S c E ≅ systemFiniteTarget l source c E)
    (halpha : ∀ (E : Index l (PadicAlgCl l))
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      (alpha E).hom.app ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) =
        (systemIntegralMap l D hl source target S c E (change E)
          (ha E X (source.coefficient E)) (ha E Y (target.coefficient E))).app K)
    (A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
    (E : Index l (PadicAlgCl l)) (h : A.stage ≤ E) :
    ((S.ring.operation c .closed).F ⋙ target.J).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom ≫
        (alpha E).hom.app (A.toStage h) =
      (alpha A.stage).hom.app A.obj ≫ (source.J ⋙ actual l c).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          A h).hom := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
