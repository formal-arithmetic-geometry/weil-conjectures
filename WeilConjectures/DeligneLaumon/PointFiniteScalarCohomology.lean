/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology
public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData

/-! # Point cohomology along the recorded finite-stage transitions

Source: Bhatt--Scholze 6.8.14(2), with the normalized point-realization scalar square
(blueprint: lem-a1-point-finite-scalar-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
universe u uC vC uB vB uA vA uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

section Transport

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {tC : TStructure C} {tB : TStructure B} {tA : TStructure A} {tD : TStructure D}
  {F : C ⥤ A} {G : B ⥤ D} {T : C ⥤ B} {U : A ⥤ D}

private theorem transport_point_scalar_square
    (PF : PointRealizationComparison tC tA F) (PG : PointRealizationComparison tB tD G)
    (PT : PointRealizationComparison tC tB T) (PU : PointRealizationComparison tA tD U)
    (φ : T ⋙ G ≅ F ⋙ U) (hφ : PointRealizationCohomologySquare PF PG PT PU φ)
    (T' : C ⥤ B) (e : T' = T) :
    ∃ PT' : PointRealizationComparison tC tB T',
      PointRealizationCohomologySquare PF PG PT' PU
        (Functor.isoWhiskerRight (eqToIso e) G ≪≫ φ) := by
  subst T'
  refine ⟨PT, ?_⟩
  simpa using hφ

end Transport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (stageTransition)

/-- The finite scalar square is unchanged when the rational scalar functor is replaced
by the recorded stage transition. Source: Bhatt--Scholze 6.8.14(2) and the coefficient
stage convention (blueprint: lem-a1-point-finite-scalar-cohomology).

Proof: the stage-system specification identifies the transition with the rational
scalar functor. Transport the source comparison across that equality. The given
point-realization square then has exactly the displayed beta after inversion.
This includes identity transitions and needs no faithful scalar-extension hypothesis. -/
theorem pointFiniteScalarCohomology
    (P : PointRealizationFiniteCohomologyData D l hl) (E L : Index l Ω) (a : E ≤ L)
    (β : pointRealizationAmbient D l hl (Coefficient.{u} l Ω E) ⋙
        DerivedCategory.fieldDerivedScalarExtension
          (coefficientInclusion l Ω E L a).toRingHom ≅
      stageTransition l Ω (Spec (.of D.k)) E L a ⋙
        pointRealizationAmbient D l hl (Coefficient.{u} l Ω L))
    (hβ : β = (pointRealizationScalarIso D l hl (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a)).symm ≪≫
      Functor.isoWhiskerRight (operationStageTransitionIso l Ω (Spec (.of D.k)) E L a).symm
        (pointRealizationAmbient D l hl (Coefficient.{u} l Ω L))) :
    ∃ s : PointRealizationComparison
        (pointRealizationSourceT D l hl (Coefficient.{u} l Ω E))
        (pointRealizationSourceT D l hl (Coefficient.{u} l Ω L))
        (stageTransition l Ω (Spec (.of D.k)) E L a),
      PointRealizationCohomologySquare
        (P.finite (Coefficient.{u} l Ω E)) (P.finite (Coefficient.{u} l Ω L)) s
        (pointFieldComparison (coefficientInclusion l Ω E L a).toRingHom) β.symm := by
  obtain ⟨s, hs⟩ := transport_point_scalar_square
    (P.finite (Coefficient.{u} l Ω E)) (P.finite (Coefficient.{u} l Ω L))
    (P.scalar _ _ (coefficientInclusion l Ω E L a))
    (pointFieldComparison (coefficientInclusion l Ω E L a).toRingHom)
    (pointRealizationScalarIso D l hl _ _ (coefficientInclusion l Ω E L a))
    (P.scalar_square _ _ (coefficientInclusion l Ω E L a))
    (stageTransition l Ω (Spec (.of D.k)) E L a)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω (Spec (.of D.k))).exists.choose_spec.1 E L a)
  refine ⟨s, ?_⟩
  have hb : β.symm =
      Functor.isoWhiskerRight (operationStageTransitionIso l Ω (Spec (.of D.k)) E L a)
        (pointRealizationAmbient D l hl (Coefficient.{u} l Ω L)) ≪≫
      pointRealizationScalarIso D l hl (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a) := by
    rw [hβ]
    rfl
  rw [hb]
  exact hs

end WeilConjectures
