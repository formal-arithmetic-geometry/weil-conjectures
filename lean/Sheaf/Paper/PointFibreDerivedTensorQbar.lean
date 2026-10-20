/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorRational

/-! # Canonical point tensor comparison interfaces

Source: Stacks 07A4 and the recorded coefficient constructions.
(blueprint: def-sf-point-fibre-tensor-common-stage).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v c e d hc he hd w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- The actual inclusion of the small finite coefficient model into Ω.
Source: recorded Shrink coefficient identification
(blueprint: def-sf-point-fibre-tensor-common-stage). -/
def pointTensorStageEmbedding (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (F : Padic.FiniteCoefficientFields l Ω) :=
  F.val.subtype.comp (Shrink.algEquiv ℚ_[l] F.val).toRingHom

/-- The common-stage fibre, identified with the scalar extension of its rational fibre.
This uses the defining object equality and the canonical field tensor tower.
Source: blueprint common-stage construction
(blueprint: def-sf-point-fibre-tensor-common-stage). -/
def pointTensorQbarObjectNormalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  (DerivedCategory.pointFdQbarRealization l Ω).mapIso
      (eqToIso ((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1 A)) ≪≫
    (DerivedCategory.fieldScalarTower (Shrink.algEquiv ℚ_[l] A.stage.val).toRingHom
      A.stage.val.subtype).app
      ((pointRationalFibre D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A.stage)).obj A.obj).obj

/-- The tensor's source normalized at any common finite extension. The comparisons are
exactly `commonStageTensorComparison` and the prescribed point fibre on stage morphisms;
the latter includes `pointStageTensorSquare` through `pointStageFibreScalarIso`.
Source: node proof steps 7 and 9 (blueprint: def-sf-point-fibre-tensor-common-stage). -/
def pointTensorQbarSourceNormalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (L : Padic.FiniteCoefficientFields l Ω)
    (h : Padic.finiteCoefficientCompositum l Ω P.stage Q.stage ≤ L) :=
  letI : ∀ w : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  (pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω).mapIso
      (eqToIso ((commonStageDerivedTensor_existsUnique l Ω
        (Spec (.of D.k))).exists.choose_spec.1 P Q)) ≪≫
    (pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω).mapIso
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).isoToStage
        (commonStageTensorObject l Ω (Spec (.of D.k)) P Q) h) ≪≫
    (pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω).mapIso
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).mapIso
        (commonStageTensorComparison l Ω (Spec (.of D.k)) P Q L h)) ≪≫
    pointTensorQbarObjectNormalization D l hl Ω _

/-- The input fibre transported back from an arbitrary common finite stage.
The actual `isoToStage` is sent by the recorded common-stage fibre functor.
Source: blueprint common-stage representative formula
(blueprint: def-sf-point-fibre-tensor-common-stage). -/
def pointTensorQbarInputNormalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (L : Padic.FiniteCoefficientFields l Ω) (h : P.stage ≤ L) :=
  (pointTensorQbarObjectNormalization D l hl Ω
    ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj (P.toStage h))).symm ≪≫
    (pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω).mapIso
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
        (Spec (.of D.k))).isoToStage P h).symm

/-- The algebraically closed comparison is the rational comparison at every common
finite stage, followed by canonical scalar tensor and the recorded stage transports.
Quantification over every L above the compositum is the scalar-extension compatibility;
there is no chosen representative or ignored identity inclusion.
Source: node proof steps 7 and 9 (blueprint: def-sf-point-fibre-tensor-common-stage). -/
def PointQbarTensorCanonical
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (S : PointFibreDerivedTensorSystem D l hl Ω)
    (B : ∀ L : Padic.FiniteCoefficientFields l Ω,
      PointModuleScalarTensorData (pointTensorStageEmbedding l Ω L)
        (DerivedCategory.fieldDerivedScalarExtension (pointTensorStageEmbedding l Ω L))) : Prop :=
  ∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (L : Padic.FiniteCoefficientFields l Ω)
    (h : Padic.finiteCoefficientCompositum l Ω P.stage Q.stage ≤ L),
    (S.qbar.tensorIso P Q).hom =
      (pointTensorQbarSourceNormalization D l hl Ω P Q L h).hom ≫
      (DerivedCategory.fieldDerivedScalarExtension (pointTensorStageEmbedding l Ω L)).map
        ((S.rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).tensorIso
          (P.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).1.trans h))
          (Q.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).2.trans h))).hom ≫
      (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ _ (B L).strong.toOplaxMonoidal
        ((pointRationalFibre D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj
            (P.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
              P.stage Q.stage).1.trans h))).obj
        ((pointRationalFibre D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj
            (Q.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
              P.stage Q.stage).2.trans h))).obj) ≫
      (MonoidalCategory.tensor _).map
        (Prod.mkHom (pointTensorQbarInputNormalization D l hl Ω P L
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h)).hom
          (pointTensorQbarInputNormalization D l hl Ω Q L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)).hom)


/-- The Ω-unit is the normalized rational unit from the actual base finite stage.
Source: common finite-stage coefficient unit
(blueprint: def-sf-point-fibre-tensor-common-stage). -/
def PointQbarTensorUnitCanonical
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (S : PointFibreDerivedTensorSystem D l hl Ω)
    (B : PointModuleScalarTensorData
      (pointTensorStageEmbedding l Ω (Padic.finiteCoefficientBase l Ω))
      (DerivedCategory.fieldDerivedScalarExtension
        (pointTensorStageEmbedding l Ω (Padic.finiteCoefficientBase l Ω)))) : Prop :=
  S.qbar.unitIso.hom =
    (pointTensorQbarObjectNormalization D l hl Ω
      ⟨Padic.finiteCoefficientBase l Ω, (S.rational
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω))).monoidal.tensorUnit⟩).hom ≫
      (DerivedCategory.fieldDerivedScalarExtension
        (pointTensorStageEmbedding l Ω (Padic.finiteCoefficientBase l Ω))).map
        ((pointRationalFibre D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            (Padic.finiteCoefficientBase l Ω)) ⋙
            (DerivedCategory.pointFiniteDimensional _).ι).map
          (eqToHom (S.rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            (Padic.finiteCoefficientBase l Ω))).unit_eq)) ≫
      (DerivedCategory.fieldDerivedScalarExtension
        (pointTensorStageEmbedding l Ω (Padic.finiteCoefficientBase l Ω))).map
        (S.rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω))).unitIso.hom ≫
      (@Functor.Monoidal.εIso _ _ _ _ _ _ _ B.strong).inv

end WeilConjectures
