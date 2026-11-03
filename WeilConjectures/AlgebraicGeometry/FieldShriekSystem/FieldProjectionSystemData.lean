/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemModels

/-! # The scalar projection square on whole coefficient systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), projection square
(blueprint: lem-sp-field-projection-system-square).

The comparison is the recorded proper/open word. The tensor comparisons below are
fixed on signed K-flat representatives, before evaluation. No cartesian coefficient
square or faithfulness of derived evaluation is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

/-- The specified tensor comparisons used at all four corners. Symmetry is fixed by
its signed total-complex generators; the scalar tensorator uses the existing pure-tensor
and K-flat model, so neither map is an unspecified identification of object values.
Source: blueprint (2), canonical monoidal scalar and symmetry identifications
(blueprint: lem-sp-field-projection-system-square). -/
structure ProjectionTensorComparisons where
  symmetry : ∀ (E : Index P) (T : Scheme.{u}),
    SpTowerShriek.tensor P.coefficients.l E.val (D.base E) T ≅
      CategoryTheory.Prod.swap _ _ ⋙ SpTowerShriek.tensor P.coefficients.l E.val (D.base E) T
  symmetry_model : ∀ (E : Index P) (T : Scheme.{u})
    (A B : CochainComplex (SpTowerShriek.S P.coefficients.l E.val T) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T)) A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T)) B),
    ∃ s : (totalTensor.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
          (SpTowerShriek.tau P.coefficients.l E.val T))).obj (A, B) ⟶
      (totalTensor.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
          (SpTowerShriek.tau P.coefficients.l E.val T))).obj (B, A),
      (∀ (a b n : ℤ) (hab : a + b = n) (hba : b + a = n)
        (U : (ℕ × T.ProEt)ᵒᵖ) (x : (A.X a).val.obj U) (y : (B.X b).val.obj U),
        (s.f n).val.app U
            (coefficientTensorGenerator.{u + 1, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology T))
              (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
                (SpTowerShriek.B P.coefficients.l E.val T)
                (SpTowerShriek.tau P.coefficients.l E.val T)) A B a b n hab U x y) =
          (a * b).negOnePow •
            coefficientTensorGenerator.{u + 1, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology T))
              (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
                (SpTowerShriek.B P.coefficients.l E.val T)
                (SpTowerShriek.tau P.coefficients.l E.val T)) B A b a n hba U y x) ∧
      ((D.base E).calculus T).tensorModels.comparison.hom.app (⟨A, hA⟩, ⟨B, hB⟩) ≫
          (symmetry E T).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
        DerivedCategory.Q.map s ≫
          ((D.base E).calculus T).tensorModels.comparison.hom.app (⟨B, hB⟩, ⟨A, hA⟩)
  scalar : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}),
    SpTowerShriek.tensor P.coefficients.l E.val (D.base E) T ⋙ (D.scalars E F h T).T ≅
      ((D.scalars E F h T).T.prod (D.scalars E F h T).T) ⋙
        SpTowerShriek.tensor P.coefficients.l F.val (D.base F) T
  scalar_model : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}),
    ScalarTensorComparisonModel.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l F.val T)
        (SpTowerShriek.tau P.coefficients.l F.val T))
      (coefficientMap P (D.coefficients E F h) T) (D.scalars E F h T)
      ((D.base E).calculus T).closed ((D.base F).calculus T).closed
      ((D.base E).calculus T).tensorModels ((D.base F).calculus T).tensorModels
      (scalar E F h T)

/-- The left-input compact-support projection, including both tensor symmetries.
Its middle arrow is exactly the published proper-counit/open projection.
Source: blueprint (2), pi_A and pi_B (blueprint: lem-sp-field-projection-system-square). -/
def leftProjection (t : ProjectionTensorComparisons P D) (E : Index P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X) :=
  (t.symmetry E Y).hom.app
      (K, (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj W) ≫
    SpTowerShriek.projection P.coefficients.l E.val (D.base E) (D.operations E) c W K ≫
    (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).map
      ((t.symmetry E X).hom.app
        (W, (SpTowerShriek.pull P.coefficients.l E.val (D.base E)
          ((D.operations E).geometry f)).obj K))

/-- The target comparison is scalar tensor followed by the inverse pullback compositor.
Source: blueprint (2), C_X f_A^* = f_B^* C_Y
(blueprint: lem-sp-field-projection-system-square). -/
def projectionTarget (t : ProjectionTensorComparisons P D) {E F : Index P} (h : E ≤ F)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X) :=
  (t.scalar E F h X).app
      ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
        ((D.operations E).geometry f)).obj K, W) ≪≫
    (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) X).mapIso
      (Iso.prod ((D.pull E F h f).derived.symm.app K) (Iso.refl _))

end AlgebraicGeometry.ProEtale.FieldShriekSystem
