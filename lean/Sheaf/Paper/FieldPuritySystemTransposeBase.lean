/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.FieldPurityTransposeLevelWords
import Sheaf.Paper.FieldScalarNormalizedSystems
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SixFunctors.OpenTensorNormalization

/-! A strictly smaller interface lemma for the field purity transpose.

Source: blueprint sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose.
(blueprint: lem-sp-field-purity-system-transpose-base)
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

namespace AlgebraicGeometry.ProEtale.FieldPuritySystem

open FieldShriekSystem FieldExceptionalSystem
variable (P : PurityFiniteSetting.{u}) (D : Models P)
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)

/-- The tensor, unit and finite-level part of the field purity transpose package.

This is strictly the first two conjuncts of the parent theorem.  Its proof follows the
projection-square inversion and the tower-gamma finite-word calculation: choose the
canonical signed tensor comparisons and coefficient coordinates, then compare the
actual counit transpose with the finite theta word at every positive level.  The
coefficient-unit case is the triangle identity, and the diagonal finite clauses are
the normalized tower-gamma equations.  All comparisons are made before inverse limits.
Source: blueprint sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose
(blueprint: lem-sp-field-purity-system-transpose-base).
-/
theorem field_purity_system_transpose_base
    [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (exceptionalLaws : FieldExceptionalSystem.Laws P D c b a A) :
    ∃ (t : ProjectionTensorComparisons P D) (q : Coordinates P D (f := f)),
      FiniteTensorIdentification P D c b a A t q ∧
      (∀ E : Index P,
        ∃ hU : IsIso (leftProjection P D t E c (unit P D q E).obj
            (omega P D c b a A q E).obj),
          (tau P D c b a A t q E (unit P D q E) hU).hom =
            (unitConstraint P D c b a A q E).hom) ∧
      (∀ (E : Index P) (w : SpChartAdmissibility.Twists P.coefficients.l E.val X)
        (orientation : SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X w d ≅
          (omega P D c b a A q E).obj),
        DiagonalOrientation P D c b a A q E d w orientation →
        ∀ (K : N P D E Y)
          (hpf : IsIso (leftProjection P D t E c K.obj
            (omega P D c b a A q E).obj)),
          FinitePurityIdentification P D c b a A t q E d w orientation K hpf) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldPuritySystem
