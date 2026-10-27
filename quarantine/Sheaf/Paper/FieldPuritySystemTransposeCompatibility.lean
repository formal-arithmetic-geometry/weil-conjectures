/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.FieldPuritySystemTransposeBase

/-! The compatibility remainder of the field purity transpose.

Source: blueprint sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose.
(blueprint: lem-sp-field-purity-system-transpose-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldPuritySystem

open FieldShriekSystem FieldExceptionalSystem
variable (P : PurityFiniteSetting.{u}) (D : Models P)
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)

/-- The scalar compatibility remainder once the base transpose data are fixed.

This is strictly the final compatibility conjunct of the parent theorem, with the
tensor comparisons and coordinates supplied as parameters.  Its proof is the
projection-system-square calculation: invert the two projection maps on the three
finite-Tor etale-origin domains, use the exceptional counit equation at the coefficient
unit, and compare the two maps by the tower adjunction Hom bijection.  Precomposition
with the diagonal orientation gives the stated diagonal purity equation.  No equality
is inferred from finite evaluations; all words are equal as whole-system morphisms.
Source: blueprint sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose
(blueprint: lem-sp-field-purity-system-transpose-compatibility).
-/
theorem field_purity_system_transpose_compatibility
    [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (exceptionalLaws : FieldExceptionalSystem.Laws P D c b a A)
    (t : ProjectionTensorComparisons P D) (q : Coordinates P D (f := f))
    (base : FiniteTensorIdentification P D c b a A t q ∧
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
          FinitePurityIdentification P D c b a A t q E d w orientation K hpf)) :
    ∀ (E F : Index P) (h : E ≤ F) (K : N P D E Y),
      PairDomain P D E K (omega P D c b a A q E) →
      PairDomain P D F ((scalar P D a h Y).obj K) (omega P D c b a A q F) →
      PairDomain P D F ((scalar P D a h Y).obj K)
        ((scalar P D a h X).obj (omega P D c b a A q E)) →
      ∃ (hA : IsIso (leftProjection P D t E c K.obj
          (omega P D c b a A q E).obj))
        (hB : IsIso (leftProjection P D t F c ((scalar P D a h Y).obj K).obj
          (omega P D c b a A q F).obj)),
        TensorCompatibility P D c b a A t q h K hA hB ∧
          DiagonalPurityCompatibility P D c b a A t q h d := by
  sorry

end AlgebraicGeometry.ProEtale.FieldPuritySystem
