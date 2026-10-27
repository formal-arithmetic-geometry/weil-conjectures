/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.FieldPurityTransposeLevelWords
import Sheaf.Paper.FieldPuritySystemTransposeBase
import Sheaf.Paper.FieldPuritySystemTransposeCompatibility
import Sheaf.Paper.FieldScalarNormalizedSystems
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Coefficient compatibility of the actual tower purity transpose

Source: blueprint sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose
(blueprint: lem-sp-field-purity-system-transpose).
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

/-- Coefficient compatibility of the actual counit tensor transpose, its coefficient-unit
normalization, its finite theta identification, and the resulting diagonal purity equation.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose
(blueprint: lem-sp-field-purity-system-transpose).

Proof: (1) Scalar extension preserves the normalized constructible categories and the
uniform bounds (lem-sp-field-scalar-normalized-systems). Tower-gamma supplies the tensor
source and exceptional domains. The semilinear derived calculus supplies the actual scalar
and pullback tensorators. The three supplied finite-Tor origin pairs are precisely the
three domains of tower-shriek-levels (2a), which makes their projections invertible.
(2) Invert the projection-system-square at omega_A. It gives
(1 tensor b_omega) C_Y(pi_A inverse) b_source inverse = pi'_B inverse.
The exceptional-system-comparison counit equation at J_A identifies
C_Y(epsilon_A,J) b_omega inverse with epsilon_B,J P_B(c_J).
(3) Transpose both sides of TensorCompatibility under P_B adjoint G_B. On the left,
the defining counit equation for c and naturality of b give scalar extension of the
transpose of tau_A followed by b_source inverse. Insert its defining inverse projection
and use (2). On the right, naturality of pi_B in omega moves P_B(1 tensor c_J) through
pi_B inverse. Both transposes are (1 tensor the common counit word) pi'_B inverse.
Injectivity of the tower Hom bijection gives equality before evaluation or inverse limit.
(4) At the coefficient unit the proper projection is identity by the triangle identity;
the open projection is identity by lem-sf-open-tensor-normalization. Tau's transpose is
therefore the actual exceptional counit, so tau is identity under unit constraints.
(5) The tower-gamma finite equations identify gamma with theta followed by the inverse
diagonal orientation, while gamma is tau followed by that same invertible orientation.
Cancel it to obtain the finite theta equation, for both coefficient fields. The word maps
record all site, tensor, pullback and unit constraints. Finally precompose (3) by the scalar
extension of 1 tensor a_A. Naturality gives tau_B times 1 tensor c_J C_X(a_A). Replace
that word by a_B using the orientation equation to obtain diagonal purity compatibility.
No equality of general system arrows is inferred from their finite evaluations. -/
theorem field_purity_system_transpose
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
          (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)),
          FinitePurityIdentification P D c b a A t q E d w orientation K hpf) ∧
      ∀ (E F : Index P) (h : E ≤ F) (K : N P D E Y),
        PairDomain P D E K (omega P D c b a A q E) →
        PairDomain P D F ((scalar P D a h Y).obj K) (omega P D c b a A q F) →
        PairDomain P D F ((scalar P D a h Y).obj K)
          ((scalar P D a h X).obj (omega P D c b a A q E)) →
        ∃ (hA : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj))
          (hB : IsIso (leftProjection P D t F c ((scalar P D a h Y).obj K).obj
            (omega P D c b a A q F).obj)),
          TensorCompatibility P D c b a A t q h K hA hB ∧
            DiagonalPurityCompatibility P D c b a A t q h d := by
  obtain ⟨t, q, hbase⟩ := field_purity_system_transpose_base P D c b a A d
    exceptionalLaws
  refine ⟨t, q, hbase.1, hbase.2.1, hbase.2.2, ?_⟩
  exact field_purity_system_transpose_compatibility P D c b a A d exceptionalLaws t q
    ⟨hbase.1, hbase.2.1, hbase.2.2⟩

end AlgebraicGeometry.ProEtale.FieldPuritySystem
