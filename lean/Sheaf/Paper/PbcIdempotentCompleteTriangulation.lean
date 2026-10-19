/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.PbcQbarCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.PbcVerdierAxioms
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.PbcQbarIdempotentComplete
import Sheaf.Paper.PbcScalarExtension

/-! # Idempotent-complete triangulation over the algebraic closure

Source: blueprint, `sec-smooth-purity/sk-prop-sf-cbc`, order 1544
(blueprint: thm-weil-pbc-idempotent-complete-triangulation).

The category, scalar action, shift, and distinguished triangles are the recorded
common-stage constructions. The Karoubi envelope has its canonical retract triangulation.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

/-- The actual common-stage category is linear, triangulated, and idempotent complete;
its canonical Karoubi inclusion is an exact equivalence, and each finite-stage inclusion
is exact and linear over that stage's field. Linearity of the latter is written as
additivity and the scalar equation, restricting Qbar scalars by the actual field inclusion.
Source: blueprint, `sec-smooth-purity/sk-prop-sf-cbc`, order 1544
(blueprint: thm-weil-pbc-idempotent-complete-triangulation).

Proof:
1. On K-flat representatives, integral tensor sends scalar multiplication to the same
scalar multiplication by tensor balancing (lem-pur-derived-change-of-rings). This descends
through rational scalar localization (def-weil-linear-scalar-localization and
def-weil-pbc-rational-category) and the scalar-extension associators
(prop-weil-pbc-scalar-extension), giving semilinear transport.
2. Compare two auxiliary overfields in their compositum. Semilinearity and transport
transitivity (prop-weil-pbc-common-stage-calculus) make both multiplied representatives
equal there. If representatives were equivalent, first transport their witnessing equality
to a field also containing the scalar. Thus multiplication respects the equivalence relation
of def-weil-pbc-finite-stage-pair-category and is independent of the auxiliary field.
3. Move every finite collection of coefficients and arrows to one common stage. The module
laws and the two scalar-composition laws hold in the finite-stage linear category and hence
in the quotient. This is the specified Qbar-linear structure of def-weil-pbc-qbar-category.
4. Apply thm-weil-pbc-verdier-axioms to exactly the common-stage shift and cone triangles.
It gives TR1--TR4, including the octahedral axiom, and exactness of each stage inclusion
with its specified shift comparison.
5. Apply thm-weil-pbc-qbar-idempotent-complete to this same raw pair category. It gives
idempotent completeness and exact equivalence of the canonical inclusion into the envelope
of def-weil-karoubi-envelope; no change of category or triangulation is made.
6. For a scalar a in E, compute the scalar prescription at N = E, using the normalized
identity transition. Then j_E(a u) = a j_E(u). Common-stage addition similarly gives
j_E(u + v) = j_E(u) + j_E(v). These are precisely def-weil-linear-functor over E;
combine them with exactness from step 4. -/
theorem pbcIdempotentCompleteTriangulation
    (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    (∀ (α : Qbar) {X Y : pbcQbarCategory l Qbar T}
      (r s : PairCategory.Rep X Y), PairCategory.Rep.Rel r s →
        PairCategory.Rep.Rel
          (qbarScalarRep l Qbar (pbcScalarSystem l Qbar T hDim.out hInv.out) α r)
          (qbarScalarRep l Qbar (pbcScalarSystem l Qbar T hDim.out hInv.out) α s)) ∧
    (∀ (α : Qbar) {X Y : pbcQbarCategory l Qbar T}
      (M : Padic.FiniteCoefficientFields l Qbar) (hX : X.stage ≤ M) (hY : Y.stage ≤ M)
      (f : X.toStage hX ⟶ Y.toStage hY)
      (N : Padic.FiniteCoefficientFields l Qbar) (hMN : M ≤ N) (hα : α ∈ N.val),
        α • (PairCategory.mkHom M hX hY f : X ⟶ Y) =
          PairCategory.mkHom N (hX.trans hMN) (hY.trans hMN)
            ((⟨α, hα⟩ : N.val) • (pbcScalarSystem l Qbar T hDim.out hInv.out).tr hMN f)) ∧
    Nonempty (Linear Qbar (pbcQbarCategory l Qbar T)) ∧
    CategoryTheory.IsTriangulated (pbcQbarCategory l Qbar T) ∧
    IsIdempotentComplete (pbcQbarCategory l Qbar T) ∧
    (toKaroubi (pbcQbarCategory l Qbar T)).IsEquivalence ∧
    (toKaroubi (pbcQbarCategory l Qbar T)).IsTriangulated ∧
    (∀ E : Padic.FiniteCoefficientFields l Qbar,
      ((pbcScalarSystem l Qbar T hDim.out hInv.out).ι E).IsTriangulated ∧
      ((pbcScalarSystem l Qbar T hDim.out hInv.out).ι E).Additive ∧
      ∀ {K L : pbcStageCategory l Qbar T E} (f : K ⟶ L) (a : E.val),
        ((pbcScalarSystem l Qbar T hDim.out hInv.out).ι E).map (a • f) =
          (a : Qbar) • ((pbcScalarSystem l Qbar T hDim.out hInv.out).ι E).map f) := by
  sorry

end AlgebraicGeometry.Scheme
