/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.PbcQbarCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
import Sheaf.Paper.PbcQbarIdempotentComplete
import Sheaf.Paper.PbcVerdierAxioms

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

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarHom_inclusion
    (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    {C : Padic.FiniteCoefficientFields l Qbar → Type*}
    [∀ E, Category* (C E)] [∀ E, Preadditive (C E)] [∀ E, Linear E.val (C E)]
    [IsDirectedOrder (Padic.FiniteCoefficientFields l Qbar)]
    (S : StageSystem C) (hS : QbarScalarCompatible l Qbar S)
    (E : Padic.FiniteCoefficientFields l Qbar) {K L : C E} (f : K ⟶ L) (a : E.val) :
    qbarScalarHom l Qbar S hS (a : Qbar) ((S.ι E).map f) =
      (S.ι E).map (a • f) := by
  change qbarScalarHom l Qbar S hS (a : Qbar)
    (PairCategory.mkHom (X := ⟨E, K⟩) (Y := ⟨E, L⟩) E le_rfl le_rfl
      ((S.T le_rfl).map f)) = _
  have hs := qbarScalarHom_mkHom l Qbar S hS (a : Qbar) E
    (X := ⟨E, K⟩) (Y := ⟨E, L⟩) le_rfl le_rfl ((S.T le_rfl).map f)
    E le_rfl a.property
  have ht : S.tr (hi := (le_rfl : E ≤ E)) (hj := (le_rfl : E ≤ E))
      (le_rfl : E ≤ E) ((S.T (le_rfl : E ≤ E)).map f) =
      (S.T (le_rfl : E ≤ E)).map f := tr_map (le_rfl : E ≤ E) f
  have he : (⟨(a : Qbar), a.property⟩ : E.val) •
      S.tr (hi := (le_rfl : E ≤ E)) (hj := (le_rfl : E ≤ E))
        (le_rfl : E ≤ E) ((S.T (le_rfl : E ≤ E)).map f) =
      (S.T (le_rfl : E ≤ E)).map (a • f) := by
    rw [ht]
    exact (hS (E := E) (F := E) le_rfl a f).symm
  exact hs.trans (congrArg
    (fun g ↦ PairCategory.mkHom (X := ⟨E, K⟩) (Y := ⟨E, L⟩) E le_rfl le_rfl g) he)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
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
  let S := pbcScalarSystem l Qbar T hDim.out hInv.out
  have hS : QbarScalarCompatible l Qbar S := pbcQbarScalarCompatible l Qbar T
  have hKar := pbcQbarIdempotentComplete l Qbar T
  refine ⟨?_, ?_, ⟨inferInstance⟩, (pbcVerdierAxioms l Qbar T).1,
    hKar.1, hKar.2.2.2.1, hKar.2.2.2.2, ?_⟩
  · intro α X Y r s h
    exact qbarScalarRep_rel l Qbar S hS α (X := X) (Y := Y) h
  · intro α X Y M hX hY f N hMN hα
    exact qbarScalarHom_mkHom l Qbar S hS α (X := X) (Y := Y) M hX hY f N hMN hα
  · intro E
    refine ⟨(pbcVerdierAxioms l Qbar T).2.1 E, inferInstance, ?_⟩
    intro K L f a
    exact (scalarHom_inclusion l Qbar S hS E f a).symm

end AlgebraicGeometry.Scheme
