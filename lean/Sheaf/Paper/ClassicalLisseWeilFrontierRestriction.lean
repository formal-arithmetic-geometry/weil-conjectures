/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.ClassicalLisseWeilFrontierData

import Sheaf.Paper.ClassicalWeilRestrictionExistence
import Sheaf.Paper.ClassicalFrontierExistence
import Sheaf.Paper.ClassicalSuccessiveRestrictions

/-! # Classical Weil restriction along finite-field frontiers

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_model_frobenius_square
    {R : Realization D l Ω}
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    {M : sfCommonStageHeart l (fiberBase D Y₀).scheme Ω}
    {P : PartitionData D l Ω R (fiberBase D Y₀) M} {m : ℕ} {hm : 1 ≤ m}
    (V : RestrictionModel D l Ω R Y₀ (fiberBase D Y₀) M P m hm)
    (hj : V.intoSupport = V.geometricMap D l Ω) :
    V.intoSupport ≫ localPositivePower (D.geometricFrobenius Y₀).hom (m - 1) =
      (V.frobenius D l Ω).hom ≫ V.intoSupport := by
  rw [hj]
  unfold RestrictionModel.geometricMap RestrictionModel.frobenius
  rw [Category.assoc, ← constantExtensionFiber_return D m hm Y₀,
    ← Category.assoc, ← zlFrobenius_naturality (constantExtensionDatum D m hm) V.inclusion,
    Category.assoc]

/-- Classical Weil restriction and preservation along finite-field frontiers.

Source: blueprint thm-zl-real-mixed-by-curves, proof paragraphs 6--7;
BS Proposition 6.8.4(1),(4), Proposition 6.8.14(2), Remark 6.8.15
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction).

Proof: pull the chosen integral systems levelwise along each locally closed factorization.
Their finite free trivializations and quotient transitions pull back, so the same E-lattice
realizes the restricted object. The quotient-normalized comparison identifies its inverse
limit and rationalization with derived restriction; its unit square gives compatibility
with coefficients and successive restrictions. For a finite-field model j, geometric
Frobenius satisfies j g_Y^m = g_V j. Conjugate the actual theta^[m] by the two completed
compositors, pull it along j, and conjugate by the supplied realization identification.
Fullness lifts this map and its inverse to rational classical maps; faithfulness gives
both inverse equations. Represent the two maps and equations at finite stages, then take
their compositum with E. On the included finite point model, compose the restricted
realization identification with the inverse of its specified Weil realization isomorphism.
Apply the recorded normalized fibre functor, the inverse equivalence unit and its lisse
fibre comparison; this fixes the point identification before asserting equivariance.
At a point, iterate the same compositor formula; associativity
identifies it with theta^[mr]. The point-transport, return-comparison and Weil-map factors
all agree with the normalized adic factors, hence so does every local iterate. Apply the
smooth affine frontier stratification theorem to the reduced partition. Reduced immersions
factor scheme-theoretically through the reduction. Descend the finite diagram to one
finite extension, including all clopen affine smooth geometrically connected pieces.
Dimension zero gives Spec of the same finite field. Use the zero chain for an empty
scheme. Restrict the chosen lattices to these pieces and apply the preceding Weil lifting
for their common extension degree; neither partition nor lattice was required stable.
-/
theorem classical_lisse_weil_frontier_restriction
    (R : Realization D l Ω) (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (C : RestrictionComparison D l Ω R S A)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] :
    RestrictionConclusion D l Ω R S A C Y₀ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro M P K hK m hm V hj
    exact classical_weil_restriction_exists D l Ω R S A C Y₀ M P K hK m hm V hj
      (restriction_model_frobenius_square D l Ω V hj)
  · intro reduced M P
    refine ⟨classical_successive_restrictions D l Ω R S A C _ M P, ?_⟩
    obtain ⟨H⟩ := classical_frontier_exists D l Ω R Y₀ reduced M P
    exact ⟨H, fun a b ↦ ⟨(H.piece a b).identification D l Ω C⟩⟩
  · intro M P
    obtain ⟨H⟩ := classical_frontier_exists D l Ω R Y₀ false M P
    refine ⟨H, ?_⟩
    intro K hK a b
    exact classical_weil_restriction_exists D l Ω R S A C Y₀ M P K hK
      H.degree H.positive (H.piece a b)
      ((Category.comp_id (H.piece a b).intoSupport).symm.trans (H.geometric_piece a b))
      (restriction_model_frobenius_square D l Ω (H.piece a b)
        ((Category.comp_id (H.piece a b).intoSupport).symm.trans (H.geometric_piece a b)))

end WeilConjectures.ZlFrontier
