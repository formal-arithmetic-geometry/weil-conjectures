/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.PbcSupportCondition
import Sheaf.Paper.AdicLisseCohomologyCalculus
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.QbarPerverseSupportCondition
import Sheaf.Paper.TateTwistLisseLine

/-! # Tate twists preserve cohomology supports and the support condition

Source: main-20261015, sec-deligne-laumon-a1/sk-p-dl-a1-perverse,
lem-per-smooth-pullback-t-exact.proof.md, second paragraph
(blueprint: lem-per-tate-twist-support-condition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

/-- The literal signed Tate twist stays in the actual adic Qbar category, as recorded
by the codomain of pbcTateTwist. Its canonical cohomology comparison is invertible
and natural on the rational stage. Its geometric fibre is tensor with the displayed
one-dimensional Qbar line. Every cohomology support, and hence every support
inequality, is preserved.

Source: main-20261015, lem-per-smooth-pullback-t-exact.proof.md, second paragraph
(blueprint: lem-per-tate-twist-support-condition).

Proof:
1. By lem-per-tate-twist-lisse-line, signed powers and dual powers of the compatible
root line are adic lisse of rank one. Its degree-zero realization is exactly the
coefficient twist, and ordinary derived tensor by this line is already complete.
The constructibility assertion is the restriction used by pbcTateTwist. Apply
lem-per-adic-lisse-cohomology-calculus: exact tensor by the line gives the canonical
cohomology-tensor comparison. On representatives this is the inverse of
mapDerivedCategoryHomologyFunctorIso; transportNat extends it to all rational
arrows. Completed geometric pullback, exact point sections and scalar extension
give its fibre comparison. Tensor balancing identifies the target with ordinary
Qbar vector-space tensor. Coefficient extension preserves all these comparisons,
so they compute the common-stage Qbar comparison independently of the lattice.
The line's fibre has dimension one, also for zero and negative exponents.
2. Tensor with a one-dimensional vector space is zero exactly when the original
vector space is zero. The fibre comparison therefore identifies the two nonzero
fibre loci. Their closures, which define cohomology support, are equal for every
a. This includes empty schemes, zero objects and vanishing cohomology degrees.
3. Substitute these equal supports in each dimension inequality of
PbcSupportCondition at degree minus i. The two predicates are equivalent, with
empty support satisfying every inequality by the minus-infinity convention. -/
theorem pbcTateTwistSupportCondition
    (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
    [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsNoetherian X]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (M : pbcQbarCategory l Ω X) (m : ℤ) :
    (∀ a : ℤ, IsIso ((pbcTateCohomologyMap l X Ω M.stage m a).app M.obj)) ∧
    (∀ (a : ℤ) (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X),
      Nonempty
        (pbcTateRational l X Ω M.stage m ⋙
            pbcRationalCohomologyFibre l Ω X M.stage κ x a ≅
          pbcRationalCohomologyFibre l Ω X M.stage κ x a ⋙
            pbcFibreTensorRight Ω (pbcTateLineFibre l X Ω M.stage m κ x))) ∧
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X),
      Module.finrank Ω (pbcTateLineFibre l X Ω M.stage m κ x) = 1) ∧
    (∀ a : ℤ,
      pbcQbarCohomologySupport l Ω X (pbcTateTwist l X Ω M m) a =
        pbcQbarCohomologySupport l Ω X M a) ∧
    (PbcSupportCondition l Ω X M ↔
      PbcSupportCondition l Ω X (pbcTateTwist l X Ω M m)) := by
  sorry

end AlgebraicGeometry.Scheme
