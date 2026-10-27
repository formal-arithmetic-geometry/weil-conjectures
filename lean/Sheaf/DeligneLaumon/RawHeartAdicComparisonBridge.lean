/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.DeligneLaumon.RawHeartAdicLisseData
import Sheaf.Paper.ZlSfPbcNormalizedHeartModel
import Sheaf.Paper.ClassicalSystemRawLisseRealization

/-! # Comparison bridges for the raw adic lisse heart

Source: Bhatt--Scholze, Propositions 6.8.4 and 6.8.14, Remark 6.8.15;
blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.RawHeartAdic
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Translate the normalized lisse, completed-system and continuous realizations into
one coefficient-size-compatible family. This assertion concerns only the comparison
functors, independently of any particular object or stratification.

Source: BS 6.8.2, 6.8.4(1),(4), 6.8.14(2), 6.8.15; the comparison clauses of
lem-zl-sf-pbc-normalized-heart-model and lem-zl-classical-system-raw-lisse-realization
(blueprint: lem-zl-raw-heart-adic-comparison-bridge).

Proof: Identify E with its ULift by down, transporting its valuation ring and all
finite quotients by this same algebra equivalence. Evaluation on a pro-etale chart
identifies the rational and integral coefficient sheaves pointwise, and the inclusion
square commutes because both maps take an integral value to that same field value.
For the small condensed chart, use a small presentation of the finite extension;
its valuation topology has clopen balls, so the continuous chart comparison applies.
The same evaluation formulas give the two displayed section normalizations.
Transport the finite-free normalized towers of the classical-system realization
through these coefficient equivalences. Realize a tower by the degree-zero inverse
limit followed by raw rationalization. The completed-system comparison and raw
lisse realization identify its sheaf with the localization of that same limit;
full faithfulness follows from their Hom bijections. Evaluation of the limit at a
geometric point gives the required fibre comparison. Pullback and scalar extension
use the quotient and balanced-tensor maps; their section formulas give exactly the
pull_sections and scalar_sections fields, including the identity-chart projection.
At common stages transport these finite functors and their scalar comparisons;
the identity and associator laws descend to the pair categories. The classical
functor is the existing algebraic-model functor on representatives and arrows,
and its full faithfulness is the directed colimit of the finite Hom bijections.
Finally the normalized heart-model comparison identifies both halves in each degree.
Its identity-on-integral realization and the scalar-localization universal property
identify its derived realization with a.J, and its point comparison gives fibres.
All constructions preserve zero and require no nonempty base or positive rank. -/
theorem raw_heart_adic_comparison_bridge
    (a : LisseRealization.Family D l hl) (ha : Normalized D l hl Ω a)
    (c : ProEtale.CompletedLisse.System.{u} l)
    (S : FdCoefficientComparisonSystem.{u} l Ω) (hS : FdComparisonSchemeCoherence l Ω S)
    (r : ContinuousRational.Family.{u} l) :
    ∃ b : ClassicalFamily D l hl a c,
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (Y : PerAdic.Base D.k), Nonempty (CondensedCoefficients D l A Y)) ∧
    (∀ Y : PerAdic.Base D.k,
      Nonempty (HeartComparison D l hl Ω a S r Y
        (hDim := baseDimension D l hl Y) (hInv := basePrimeUnit D l hl Y))) ∧
    (∀ Y : PerAdic.Base D.k, Nonempty (ClassicalCommon D l hl Ω a c b Y)) := by sorry

end WeilConjectures.RawHeartAdic
