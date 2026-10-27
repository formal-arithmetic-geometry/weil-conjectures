/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizedOrdinaryPullbackData

/-! # Composition of normalized scalar-localization comparisons

Source: Stacks Project, Tags 03EL, 0D6D and 07A4; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-localized-ordinary-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.LocalizedOrdinary

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (ϖ : PbcIntegralRing l E)

/-- Normalized edges have the specified rational compositor and the ordinary
and derived delta-composition squares.
Source: Stacks Project, Tags 0D6D, 07A4, 06YS and 0G7D;
Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-localized-ordinary-composition).

Proof: compose the two coefficient-unit equations. Inverse-image compositor
naturality and completed coefficient composition give the unit equation for
the composite edge. The inverse-image localization universal property makes
precomposition by the localized unit injective, giving coefficient_comp.

Construct the ordinary rational compositor by balanced multiplication:
e'' tensor (e' tensor m) maps to e'' d_h^E(e') tensor m after the canonical
fiber-product restriction; its inverse inserts 1. Associativity and the
coefficient equation give balancing, both inverse identities and naturality.
Use the normalized Edge tensor and inverse-unit formulas. On e'' tensor
(b' tensor m), either delta-composition route has scalar
 e'' iota_Z(c_h(b')). Along the second route the scalar is initially
 e'' d_h^E(h⁻¹iota_Y(b')); the coefficient-unit square identifies it with
the first. The actual integral compositor is the adjunction conjugate of
fiber-product pasting, so its unit-insertion formula gives exactly the first
route. Pure tensors, local generation of inverse-image sections, and
sheafification prove ordinary_square and ordinary_mixed_tensor.

Derive the rational compositor on flat-term K-flat representatives, where it
is the ordinary chain map just constructed. Pullback and extension preserve
these representatives, giving derived_model with the fixed counits. Insert
the three Edge derived_model equations and the normalized integral derived
compositor equation. Invertibility of the resolving counits reduces the
result to the established ordinary_square degreewise. Resolve an arbitrary
derived object and conjugate the equality by its resolving isomorphism.
Naturality across quasi-isomorphisms proves derived_square for every object.
All edges are fixed by their unit/generator and resolving-model equations,
so this argument applies to the supplied edges, not just chosen witnesses. -/
theorem localizedOrdinaryComposition_exists {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y) (hc : Coefficients l E g h)
    (ag : Edge l E ϖ g) (ah : Edge l E ϖ h) (ac : Edge l E ϖ (h ≫ g)) :
    Nonempty (Composition l E ϖ g h ag ah ac) := by sorry

end AlgebraicGeometry.Scheme.LocalizedOrdinary
