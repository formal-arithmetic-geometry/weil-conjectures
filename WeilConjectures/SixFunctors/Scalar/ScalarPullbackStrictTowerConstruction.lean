/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictConeData

/-! # A step of strict scalar pullback cone naturality -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The balanced local formula constructs a unique natural map of strict towers.
Source: Stacks, sites-modules.tex, Tag 03EK; Steps 1--3 of the strict scalar
pullback cone argument (blueprint: lem-sf-scalar-pullback-strict-tower-construction).

Proof: the completed coefficient map has residue iota_n pi_E, and the two
inverse-image coefficient composites agree: their adjoints send each constant
section to the same constant section. First send p tensor a to p tensor iota(a).
After inverse image, extend the map by sending the two further scalars b and s
to iota(b) pi_L(s). The R_Y tensor balance follows from the residue identity;
the inverse-image balance follows from the coefficient square; the outer R_X
balance follows from pi_L a_X = iota pi_E. The maps respect restrictions and
therefore descend through sheafification. A differential or chain map changes
only p, so it commutes with this formula. A quotient transition reduces all
three coefficient factors, and red iota = iota red and red pi = pi give its
commuting square. These squares assemble the natural strict tower map. For
uniqueness, use sheaf tensor generator extensionality successively for the
outer scalar extension, inverse-image module pullback, and finite reduction;
the displayed generators determine every map locally, hence after sheafification.
No global pure-tensor presentation of arbitrary sections is required. -/
theorem scalarPullbackStrictTower_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) :
    ∃! d : scalarPullbackSourceTower l E L ι g ⟶ scalarPullbackTargetTower l E L ι g,
      ScalarPullbackGeneratorFormula l E L ι g d := by sorry

end WeilConjectures
