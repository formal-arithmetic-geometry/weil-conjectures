/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedERealizationLeftSystem

/-! # Integral operations with normalized left realization comparisons

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-left-system)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures.CondensedERealization

/-- Once the individual scalar equivalences are fixed, the integral operations and
left comparisons can be chosen coherently. No rational adjunction or right realization
comparison is asserted here.
Source: Bhatt--Scholze, Proposition 6.6.11, Proposition 6.8.14(2), Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-left-system)

Proof. On each finite locally closed stratum, ordinary inverse image carries a constant
perfect integral complex to the same complex over the inverse-image coefficient ring.
Pulling back the finite strata and their trivializing covers shows that ordinary inverse
image preserves the complete constructible category. The finite quotient comparisons
identify the specified completion unit with the strict-tower augmentation, so it is
invertible on these objects. Restrict the specified completed pullback and the ordinary
derived direct image to the integral full subcategories. Integral direct-image finiteness
for separated finite-type schemes over k ensures that the latter restriction exists.
The completion unit identifies the ordinary adjunction with the completed one; restriction
through the full inclusions gives its unit and counit, with exactly the two displayed
ambient equations. The coefficient maps preserve constant integral scalars, so both
restrictions are additive and linear. On continuous coefficients the normalized coefficient
maps precompose functions. The sectionwise tensor inverse-image comparison commutes with
the scalar inclusions; deriving and then composing with the inverse completion unit gives
the left realization comparison. Descend through scalar localization using the scalar
extension comparisons of the specified At records. Every rational object has an integral
representative, so naturality of those comparisons determines the descended comparison.
Define integral composition by restriction of the specified completed compositor through
the fully faithful inclusions; the ambient normalization determines it uniquely. The
identity is the inverse completion unit followed by ordinary pullback identity. Tensor
these integral isomorphisms with one for the rational composition and identity maps.
The continuous identity comparison is induced by the actual inverse-image identity.
The coefficient composition and identity equations hold by precomposition of functions.
Their module tensor comparisons have the same equations on pure tensors; derivation and
completion-unit naturality preserve them. Full faithfulness of the coefficient encoding
and naturality of each scalar-extension comparison give the two realization coherence
equations on integral representatives, hence on every rational object. The continuous
identity normalization is the unitor law for these same inverse-image comparisons.
All arguments allow zero ranks, zero complexes and empty schemes. -/
theorem condensedE_left_system
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (atObject : ∀ T : Base k, At l E T.scheme) :
    Nonempty (LeftSystem l E k atObject) := by
  sorry

end WeilConjectures.CondensedERealization
