/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.PointSystemPowerRoosData


/-! Specialization of the point-power composition argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSystemTransport.PowerRoos
variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A single family of normalized Roos comparisons for the sectionwise point compositors.
Source: Stacks 0941, lemma-derived-limit-is-ok; blueprint trace-transport,
Step 1, Global powers.
(blueprint: lem-trf-point-power-roos-comparison-specialization).

Proof: the three section identities imply the b/d/t square: evaluate at each original
coefficient level, site object and section. Both paths are the identity on the same
reindexed section. Module-sheaf and tower extensionality prove the square.
Completed inverse image is an exact product-preserving equivalence; scalar restriction
is exact. Construct the canonical product comparison by piComparison followed by the
product of b. The nth projection is the equation HasProducts. Apply the signed Roos
chain-map construction of exactProductFunctorStrictLimit, then compose with Roos(b),
to get kappa, with this same product map on both coordinates. Choose the right-derived
unit using the canonical termwise-limit/limit-of-complexes iso, whose projections are
the original limit projections. Its K-injective equation is rightDerivedFunctorUnitQ_eq.
The normalized strict Roos comparison gives theta carrying this unit to roosι on every
complex. Localize kappa conjugated by theta to obtain a and HasDerivedModel.
These choices are made once for every r, independently of a composition pair. For
(m,1,m+1), apply roosConeCompositorDescent. Its product maps equal the chosen ones
by all product projections; its kappa maps equal the chosen ones by both signed
coordinates. Its normalized theta is the same: on K-injective towers the unit is
invertible, and naturality along a K-injective resolution extends the equality.
HasDerivedModel and fully faithful precomposition with localization then identify its
a with the chosen a. Its three compositor equations are consequently the required
product, cone and derived equations for this one family, for every m, including zero.
No assertion of faithfulness of derived evaluation is involved. -/
theorem point_power_roos_comparison_specialization (P : Compositors D l E)
    (hd : HasSiteSections D l E P) (ht : HasSystemSections D l E P)
    (hb : HasRestrictionSections D l E P) :
    ∃ (N : RoosNormalization D l E) (A : Comparisons D l E),
      HasProducts D l E P A ∧ HasFirstCoordinate D l E A ∧
      HasSecondCoordinate D l E A ∧ HasDerivedModel D l E N A ∧
      ∀ m : ℕ, ProductCoherence D l E P A m ∧ ConeCoherence D l E P A m ∧
        DerivedComparisonCoherence D l E P A m := by
  sorry

end WeilConjectures.PointSystemTransport.PowerRoos
