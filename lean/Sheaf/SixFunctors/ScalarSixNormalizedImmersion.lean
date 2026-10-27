/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.ScalarSixDefinitions

/-! # The normalized locally closed scalar comparison before tower coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Normalized immersion comparison, its geometric compositor, and its specified open value.

Source: blueprint det-prop-scalar-six-pullback.proof.md (2), normalized locally closed
assembly; Stacks Tags 03DI, 03DJ, 09BM and 09AH.
(blueprint: lem-sfb-scalar-six-normalized-immersion).

Proof: transport scalar extension to section modules using the unit-normalized scalar
adjunction comparison, and transport inverse image using G.pull. The coefficient adjunct
normalization makes the transported coefficient isomorphisms cartesian. For opens use the
published scalar/open conjugate: O's mate equation identifies the two actual open units,
and open scalar conjugate normalization gives the required restriction equation. For a
closed immersion use the supported-unit scalar comparison. The exact unbounded open/closed
calculus applies because the standing schemes are finite type over a field and hence
Noetherian; complementary opens are quasi-compact. The closed supported comparison is
invertible and normalized by inverse theta. Factor an immersion as closed then open and
apply normalized immersion comparison coherence with q equal to inverse theta. This
supplies factorization independence and the gamma equation. Transport its normalized
restriction, gamma equation, and open value back through the fixed derived module
equivalences. Cancel equivalence units and counits by the triangle identities; their
resulting comparison maps are exactly scalarSixRestriction and scalarSixExtensionComp.
This assertion concerns one coefficient arrow at a time; coefficient towers are deduced
separately from normalized restriction and full faithfulness. -/
theorem scalarSixNormalizedImmersion_exists
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) :
    Nonempty (ScalarSixNormalizedImmersionData E D G C k O) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
