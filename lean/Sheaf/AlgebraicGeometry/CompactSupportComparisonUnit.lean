/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # The comparison unit in fixed-coefficient module sheaves

Source: the blueprint, sec-proper-base-change, thm-weil-pbc-site-comparison;
Stacks Project, Tag 099V (blueprint: thm-weil-pbc-site-comparison).

This exposes the canonical unit in the fixed-ring presentation used by compact support.
The recorded coefficient realization identifies this presentation with constant-ring
module sheaves. The existing realized-coefficient statement is reexported as well.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The actual bounded below comparison-adjunction unit is invertible on all objects.
Source: Stacks, Tag 099V; blueprint site-comparison theorem
(blueprint: thm-weil-pbc-site-comparison).

Proof: resolve a bounded below complex by a bounded below complex of injectives.
The ordinary comparison unit is invertible termwise, and comparison inverse image
sends injectives to direct-image-acyclic objects. Thus the right-derived comparison
on this complex is invertible. Their composite is the canonical derived unit.
Naturality transports invertibility from this representative to every bounded below
object and assembles its inverses into a natural isomorphism. The adjunction Hom
bijection, followed by composition with this unit, gives full faithfulness. This is
the same six-step injective-resolution proof as the realized-coefficient statement;
no condition on the individual module sheaves is imposed. -/
theorem isIso_compactSupportComparisonUnit (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    IsIso (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).unit := by
  sorry

/-- The comparison isomorphism is the inverse of the uniquely specified adjunction unit,
not an arbitrary fully-faithful witness. Source: blueprint site-comparison theorem
(blueprint: thm-weil-pbc-site-comparison). -/
noncomputable def compactSupportComparisonUnit (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    𝟭 _ ≅ (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus ⋙
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) T).rightDerivedFunctorPlus :=
  @asIso _ _ _ _ (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).unit
    (isIso_compactSupportComparisonUnit T Λ)

end AlgebraicGeometry.ProEtale
