/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel

/-! # Recognizing the classical part

Source: Weil conjectures blueprint, main-20261015,
`sec-proetale-coefficients/sk-thm-pe-classical-sheaves`, node statement;
Stacks Project, Tag 099T (blueprint: sk-thm-pe-classical-sheaves).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The comparison inverse image is fully faithful and its essential image is the
classical sheaves; the same comparison is an exact equivalence onto classical module
sheaves for every discrete commutative coefficient ring.

Source: Weil conjectures blueprint, main-20261015,
`sec-proetale-coefficients/sk-thm-pe-classical-sheaves`, node statement;
Stacks Project, Tag 099T (blueprint: sk-thm-pe-classical-sheaves).

Proof:
1. Apply `det-pe-classical-sheaves-unit` to obtain the invertible comparison unit and
   the induced bijection on Hom sets, giving full faithfulness.
2. Apply `det-pe-classical-sheaves-image` and the definition `sk-def-pe-classical-definition`
   (with `det-pe-classical-definition-continuity-map`) to identify the essential image
   with the continuity-map condition defining `IsClassical`.
3. Apply `det-pe-classical-sheaves-modules` to the arbitrary discrete commutative ring.
   Its module adjunction is an exact equivalence onto the full subcategory defined by
   the module continuity maps, the recorded `IsClassicalModuleFor`; the inverse image
   is additive and preserves finite limits and colimits, hence exact.
-/
theorem proEtaleClassicalSheaves (X : Scheme.{u}) :
    Nonempty
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).FullyFaithful ∧
      (∀ (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))),
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).essImage G ↔
          ProEtale.IsClassical G) ∧
      ∀ (Λ : Type (u + 1)) [CommRing Λ],
      ∃ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
          ObjectProperty.FullSubcategory (ProEtale.IsClassicalModuleFor X Λ)),
        F ⋙ ObjectProperty.ι _ =
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X ∧
          F.IsEquivalence ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  sorry

end AlgebraicGeometry
