/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.PointSystemRoosTransportData

import Sheaf.Paper.PointSystemNormalizedComparisonData
import Sheaf.Paper.PointRestrictionWholeRoosSquare

/-! Canonical point-system comparisons in the common whole-Roos coordinates. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemRoos

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] roosF

/-- Canonical products, normalized full-tower models, and their derived comparisons.

Source: blueprint integral-model proof (3), comparison construction steps 1--4 and 6;
lem-trf-point-system-normalized-comparison-data; Stacks Tag 0941.
(blueprint: lem-trf-point-system-roos-comparison-assembly).

Proof: take the simultaneous normalized comparison data. Use its theta and eta as
models, reordering the inclusion-coordinate and quasi-isomorphism assertions. Compose
its inverse-image product comparison with the product of the inverse coefficient
identification; compose its cone comparison with roosF of that identification.
For sections use the supplied product and cone comparisons directly. The coefficient
identification is the identity on section carriers, so its inverse is too; product
projection equations then give ProductLaws. The cone-map coordinate formula gives the
two diagonal equations after composition. Use the supplied a and zeta. Restriction at
the point is the natural module transformation from the whole-Roos square theorem;
apply it termwise, then localize and compose with mapDerivedCategoryCompIso. The
localization factorization proves sigma_model, and its sections are actual restriction.
The supplied a_model and zeta_model give the other two ComparisonLaws. This constructs
only comparisons and normalizations, without asserting the transport square. -/
theorem point_system_roos_comparison_assembly (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    ∃ (models : Models D l E) (products : Products D l E r)
      (comparisons : Comparisons D l E r),
      ProductLaws D l E r products ∧
        ComparisonLaws D l E r models products comparisons := by sorry

end WeilConjectures.PointSystemRoos
