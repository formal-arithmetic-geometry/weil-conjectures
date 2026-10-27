/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Sheaf.Paper.IntegralDirectImageTowerData

import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.Paper.SmoothPurityReductionTowerNormalized
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Construct normalized scalar/pullback comparisons and the total derived restricted limit.
Source: blueprint latest direct-image.proof.md paragraph (2), and the original node's
representative-normalization step.
Proof: identify the two sequence-site presentations by their identical local sections and
restriction maps. Scalar extension commutes with inverse image on generators: send
1 tensor f*(x) to f*(1 tensor x). These maps commute with quotient transitions and descend
on flat-term K-flat complexes using the fixed universal derived reduction counit. Their
representative equation is the localization equation. The open mate is invertible by the
exact slice tensor identity. Ordinary strict reduction is left adjoint to the inverse limit
of scalar-restricted levels: transpose each tensor map, then use the limit universal property.
This gives the specified ordinary unit formula. Derive this adjunction using K-flat and
K-injective resolutions; K-injectives compute the total right derived functor. The derived
hom-equivalence on representatives is the specified normalization. All these constructions
are valid for arbitrary schemes, including the empty scheme and zero modules.
(blueprint: lem-sp-integral-tower-geometry-limits). -/
theorem normalized_geometry_limits (s : Presentation l E) :
    ∃ (q : ReductionGeometry l E s) (_hq : OpenReductionIsIso l E s q),
      Nonempty (∀ T : Scheme.{u}, Limit l E s T) := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
