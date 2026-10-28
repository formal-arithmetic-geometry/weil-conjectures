/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel

/-! # Uniqueness of the prescribed integral Roos limit

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph;
Stacks 08TC and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- A prescribed Roos presentation is uniquely isomorphic to the chosen derived limit.

Source: Stacks 08TC and 0941 (blueprint: lem-coef-integral-dualizing-mapping-tower-limit).

Proof: unpack the supplied triangle in `IntegralDualizingLimitPresentation` and the
canonical Roos triangle for `integralDualizingLimit`.  Both triangles have the same
successor transition endomorphism and product object.  Rotate both distinguished
triangles and apply the triangulated triangle-isomorphism theorem with the identity on
the product term.  The resulting isomorphism of the third terms, transported back
through the shift equivalence, is the required isomorphism between `M.obj` and the
chosen limit.  The extra counit clauses in the presentation are irrelevant to this
uniqueness statement.
(blueprint: lem-coef-integral-dualizing-mapping-tower-limit-roos-iso). -/
theorem integralDualizing_mapping_tower_limit_roos_iso
    (T : NormalizedDVRTower l E X D hl)
    (M : sfIntegralConstructibleCategory l E X)
    (hM : IntegralDualizingLimitPresentation l E D hl X T M.obj) :
    Nonempty (M.obj ≅ (integralDualizingLimit l E X).obj T.tower) := by
  sorry

end WeilConjectures
