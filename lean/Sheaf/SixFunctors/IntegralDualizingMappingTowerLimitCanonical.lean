/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
public import Sheaf.SixFunctors.IntegralDualizingRoosModel

/-! # Mapping into the canonical integral Roos limit

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph;
Stacks 0B6E, 0D3F and 0941.
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

/-- Global Hom into the canonical limit is computed by the strict mapping tower.

Source: Stacks 0B6E, 0D3F and 0941 (blueprint:
lem-coef-integral-dualizing-mapping-tower-limit-canonical).

Proof: resolve the strict tower by a K-injective complex of injective towers and
apply the global-Hom/derived-limit comparison.  The constant-ring internal-Hom
model identifies the resulting resolved Hom tower with
`integralDualizingMappingTower`; its scalar sections are exactly the prescribed
integral sections.  Products and differentials commute with the ordinary limit,
and the split (hence surjective) transitions identify that ordinary limit with the
Roos-derived limit.  The comparison is natural in the constructible input, so it
assembles to the displayed functor isomorphism.  No finite-level dualizing
identification is used.
(blueprint: lem-coef-integral-dualizing-mapping-tower-limit-canonical). -/
theorem integralDualizing_mapping_tower_limit_canonical
    (T : NormalizedDVRTower l E X D hl) :
    Nonempty (integralDualizingGlobalHom l E X
        ((integralDualizingLimit l E X).obj T.tower) ≅
      integralDualizingMappingTower l E X T.tower ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E)) := by
  sorry

end WeilConjectures
