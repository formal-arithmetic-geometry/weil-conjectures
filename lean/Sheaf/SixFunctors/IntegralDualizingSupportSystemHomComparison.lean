/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.SixFunctors.IntegralDualizingSupportSystemHom
public import Sheaf.SixFunctors.IntegralDualizingMappingTower

/-! # Scalar adjunction for the compact-support quotient system -/

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

/-- Compare the dual of the quotient compact-support system with Hom from the
constant integral compact-support sections. There is no dualizing tower or
exceptional inverse image in this statement.

Source: prop-coef-integral-dualizing, second paragraph, last scalar-adjunction
comparison; integral compact-support reduction and point-section reduction.
(blueprint: lem-coef-integral-dualizing-support-system-hom-comparison).

Proof: resolve an integral constructible input by a K-flat complex. Integral
residue Tor invariance gives its reductions a common finite Tor interval.
Compact-support reduction with its prescribed projection maps identifies the
quotient-system support with derived scalar extension of the defined integral
compact-support object. Point-section reduction identifies the point-system
version of this extension with tensor of its integral R-module sections by the
actual quotient ring system. The identifications commute with quotient maps and
precomposition, since they use the prescribed reduction-unit comparisons.
Apply scalar tensor-restriction adjunction on the point sequence site to Hom
from this scalar extension into the regular quotient module. After restriction
its target is exactly the actual quotient R-module tower A_bullet[0]. Hom from
the constant section complex into a simultaneous K-injective resolution computes
the closed Hom in integralDualizingCoefficientHomTower. Uniqueness of the
localization comparison identifies the small-Hom and standard tower models.
All arrows are natural before localization, so the isomorphism is of functors,
not only of evaluated objects. Zero input and empty schemes are included. -/
theorem integralDualizing_support_system_hom_comparison
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S) :
    Nonempty (integralDualizingSupportSystemHom D l E X S G ≅
      (integralDualizingCompactSections l E D hl X).op ⋙
        integralDualizingCoefficientHomTower l E) := by
  sorry

end WeilConjectures
