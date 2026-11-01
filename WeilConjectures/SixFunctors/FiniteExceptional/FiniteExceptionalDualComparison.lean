/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.SixFunctors.Compact.CompactSupportNormalizedRealization
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
import all WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemResolutionModels
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import all WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicVerdierBounds
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The intrinsic finite Verdier coefficient comparison

Source: current blueprint cor-coef-finite-verdier.proof.md, paragraphs 1--3, and
lem-coef-finite-exceptional.proof.md, paragraph 2.
(blueprint: lem-sf-finite-exceptional-dual-comparison).

The actual quotient tensor and the coefficient-system quotient have the same normalized
restriction right adjoint. Its adjunction determines their comparison uniquely. The
etale dualizing object is finite-Tor constructible by finite duality of the unit;
site descent and the specified dualizing origin transport this property. Finite Verdier
bounds give closure under duality, including the empty scheme. The counit-defined
dualizing quotient comparison is invertible. Compose finite Hom coefficient change
with Hom of that dualizing comparison, correcting both source and target by the unique
quotient-model comparison. Each factor is invertible on the stated domain.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
  [QuasiCompact (T ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]

include hl in
include hl in
/-- Finite Verdier duality preserves the full finite-Tor constructible domain. -/
theorem dual_mem (n : ℕ) (K : (domain l E T n).FullSubcategory) :
    domain l E T n ((dual l E D T n).obj (op K.obj)) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (T ↘ Spec (.of D.k))
  obtain ⟨hc, a, b, ht⟩ := K.property
  have hv := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E T n K.obj hc d hd a b ht
  exact ⟨hv.1, -b - 2 * (d : ℤ), -a, hv.2.1⟩

set_option maxHeartbeats 1000000 in
-- The scalar adjunctions involve independently chosen derived presentations.
end WeilConjectures.FiniteExceptional
