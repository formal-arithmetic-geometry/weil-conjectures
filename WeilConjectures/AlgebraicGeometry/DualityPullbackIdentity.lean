/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualityPullbackData

/-! # Identity of the normalized duality transform -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The normalized transform obeys the canonical identity equation.
Source: cor-sf-duality-pullback, the identity part of naturality in `f`.
(blueprint: lem-sf-duality-pullback-normalized-identity).

Proof: evaluate normalization for the identity map using the identity-open
compactification. Identify the ordinary pullback/direct-image adjunction with the
identity adjunction through the actual pullback unit; identify the compact-support
adjunction with the identity through `finiteDualitySupportId` and its unique right
mate. The support-unit normalization identifies the dualizing mate in Verdier
exchange with the inverse of the unit. Expanding the evaluation transposes cancels
the two units and counits by their triangle identities. Thus the Hom action is
postcomposition with the dual of the inverse pullback unit, followed by the inverse
exceptional unit. Finite-Tor stability of pullback and absolute duality supplies the
source as a test object of normalization. Evaluate at its identity map and compose
with the exceptional unit. This is precisely `FiniteDualityPullbackIdentity`.
The calculation matches the actual units, including their derived normalization;
merely knowing that the identity functors are isomorphic would not suffice. -/
theorem normalized_duality_pullback_identity (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (k : Type u) [Field k] [IsAlgClosed k]
    [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    (datum : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
      [HasCompactification f] [QuasiCompact f] [IsSeparated f]
      [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
      [HasCompactification aY] [HasCompactification (f ≫ aY)],
      SixOperationsPackage Λ k f aY)
    (chi : FiniteDualityPullbackFamily Λ k)
    (hN : FiniteDualityPullbackNormalized Λ k chi) :
    FiniteDualityPullbackIdentity Λ k chi := by
  sorry


end AlgebraicGeometry.Etale
