/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualityPullbackData

/-! # Composition of the normalized duality transform -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The normalized transform obeys the canonical composition equation.
Source: cor-sf-duality-pullback, the composition part of naturality in `f`.
(blueprint: lem-sf-duality-pullback-normalized-composition).

Proof: for f and g expand the three Verdier exchanges into inverse projection
maps followed by the dualizing mates of support composition. Compute support on a
compatible proper/open tower; independence of the tower and associativity identify
the resulting comparisons with the specified `finiteDualitySupportComp`. Naturality
of evaluation, base-change pasting and open-extension composition show that the
projection map for the composite is the pasting of the two projection maps. Move
adjunction units and counits through these squares. Mate-pasting gives exactly
`finiteDualityExceptionalComp` on the exceptional side and
`leftDerivedUpperStarComp` on the ordinary side. The intervening evaluation
transpose and inverse transpose cancel by their triangle identity. Therefore the
Hom action of the composite is that of f followed by exceptional pullback of the
Hom action of g, with exactly the displayed comparison factors. Use the datum's
finite-Tor stability for the middle pullback and for the dual source object.
Apply normalization to the three maps and test the resulting equation on the
identity of its source. This yields `FiniteDualityPullbackComposition` for every
compatible compactification coordinate. No identity equation is assumed. -/
theorem normalized_duality_pullback_composition (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (k : Type u) [Field k] [IsAlgClosed k]
    [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    (datum : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
      [HasCompactification f] [QuasiCompact f] [IsSeparated f]
      [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
      [HasCompactification aY] [HasCompactification (f ≫ aY)],
      SixOperationsPackage Λ k f aY)
    (chi : FiniteDualityPullbackFamily Λ k)
    (hN : FiniteDualityPullbackNormalized Λ k chi) :
    FiniteDualityPullbackComposition Λ k chi := by
  sorry


end AlgebraicGeometry.Etale
