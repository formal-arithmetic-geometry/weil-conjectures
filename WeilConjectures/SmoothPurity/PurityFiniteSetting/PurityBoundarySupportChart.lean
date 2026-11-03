/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructureStatement

/-! # The supported-section chart and the specified supported-Hom map -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- Evaluation through the specified supported-Hom map agrees with the normalized
edge/support chart. This only compares maps on sections; it asserts no realization,
Tor bound, or site-counit compatibility.
Source: affine-line orientation proof, supported-Hom/edge identification, and
Milne, Section 9, Theorem 9.4 and Example 9.5.

Proof: represent a supported class by its specified supported-Hom morphism
from the closed coefficient unit placed in degree two. The exact closed-image
comparison identifies this source with its bounded-below etale model. This uses
the cocycle-to-map formula in SupportedHomCocycleNormalization, transported along
an injective resolution. Full faithfulness of bounded-below comparison gives an
etale antecedent of this morphism, so naturality of supportIso applies. It reduces
compatibility with this morphism
to the class of 1 on that supported coefficient object. On this object, closed
pushforward is fully faithful and the retraction collapse identifies the closed
counit with the identity. The equation global_first therefore fixes supportIso
on that class. The transport field of Comparison fixes this counit identification.
The normalized edge sends its global cocycle to the local class of the same
cocycle. Taking the closed adjunct and evaluating H^0 on 1 is precisely
gysinSupportToSections. Naturality now gives the equality on the represented
class. The single and shift comparisons in gysinSupportToHom identify degree two
with degree zero after shifting, giving the displayed shift comparison. No
invertibility or inverse chart is included in this statement.
(blueprint: lem-pur-boundary-support-chart). -/
theorem boundary_support_chart (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y))
    : ∀ v : (hyper P Y 2).obj (P.gysinClosed h Y),
      (c.edge 2).app (P.gysinClosed h Y) v =
        (globalSectionsFunctor (Modules P) Y).map
          (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
            (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y))
          (P.gysinSupportToSections h Y a
            ((c.supportIso 2).hom.app (P.gysinEtaleInput h Y) v)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
