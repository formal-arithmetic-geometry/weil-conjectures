/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-!
# Composition of canonical constant-ring maps on pro-etale sites

Source: Stacks Project, Tag 09A5 (Functoriality of the pro-etale site), together with
Tags 0H7J and 00WH (constant sheaves and sheafification)
(blueprint: lem-pur-proetale-constant-ring-composition).

The inverse-image comparison is the published adjunction mate of the canonical
fibre-product associativity comparison on direct images. The coefficient maps are
exactly the adjuncts of the published constant-section maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical constant-ring coefficient maps respect composition of scheme morphisms.
Source: Stacks Project, Tag 09A5, with Tags 0H7J and 00WH
(blueprint: lem-pur-proetale-constant-ring-composition).

Proof: (1) The direct-image comparison induced by fibre-product associativity restricts
sections along the canonical isomorphism of the two base-changed objects. It preserves
constant sections, since the unit from the constant presheaf to its sheafification is
natural and the constant presheaf has identity restriction maps. This includes the empty
object (`def-weil-proetale-inverse-image`, `def-weil-pbc-constant-sheaf`).
(2) Consequently the composite of the two direct-image constant-section maps, followed
by this comparison, agrees on every constant with the map for the composite morphism.
Uniqueness of sheafification makes the ring-sheaf maps equal
(`def-weil-pbc-sheafification`).
(3) Apply successively the adjunction Hom bijections for h and k. Unit naturality and
the definition of the coefficient maps as adjuncts show that the adjunct of
h-inverse-image of c_k followed by c_h is the composite of the two direct-image
constant-section maps (`def-weil-proetale-inverse-image`).
(4) The published inverse-image comparison is the mate of the direct-image comparison.
Its defining Hom-bijection compatibility identifies the adjunct of the right-hand side
with the map of step (2). Injectivity of the composite-morphism adjunction bijection
gives the displayed equality. No invertibility of a coefficient map is assumed. -/
theorem proEtaleCoefficientInverseImageMap_comp
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleCoefficientInverseImageMap (h ≫ k) A =
      (ProEtale.supportSiteProEtaleComparisonComp CommRingCat.{u + 1} h k).hom.app
          (proEtaleConstantRing V A) ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (proEtaleCoefficientInverseImageMap k A) ≫
        proEtaleCoefficientInverseImageMap h A := by
  sorry

end AlgebraicGeometry.Scheme
