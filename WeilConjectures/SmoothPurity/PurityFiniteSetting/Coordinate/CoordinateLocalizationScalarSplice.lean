/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement

/-! # Scalar forgetting of the coordinate localization splice

Source: the finite-coefficient and rank-one paragraphs of the current blueprint,
cor-pur-affine-space-zero-section-purity.proof.md; Stacks Tags 03PL and 0A45
(blueprint: lem-pur-coordinate-localization-scalar-splice).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Scalar forgetting and the integral generator carry the coordinate module
localization splice to the integral localization pushout spliced with Kummer.
This statement involves no Cartier ideal, frame torsor, exceptional functor or
orientation chart.
Source: Stacks 03PL, 0A45; the finite-coefficient paragraph of the current blueprint
(blueprint: lem-pur-coordinate-localization-scalar-splice).

Proof: forgetting scalars is exact and commutes with the two inverse-image
functors, closed direct image and extension by zero. The constant integral
generator therefore gives a morphism from the integral open-closed sequence to
the underlying coefficient open-closed sequence. More explicitly, write c_q for
the constant pullback comparison along q and g for the integral generator on each
site. The closed component is i_* applied to c_i(Z).hom, then g on the closed
site, then forget(c_i(A).inv), using the literal closed-image/forgetting equality.
The open component is the analogous composite under j_!, followed by the inverse
extension-by-zero/forgetting mate. The unit and counit squares commute by the
adjunction identities; on constant generators they both take one to one. Thus the
closed component is exactly supportedIntegralGenerator conjugated by the constant
comparisons, not a freely chosen comparison.
Use Ext.mapExactFunctor_comp_mk₀_eq_sheaf across the exact-functor comparison
isomorphisms. Naturality of the short-exact Ext class identifies pullback of the
coefficient localization extension with pushout of the integral localization extension.
By definition of kummerEtale as the inverse scalar comparison, its image is the
positive Kummer connecting class of the coordinate, followed by the root
coefficient map. The degree-zero cohomology/section adjunction expresses that
connecting class as the unit section morphism spliced with the Kummer sequence.
The normalized openSection comparison sends precisely this morphism to the
coordinate section. To see uniqueness of that comparison, use naturality on the
localization inclusion and the identity of its open source: both possible images
of that identity map to one under the monic inclusion on open sections, so are
equal. Naturality then determines the comparison on every morphism. Identify the
two integral constant-generator constructions by their common value on one under
the constant-sheaf adjunction. Move the open counit past the Kummer
extension by Ext-class naturality. Reassociate the three Yoneda factors, using
the canonical root pullback and the inverse twist pullback in the open class.
They cancel by naturality of the root coefficient map. Finally all comparisons
are additive, so the minus sign on the module class is the inverse-coordinate
section in the integral pushout. This proves the equation, including on empty
schemes and for coefficients of characteristic two. -/
theorem coordinateLocalization_scalarSplice (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (C : Etale.PrincipalTorsorComparisons.{u}) (hC : C.Normalized)
    (hL : (Etale.principalTorsorLocalization (zeroSection T)
      ((Line T).basicOpen (coordinate T))
      (coordinateLocalization_complement T)).ShortExact) :
    (Ext.mk₀ (Etale.supportedIntegralGenerator P.Coefficient (zeroSection T))).comp
        ((-P.coordinateLocalizationClass h T aT).mapExactFunctor
          (Etale.RawModuleScalarComparison.forget P.Coefficient (Line T))) (zero_add 2) =
      (((Ext.mk₀ ((Etale.lowerStar AddCommGrpCat.{u + 1} (zeroSection T)).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (zeroSection T)).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)).comp
        (hL.extClass.comp (Ext.mk₀ ((C.openSection (Line T) T (zeroSection T)
          ((Line T).basicOpen (coordinate T))
          (coordinateLocalization_complement T) (Line T).gmSheaf).symm
            (-(ULift.up (Additive.ofMul (coordinateUnit T)))))) (add_zero 1))
        (zero_add 1)).comp
        ((Line T).kummerSequence_shortExact P.exponent
          (P.exponent_isUnit (Line T) (lineProjection T ≫ aT))).extClass
        (rfl : 1 + 1 = 2)).comp
        (Ext.mk₀ (Etale.ordinaryFiniteRootMap P.Coefficient P.exponent
          (P.exponent_coefficient_eq_zero h) (Line T))) (add_zero 2) := by sorry

end WeilConjectures.PurityFiniteSetting
