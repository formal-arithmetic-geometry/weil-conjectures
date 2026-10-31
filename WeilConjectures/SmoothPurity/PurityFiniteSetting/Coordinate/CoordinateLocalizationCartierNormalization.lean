/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinatePoleSign
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationScalarSplice

/-! # Relative Cartier normalization of the negative coordinate localization splice

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
rank-one paragraph, and Stacks Tags 03AJ, 03PL and 0A45
(blueprint: lem-pur-coordinate-localization-cartier-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The negative of the explicit ordinary localization splice has the relative
frame-torsor normalization of the positive Cartier class. This statement concerns
ordinary sheaf Ext only; it uses neither an orientation chart nor site comparison.
Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
rank-one Cartier paragraph; Stacks Tags 03AJ, 03PL and 0A45
(blueprint: lem-pur-coordinate-localization-cartier-normalization).

Proof: let W be the complement of the zero section. By coordinateIdealFrame the
coordinate is a global generator of the zero ideal. Dualize its trivialization to
obtain the global frame e=t inverse of the dual ideal. The canonical divisor section
on W is t times the restricted frame e; its underlying torsor section tau is fixed
by this equality. The relative Cartier extension supplies E, its kernel and quotient
maps, and an equivariant torsor map killing tau and carrying every frame to supported
one. Apply principal_torsor_yoneda_sign to this frame and tau. Its first formula
identifies the integral extension class with the localization extension pushed out
along the section minus t (multiplicatively t inverse). Splice this equality with
the positive Kummer short exact sequence and its root tensor map. Naturality of
short-exact Ext classes under the integral-to-coefficient generator identifies the
result with minus coordinateLocalizationClass: the open factors are exactly the
constant pullback comparison, extension by zero of kummerEtale(t), the inverse twist
pullback, and the open counit. The closed factor is the inverse constant pullback
comparison. Thus the relative Cartier witnesses satisfy SupportedKummerBoundary
for this negative class. Every complementary open equals W, so these witnesses
supply its universal complement clause. An empty base gives zero objects throughout;
no nonemptiness or restriction on the characteristic of the coefficient ring is used. -/
theorem coordinateLocalization_cartierNormalized (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (hI : (zeroSection T).ker.IsInvertible) :
    Etale.SupportedKummerBoundary P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h) (zeroSection T) hI
      (P.exponent_isUnit (Line T) (lineProjection T ≫ aT))
      (-P.coordinateLocalizationClass h T aT) := by
  have : IsClosedImmersion (zeroSection T) := by
    dsimp only [zeroSection]
    infer_instance
  have := hI.isInvertible_dual_toModules
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual (zeroSection T).ker.toModules)
  obtain ⟨C, hC, hL, hpole⟩ := coordinatePoleSign T hI
  have hβ := (Classical.choose_spec
    (Etale.cartierPoleBoundary_existsUnique (zeroSection T) hI)).1
  unfold Etale.SupportedKummerBoundary
  intro W hW
  obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hclass⟩ := hβ W hW
  refine ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, ?_⟩
  change Etale.cartierPoleBoundary (zeroSection T) hI = hE.extClass at hclass
  rw [← hclass, hpole]
  exact P.coordinateLocalization_scalarSplice h T aT C hC hL

end WeilConjectures.PurityFiniteSetting
