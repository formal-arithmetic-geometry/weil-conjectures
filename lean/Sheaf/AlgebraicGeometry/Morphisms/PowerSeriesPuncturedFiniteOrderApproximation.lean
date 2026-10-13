/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction

/-! # Finite-order approximation on the punctured zero section

Source: Stacks Project, Tag 0EY9, first displayed calculation at a fixed index.
(blueprint: lem-sbc-power-series-punctured-finite-order-approximation)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A section can be represented by a power series to any fixed finite order
along the punctured zero section.

Source: Stacks Project, Tag 0EY9 (lemma-fully-faithful-power-series-over-depth2),
the first displayed calculation, at a fixed index before taking inverse limits.
(blueprint: lem-sbc-power-series-punctured-finite-order-approximation)

Proof: Put B = A[[X_1,...,X_d]], I = (X_1,...,X_d), and let U be the punctured
spectrum of A. For n positive the closed subscheme Spec(B/I^n) has the same
underlying space as Spec(A). Its intersection with V is therefore the inverse
image of U under the finite affine projection to Spec(A). The A-module B/I^n
is finite free on the monomials of total degree less than n. Its associated
module restricted to U is consequently a finite direct sum of O_U. Depth-two
Hartogs identifies Gamma(U,O_U) with A, so its sections are exactly B/I^n.
Restrict s to this closed subscheme and lift its class in B/I^n to B. At each
point x of U, localization of the constant-coefficient quotient map has kernel
I times B_q, with q the inverse image of the prime x. The open-immersion stalk
isomorphisms identify this kernel with ker((z restricted to V).stalkMap x).
Localization commutes with ideal powers and quotients. Equality of the two
sections on the thickening therefore gives the asserted germ membership.
For n = 0 the power is the unit ideal, so b = 0 suffices. No compatibility
between representatives at different orders is asserted here. -/
theorem exists_powerSeries_punctured_finite_order_approximation
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map
      (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
    let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
    ∀ (s : Γ(V.toScheme, ⊤)) (n : ℕ), ∃ b : MvPowerSeries (Fin d) A,
      ∀ x : (z ⁻¹ᵁ V).toScheme,
        (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (s - r b) ∈
          (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n := by sorry

end AlgebraicGeometry.Scheme
