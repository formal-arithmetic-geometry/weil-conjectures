/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction

/-!
# Restriction to a punctured power-series thickening

Source: Stacks Project, Tag 0EY9, first displayed calculation at a fixed index.
(blueprint: lem-sbc-power-series-punctured-thickening-restriction)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Sections of each individual thickening are its quotient ring.

Source: Stacks Project, Tag 0EY9, first displayed calculation, and Tag 0BK0.
(blueprint: lem-sbc-power-series-punctured-thickening-restriction)

Proof: Put B = A[[x_1,...,x_d]], I = ker(constantCoeff), and let U be the
punctured spectrum of A. The quotient B/I^(n+1) is finite free over A on the
monomials of total degree at most n. Its spectrum has the same underlying
space as Spec A, since its variable ideal is nilpotent. Thus its inverse
image of V is the thickening of U. Push its structure sheaf along the affine
constants projection to U: it is the direct sum of copies of O_U on those
monomials. Depth-two Hartogs identifies Gamma(U,O_U) with A. Taking the
finite direct sum of this identification identifies sections of the
thickening with B/I^(n+1). The identification takes a quotient polynomial
to its restriction as a section, so its inverse is precisely the canonical
map in the conclusion, rather than an unspecified ring isomorphism.
This is a single finite-index calculation; it does not assert comparison
for compatible families, for sections on V, or for finite étale covers. -/
theorem bijective_powerSeries_punctured_thickening_restriction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (n : ℕ) :
    Function.Bijective
      ((ΓSpecIso (.of (MvPowerSeries (Fin d) A ⧸ FiniteEtale.Adic.ideal
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n))).inv ≫
        (pullback.snd V.ι (FiniteEtale.Adic.baseMap
          (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n)).appTop).hom := by sorry

end AlgebraicGeometry.Scheme
