/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

/-! Kummer charts for prime-to-residue-characteristic torsors on a regular divisor complement. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The regular-divisor Kummer theorem, applied after an affine base change.

Source: Stacks Project, Tags 09EB and 0EYG, including its case off the divisor.
(blueprint: lem-sbc-regular-divisor-galois-punctured-root-chart)

Proof: Use beta to identify U times_L Spec R with D(f). Pull back the torsor to
this open; the torsor condition, finiteness and etaleness are stable under base
change. At a generic point of V(f), the local ring of the regular base is a DVR:
f is a nonzerodivisor and the regular quotient has a minimal prime of height one
in R. For each connected component of the torsor over its fraction field, the
stabilizer acts as its Galois group. Tag 09EB gives equal ramification and residue
degrees, whose product divides the stabilizer order, which divides the order of G.
The residue characteristic cannot divide these degrees because that order is a
unit. Thus every component is tame in codimension one. Apply 0EYG to obtain an
affine etale neighborhood of y and a finite disjoint union of punctured root
covers. The equation is the pullback of f; the exponents are positive units.
The new base is regular by etale ascent, its divisor is regular by etale base
change, and its equation remains a nonzerodivisor by flatness. Enumerate the finite
components by Fin m. A finite disjoint union of affine schemes is the spectrum
of their product ring; localizing this product at the equation gives precisely
the displayed basic open of the product of full root algebras. Pullback pasting
identifies the torsor base change with pullback (W.pi followed by i) along
(psi followed by phi). All these identifications are over Spec S and hence give
the displayed equality. Off the divisor, split the finite etale cover etale
locally and use equation 1 and exponents 1; the quotient is the zero ring and is
regular. Empty covers use m = 0. No smooth morphism or valuation ring is required. -/
theorem GaloisCover.regular_divisor_punctured_root_chart
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (y : Spec R) :
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      ∃ (m : ℕ) (g : S) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S g ∧
        IsRegularRing (S ⧸ Ideal.span {g}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C g)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C g))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C g)) g)
        ∃ γ : pullback (W.π ≫ i) (ψ ≫ φ) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd (W.π ≫ i) (ψ ≫ φ) := by sorry

end AlgebraicGeometry.Scheme
