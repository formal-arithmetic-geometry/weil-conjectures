/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

/-!
# Killing ramification by one root cover

Source: Stacks Project, Tags 09EB and 0EYG, paragraphs on the strictly henselian base
and the extension after adjoining a root.
(blueprint: lem-sbc-regular-divisor-galois-root-splitting)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A prime-to-characteristic torsor splits after one punctured root cover, locally on the base.

Source: Stacks Project, Tags 09EB and 0EYG, proof through the construction of B' and C.
(blueprint: lem-sbc-regular-divisor-galois-root-splitting)

Proof: Identify the base change of U with D(f) by beta, over Spec R. Pull back the
finite etale torsor. At a generic point of the divisor the regular local ring is a DVR,
with uniformizer f. Each generic connected component is Galois under its stabilizer
in G. By 09EB its ramification index and residue degree divide the stabilizer order,
which divides |G|. Thus the residue extension is separable and the ramification index
is prime to the residue characteristic. Pass to the strict henselization at y. Flatness
preserves the nonzerodivisor, and its quotient is the strict henselization of the divisor
local ring, hence regular. The base is regular too. Take n = |G|, which is positive
and a unit; every ramification index divides n. These divisibilities still hold after
strict henselization: the base-changed cover is again a G-torsor, so apply the same
stabilizer and DVR argument there. Adjoining an n-th root of f kills the ramification
by Abhyankar's DVR lemma (Stacks 0BRM). This root ring
is regular local and strictly henselian: the root is a nonzerodivisor, its quotient is the
regular divisor ring, and it is a local finite extension of the strictly henselian base.
Purity across the regular divisor (0EYE) extends the pulled-back cover to a finite etale
cover of this root ring. It is split because the ring is strictly henselian. Restriction
to the punctured root ring gives delta. Descend the finite presentation data, the splitting,
its inverse and the projection identity to a pointed affine etale neighborhood of y,
using 0BSK and 05N9. Shrink it until n is a unit. Regularity of the base and divisor
ascends etale locally; the equation remains a nonzerodivisor by flatness. Take g to be
the image of f under the descended ring map R to S; no new divisor data is chosen.
If y is off the divisor, split the finite etale cover on an affine etale neighborhood
inside D(f), take n = 1; the image g of f is a unit there,
so use the zero quotient's vacuous regularity.
The empty base and zero split factors cause no exception: the assertion is pointwise
and a finite disjoint union may have zero factors. -/
theorem GaloisCover.regular_divisor_root_splitting
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (y : Spec R) :
    ∃ (S : CommRingCat.{u}) (a : R ⟶ S) (z : Spec S),
      Etale (Spec.map a) ∧ (Spec.map a) z = y ∧
      let g := a.hom f
      ∃ (n : ℕ),
        (0 < n ∧ IsUnit (n : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S g ∧
        IsRegularRing (S ⧸ Ideal.span {g}) ∧
        let p := pullback.snd (W.π ≫ i) (Spec.map a ≫ φ)
        let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
        let N := Spec (CommRingCat.of A)
        let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
        let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
        ∃ (d : ℕ) (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
          δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
            pullback.snd p (V.ι ≫ q) := by sorry

end AlgebraicGeometry.Scheme
