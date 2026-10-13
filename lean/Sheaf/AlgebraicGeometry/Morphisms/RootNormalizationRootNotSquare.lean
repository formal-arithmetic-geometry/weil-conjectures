/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # The tame root has nonzero first-order class -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The image of the root does not belong to the square of the normalized maximal ideal.

Source: Stacks Project, Tags 09EB, 0BRM, 09E7 and 0307.
(blueprint: lem-sbc-root-normalization-root-not-square)

Proof: Put n = |G|, g = b(f), and t for the adjoined root. A group is nonempty,
so n is positive. The monic relation makes A free over H; regularity of g makes
 t regular, and A/(t) = H/(g). At the root prime the maximal ideal is generated
by this nonzero t. Its regular local stalk is therefore a DVR. Localizing H at
(g) likewise gives a DVR with uniformizer g, and t^n = g gives ramification index n.
The chart beta identifies the cover before the root extension with a G-torsor over
the fraction field of H_(g). Each field factor is Galois with group a stabilizer
subgroup of G. The degree formula 09EB makes its ramification index and residue
degree divide n. In positive residue characteristic the inseparable residue degree
is a power of that characteristic; since n is a unit, this degree is one and the
ramification index is prime to the characteristic. Thus every factor is tame.
Apply 0BRM to the index-n root extension. By 09E7 the resulting normalized DVR
extensions have index one. Tag 0307 identifies their local rings and structural
maps with the actual relative-normalization stalk and stalkMap in the statement.
The image of t consequently has valuation one, whereas every element of the square
of the maximal ideal has valuation at least two. It cannot lie in that square.
For n = 1 the same calculation holds. An empty cover has no normalization point x. -/
theorem root_normalization_root_not_square
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (H : CommRingCat.{u}) [IsNoetherianRing H] (b : R ⟶ H)
    (hG : IsUnit (Nat.card G : H)) (hg : IsSMulRegular H (b.hom f))
    [IsDomain (H ⧸ Ideal.span {b.hom f})] :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    let := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    let := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)} →
      IsRegularLocalRing (N.presheaf.stalk (a.fromNormalization x)) →
      let C := a.normalization.presheaf.stalk x
      let m := IsLocalRing.maximalIdeal C
      let t := AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
        (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g))
      (a.fromNormalization.stalkMap x).hom t ∉ m * m := by
  sorry

end AlgebraicGeometry.Scheme
