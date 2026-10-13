/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Ideal

/-! # RootNormalizationGenericStalkResidueSeparable

Source: Stacks Project, Tags 09EB, 0BRM and 0EYG. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The residue-field extension at a normalization point above the root divisor
generic point is separable.

Source: Stacks Project, Tags 09EB (lemma-galois-conclusion), 0BRM
(lemma-abhyankar), 0EYG (pione-lemma-abhyankar-one-divisor), 0307, and 09E7.

Proof: The root t is regular since A is free over H and t^n=g is regular.
Evaluation at t=0 gives A/(t)=H/(g), hence (t) is prime. Its regular
height-one localization is a DVR. The generic point of the integral
Cartier centre with complement D(g)=D(t) maps to this prime. The local
ring H_(g) is a DVR with uniformizer g, and the root DVR extension has
index n=|G|. Via beta the cover comes from the original G-torsor over
D(f). Over the fraction field of H_(g), its connected field factors are
Galois for stabilizer subgroups, whose orders divide n. By the Galois
degree formula each residue degree divides n. In positive residue
characteristic the inseparable degree is a power of that characteristic;
as n is a unit this degree must be one. The ramification indices are
also prime to the residue characteristic. Thus these factors are tame.
Abhyankar's lemma for the root extension preserves residue separability
in the normalized base-change factors (its local adic formal smoothness
criterion gives separability of the residue extensions by Tag 09E7). Localization
of integral closure identifies these local maps with the normalization
stalk maps in the statement. Passing to residues identifies the induced
map with the canonical scheme residueFieldMap, giving precisely the
algebra structure displayed. This assertion does not claim maximal-ideal
equality. Empty fibres have no x; n=1 is the unramified case, and no
perfectness of the base residue field is assumed.
(blueprint: lem-sbc-root-normalization-generic-stalk-residue-separable) -/
theorem root_normalization_generic_stalk_residue_separable
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
    (∀ (Q : Ideal A) (hQ : Q.IsPrime),
      letI := hQ
      AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g) ∈ Q →
        IsRegularLocalRing (Localization.AtPrime Q)) →
    ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∀ (x : a.normalization), a.fromNormalization x = j η →
        letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparable (N.residueField (a.fromNormalization x))
          (a.normalization.residueField x) := by sorry

end AlgebraicGeometry.Scheme
