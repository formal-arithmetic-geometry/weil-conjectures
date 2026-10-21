/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs

import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteStrictHenselianAlgebraEtaleSection
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility

/-!
# A section on a punctured root cover over the strict henselization

Source: Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG, strictly henselian case.
(blueprint: lem-sbc-regular-divisor-strict-hensel-root-section)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Adjoining the group-order root over the strict henselization gives a section.

Source: Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG, proof through the finite
etale extension C. (blueprint: lem-sbc-regular-divisor-strict-hensel-root-section)

Proof: Pull W back to D(f) using beta. At each generic point of the divisor the local
ring is a DVR. A connected generic component is Galois under its stabilizer in G;
09EB makes its ramification index and residue degree divide the stabilizer order,
hence the group order. Invertibility of the group order makes the ramification tame
and the residue extension separable. Pass to the strict henselization at barY. Its
base and divisor rings are regular, and the divisor equation remains a nonzerodivisor
by flatness. The pulled-back cover is still a G-torsor, so the same stabilizer argument
makes all its ramification indices divide n = |G|. If barY is on the divisor, the
root algebra H[T]/(T^n-b(f)) is a regular strictly henselian local ring: T is a
nonzerodivisor, the quotient by T is the regular divisor ring, and the root algebra
is a finite local extension of H. Abhyankar's DVR lemma 0BRM kills the ramification;
purity 0EYE extends the punctured cover to a finite etale cover of the root algebra.
This cover is split over the strictly henselian ring and is nonempty because the
original torsor is surjective. Choose one split component and restrict its section
to D(b(f)). If barY is off the divisor, b(f) is a unit and the pulled-back torsor
already splits over H; pull any one section to the root algebra. Compose the
section with the projection to W.P. Its structure equation is the pullback equation.
No arbitrary data are defined using this existential theorem. -/
theorem GaloisCover.strict_hensel_root_section
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ s : V.toScheme ⟶ W.P,
      s ≫ W.π ≫ i = V.ι ≫ q ≫ Spec.map b ≫ φ := by
  classical
  dsimp only
  let H := strictHenselizationRing barY
  let g := b.hom f
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  obtain ⟨E, p, _, hp, hsurj, δ, hδ⟩ :=
    W.strict_hensel_root_finite_etale_model i G R φ f hG hf β hβ barY b hb
  let : Etale p := hp
  obtain ⟨hlocal, hstrict⟩ := AlgebraicGeometry.strictHenselizationLocalStructure barY
  let : IsLocalRing H := hlocal
  let : IsStrictlyHenselianLocalRing H := hstrict
  have hm : ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g).Monic := by
    exact Polynomial.monic_X_pow_sub_C g (Nat.card_pos.ne')
  let : Module.Finite H A := hm.finite_adjoinRoot
  obtain ⟨σ, hσ⟩ := finite_strict_henselian_algebra_etale_section H A p hsurj
  let l : V.toScheme ⟶ pullback p V.ι :=
    pullback.lift (V.ι ≫ σ) (𝟙 _) (by
      rw [Category.assoc, hσ]
      change V.ι ≫ 𝟙 N = 𝟙 V.toScheme ≫ V.ι
      simp only [Category.comp_id, Category.id_comp])
  change δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
    pullback.snd p V.ι at hδ
  refine ⟨l ≫ δ.hom ≫ pullback.fst (W.π ≫ i)
    (V.ι ≫ q ≫ Spec.map b ≫ φ), ?_⟩
  calc
    (l ≫ δ.hom ≫ pullback.fst (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)) ≫
        W.π ≫ i =
        l ≫ δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) ≫
          (V.ι ≫ q ≫ Spec.map b ≫ φ) := by
      simp only [Category.assoc, pullback.condition]
    _ = V.ι ≫ q ≫ Spec.map b ≫ φ := by
      rw [← Category.assoc δ.hom, hδ]
      change l ≫ pullback.snd p V.ι ≫ (V.ι ≫ q ≫ Spec.map b ≫ φ) = _
      rw [← Category.assoc, show l ≫ pullback.snd p V.ι = 𝟙 _ from
        pullback.lift_snd _ _ _, Category.id_comp]

end AlgebraicGeometry.Scheme
