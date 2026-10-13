/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
import Sheaf.RingTheory.RootAlgebraRegularAtRoot

/-! # Properties of the explicit root-cover normalization
Source: Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Abhyankar's lemma gives an etale neighborhood of the divisor generic point
for the already finite, explicitly constructed relative normalization.
Source: Stacks Project, Tags 09EB, 0BRM and 0EYG, root-extension paragraph.
(blueprint: lem-sbc-strict-hensel-root-normalization-generic-etale)

Proof: The strict henselization quotient by g is a regular local domain and g
is regular. In the root algebra the coordinate t is regular, its quotient is
H/(g), and t^|G|=g. Its height-one local ring at the root divisor is therefore
a DVR and the root extension has ramification index |G|. Generic components of
the original torsor are Galois for stabilizer subgroups of G. By 09EB their
ramification and residue degrees divide the invertible group order; hence the
extensions are tame. Apply 0BRM: every ramification index becomes one after
adjoining the group-order root, and residue extensions remain separable.
Consequently the relative normalization is etale above the generic point of
the root divisor. The supplied integral regular Cartier divisor is reduced
and has exactly the same support, so its generic point has that same image.
The assumed finite normalization is finitely presented over the Noetherian N.
Its nonetale locus is closed. Its image is closed under the finite structural
map and misses j(eta). Its complement is the required open O, on which the
whole normalization morphism is etale. No assertion of global etaleness or
purity is used, and the finiteness assertion is a separate input. -/
theorem GaloisCover.strict_hensel_root_normalization_generic_etale
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
    ¬ IsUnit g → ∀ (hN : IsLocallyNoetherian N),
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
      ∃ (O : N.Opens), j η ∈ O ∧ Etale (a.fromNormalization ∣_ O) := by sorry

end AlgebraicGeometry.Scheme
