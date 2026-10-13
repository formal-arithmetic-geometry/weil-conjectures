/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

/-! # Tame normalization after the group-order root extension
Source: Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The pulled-back cover has a finite normalization etale near the divisor generic point.
Source: Stacks Project, Tag 0EYG, root-extension paragraph, Tag 0EYH
(pione-lemma-extend-tame-covering-normal), Tag 09EB and Tag 0BRM (lemma-abhyankar).
(blueprint: lem-sbc-strict-hensel-root-tame-normalization)

Proof: Identify the original open with D(f) using beta and its projection identity.
After passing to H, connected generic components of the finite G-torsor have
Galois groups which are stabilizer subgroups of G. The Galois degree formula gives
ramification and residue degrees dividing their orders, hence dividing |G|.
Invertibility of |G| excludes inseparable residue degrees and wild ramification.
The nonunit equation cuts out a regular local divisor in H. Its height-one local
ring is a DVR with uniformizer g. The root extension has ramification index |G|:
the root is regular and its quotient is the regular domain H/(g). Abhyankar's
lemma therefore kills each component's ramification index, with separable residue
extensions. The pulled-back cover is still tame, by flat base change of tameness.
Normalize N in this cover, component by component. Tag 0EYH makes this morphism
finite locally free without excellence, and normality identifies its restriction
with the cover on V. This identification gives zeta over V, including the stated
projection equation. The normalization is etale above the divisor generic point
by the DVR computation. The supplied regular integral Cartier divisor has the
same support as the root divisor; both are reduced, so their generic points agree.
Since N is Noetherian, the finite normalization is finitely presented. Its nonetale
locus is closed; its image is closed under the finite morphism and omits j(eta).
The complement of this image is the required target open O. No purity or global
etaleness is used, and no arbitrary normalization data are defined from this theorem. -/
theorem GaloisCover.strict_hensel_root_tame_normalization
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
    ¬ IsUnit g → IsLocallyNoetherian N →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (C : Scheme.{u}) (n : C ⟶ N),
        IsFinite n ∧ Etale (n ∣_ V) ∧
        ∃ (O : N.Opens), j η ∈ O ∧ Etale (n ∣_ O) ∧
        ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
            pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
          ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
            n ∣_ V := by
  sorry

end AlgebraicGeometry.Scheme
