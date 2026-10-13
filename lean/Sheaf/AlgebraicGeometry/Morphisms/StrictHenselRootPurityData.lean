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

/-! # A normalization model ready for purity after the group-order root extension
Source: Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite normalization model is etale at the generic point of the root divisor.
Source: Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH, through the construction
of B' and tame normalization.
(blueprint: lem-sbc-strict-hensel-root-purity-data)

Proof: Identify the torsor over D(f) using beta, then base change it to H. The
canonical pointed-neighbourhood colimit is the strict henselization of the local
ring at barY. Flatness keeps g regular; quotient compatibility identifies H/(g)
with the strict henselization of the regular divisor local ring. For nonunit g,
H is regular local and H/(g) is a regular local domain. The monic root algebra
A is finite local over H, its root t is regular, and A/(t) is H/(g); hence A is
regular local. Put D=Spec(A/(t)), with its quotient closed immersion j. Since
t^n=g, its complement is V=D(g). In particular D is integral and regular,
j is an effective Cartier centre, and N is locally Noetherian.

At the generic point of D the local ring is a DVR. Each connected generic
component of the pulled-back torsor has Galois group a stabilizer in G. The
Galois degree formula 09EB makes its ramification and residue degrees divide
|G|, which is invertible, so its ramification is tame. The n-th root extension
has ramification index n there; Abhyankar 0BRM kills every component index.
Normalize N in the finite etale cover of V, taking the disjoint union over
its finitely many generic components. Tame normalization is finite (the
finite locally free tame normalization theorem 0EYH), and agrees with the cover on V by
normality. Its localization over the divisor generic point is finite etale
by Abhyankar. Etaleness is open for this finite presentation, giving O.
The agreement over V gives ζ and its projection identity. This lemma only
constructs the finite model: purity and surjectivity are proved separately.
The nonunit condition excludes the empty divisor; n>0 since G is a group. -/
theorem GaloisCover.strict_hensel_root_purity_data
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
    ¬ IsUnit g →
    IsLocallyNoetherian N ∧
      ∃ (D : Scheme.{u}) (j : D ⟶ N),
        IsRegular D ∧ IsIntegral D ∧ IsEffectiveCartierCenter j ∧
        (∀ z : N, z ∈ V ↔ z ∉ Set.range j) ∧
        ∃ (C : Scheme.{u}) (n : C ⟶ N),
          IsFinite n ∧ Etale (n ∣_ V) ∧
          ∃ (O : N.Opens) (η : D), IsGenericPoint η Set.univ ∧
            j η ∈ O ∧ Etale (n ∣_ O) ∧
          ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
              pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
            ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
              n ∣_ V := by
  sorry

end AlgebraicGeometry.Scheme
