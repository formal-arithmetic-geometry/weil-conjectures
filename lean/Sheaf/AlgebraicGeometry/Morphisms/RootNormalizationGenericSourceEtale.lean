/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericSourceEtalePoint
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Ideal

/-! # Abhyankar's lemma at the generic root-divisor fibre
Source: Stacks Project, Tags 09EB, 0BRM, and 0EYG, root-extension paragraph.
(blueprint: lem-sbc-root-normalization-generic-source-etale)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- After the group-order root extension, every point of the normalization over the
root divisor generic point has an etale source neighbourhood.
Source: Stacks Project, Tags 09EB and 0BRM; Tag 0EYG, root-extension paragraph.
(blueprint: lem-sbc-root-normalization-generic-source-etale)

Proof: Set g=b(f), n=|G|, A=H[t]/(t^n-g). The monic equation makes A finite free
and Noetherian. Multiplication by g is injective on A, hence t is a nonzerodivisor.
Evaluation at t=0 identifies A/(t) with H/(g), a domain. Thus (t) is a prime
ideal of height one: the principal ideal theorem gives height at most one and
regularity of t excludes minimal primes. The assumed regularity of its prime
localization makes A_(t) a DVR with uniformizer t. The prime (g) of H similarly
has a DVR localization with uniformizer g, since its maximal ideal is generated
by the nonzerodivisor g. The extension of these DVRs has ramification index n.
The support condition on j identifies j(eta) with the prime (t): an integral
scheme's generic point maps to the generic point of its closed image, and the
Cartier immersion has precisely V(t) as image.
Use beta to identify the original cover with a finite G-torsor over D(f).
Base change to H and take the generic components near (g). A component is a
Galois field extension with group a stabilizer subgroup of G. By Tag 09EB its
ramification index and residue degree divide the stabilizer order, which divides
n. Because n is invertible in H, all these extensions are tame. Apply Tag 0BRM
to the DVR extension of index n. Every normalized component has index one and
separable residue extension. Localization of the concrete relative integral
closure is the integral closure of the DVR in these generic fields; consequently
its local maps above (t) are unramified and flat. They are etale because the
normalization is finite over the locally Noetherian N. Finite presentation makes
etaleness open on the source, giving a neighbourhood for each such point.
This asserts only source-local etaleness over one fibre. It neither constructs a
target neighbourhood nor asserts global etaleness. Empty fibres are vacuous;
n=1 is the unramified case; the domain quotient excludes the zero divisor scheme.
No arbitrary normalization witness is chosen. -/
theorem GaloisCover.root_normalization_generic_source_etale
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
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
      ∀ x : a.normalization, a.fromNormalization x = j η →
        ∃ E : a.normalization.Opens, x ∈ E ∧ Etale (E.ι ≫ a.fromNormalization) := by
  dsimp only
  intro hroot hN hp he hn D j hD hDi hj hV η hη x hx
  exact root_normalization_generic_source_etale_point i G W R φ f β hβ H b hG hg hroot hN hp
    he hn D j hD hDi hj hV η hη x hx

end AlgebraicGeometry.Scheme
