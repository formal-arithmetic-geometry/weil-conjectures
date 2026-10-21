/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts

/-! # Punctured Kummer charts retaining a prescribed divisor equation

Source: Stacks Project, Tags 09EB and 0EYG (lemma-abhyankar-one-divisor).
(blueprint: lem-sbc-regular-divisor-prescribed-punctured-root-chart)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Kummer charts on the divisor use the image of its specified equation.

Source: Stacks Project, Tags 09EB (lemma-galois-conclusion) and 0EYG
(lemma-abhyankar-one-divisor), strict henselization and descent paragraphs.
(blueprint: lem-sbc-regular-divisor-prescribed-punctured-root-chart)

Proof: Identify the pullback of U with D(f) by beta and pull the torsor back.
At the generic points of V(f), regularity of R and R/(f) makes the local rings
DVRs. Each connected component of the generic torsor has Galois group a stabilizer
in G. By 09EB its ramification indices and residue degrees divide that stabilizer
order, hence the unit order of G. The inseparable residue degree, a power of the
residue characteristic, is therefore one, so the cover is tame in codimension one.
At the specified point y on V(f), pass to the strict henselization. In the proof
of 0EYG the root extensions use the image of this very f: adjoin an e-th root of f
to kill the tame indices, extend the resulting unramified cover by purity, split
it over the strictly henselian base. Tag 0EYG then uses the intermediate
field calculation of More on Algebra Lemma 15.116.2 to identify each component
field with K[f^(1/n)], where n divides the chosen ramification exponent.
Normality identifies its punctured ring with R_f[T]/(T^n-f). Etaleness makes
n a unit in R_f, and tameness makes n a unit at the height-one prime (f).
The strictly henselian regular local ring is factorial and f is prime, so
these two facts make n a unit in R itself. Descend the finitely presented
isomorphisms and these unit exponents to an affine etale neighborhood of y. Thus the equation is
exactly the image g of f under the ring map corresponding to psi. Etale ascent
and base change preserve regularity of the base and divisor, while flatness
preserves injectivity of multiplication by g. Enumerate the finite components
by Fin m. Their union is D(g) in the spectrum of the product of the full root
algebras. Pullback pasting gives gamma over the new affine base, hence hgamma.
The empty product gives an empty cover; the hypothesis f in y excludes the
unit-equation case and also excludes the zero ring. No normalization or trait
localization occurs in this statement. -/
theorem GaloisCover.regular_divisor_prescribed_punctured_root_chart
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (y : Spec R) (hy : f ∈ y.asIdeal) :
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      let g := (Spec.preimage ψ).hom f
      ∃ (m : ℕ) (e : Fin m → ℕ),
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
          γ.hom ≫ V.ι ≫ q = pullback.snd (W.π ≫ i) (ψ ≫ φ) := by
  have _ := hy
  obtain ⟨S, a, z, hψ, hz, n, hn, hS, hg, hSg, d, δ, hδ⟩ :=
    W.regular_divisor_root_splitting i G R φ f hG hf β hβ y
  let ψ := Spec.map a
  let g := a.hom f
  let p := pullback.snd (W.π ≫ i) (ψ ≫ φ)
  let t := pullback.lift
    (pullback.fst (W.π ≫ i) (ψ ≫ φ) ≫ W.π) (p ≫ ψ)
    (by simp only [Category.assoc]; exact pullback.condition)
  have ht : (t ≫ β.hom) ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = p ≫ ψ := by
    simp only [Category.assoc, hβ, t, pullback.lift_snd]
  have hp : Set.range p ⊆ Set.range
      (Scheme.Opens.ι (X := Spec S) (PrimeSpectrum.basicOpen g)) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ψ (p x) ∈ PrimeSpectrum.basicOpen f
    have hx : ψ (p x) ∈ Set.range
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f)) := by
      refine ⟨(t ≫ β.hom) x, ?_⟩
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun k ↦ k x) ht
    rw [Scheme.Opens.range_ι] at hx
    exact hx
  have hj : ∃ j : pullback (W.π ≫ i) (ψ ≫ φ) ⟶
      Scheme.Opens.toScheme (X := Spec S) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec S) (PrimeSpectrum.basicOpen g) = p :=
    ⟨IsOpenImmersion.lift _ p hp, IsOpenImmersion.lift_fac _ p hp⟩
  have : IsRegularRing S := hS
  have : IsRegularRing (S ⧸ Ideal.span {g}) := hSg
  obtain ⟨T, θ, w, hθ, hw, m, e, he, hT, hh, hTh, γ, hγ⟩ :=
    root_split_cover_prescribed_cyclic_charts S g n hn hg
      (pullback.snd (W.π ≫ i) (ψ ≫ φ)) hj d z δ hδ
  have : Etale ψ := hψ
  have : Etale θ := hθ
  let ε := pullback.congrHom (rfl : W.π ≫ i = W.π ≫ i) (Category.assoc θ ψ φ)
  let α := (ε ≪≫ (pullbackLeftPullbackSndIso (W.π ≫ i) (ψ ≫ φ) θ).symm) ≪≫ γ
  have heq : (Spec.preimage (θ ≫ ψ)).hom f = (Spec.preimage θ).hom g := by
    have hmap : Spec.preimage (θ ≫ ψ) = a ≫ Spec.preimage θ := by
      apply Spec.map_injective
      simp only [Spec.map_preimage, Spec.map_comp, ψ]
    rw [hmap]
    rfl
  refine ⟨T, θ ≫ ψ, w, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hw, hz]
  · dsimp only
    rw [heq]
    refine ⟨m, e, he, hT, hh, hTh, α, ?_⟩
    simp only [α, Iso.trans_hom, Iso.symm_hom, Category.assoc, hγ,
      pullbackLeftPullbackSndIso_inv_snd_snd, ε, pullback.congrHom_hom,
      pullback.map, pullback.lift_snd, Category.comp_id]

end AlgebraicGeometry.Scheme
