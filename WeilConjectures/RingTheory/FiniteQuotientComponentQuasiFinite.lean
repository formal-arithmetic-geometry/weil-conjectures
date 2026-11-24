/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Quasi-finiteness along a finite quotient component

A finite type algebra is quasi-finite at every prime lying on a component of its reduction
modulo an ideal that is finite over the base quotient.

## Implementation details

The ring isomorphism `e` identifies `B/IB` with `C₁ × C₂`, and `hcompat` says the
`A/I`-algebra structure on `C₁` is the one via `A/I → B/IB → C₁`. The projection
`π : B → C₁` is the quotient map composed with the first projection, and `T` is the image
of `Spec C₁`. Quasi-finiteness is in the sense of Tags 00PL and 00PK (1).

## References

* Stacks Project, More on Algebra, proof of Lemma 15.11.5 (Tag 09XH), first sentence.
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- Let `B` be a finite type `A`-algebra and `I` an ideal of `A`, and suppose
`B/IB ≅ C₁ × C₂` with `C₁` finite over `A/I`. Then `B` is quasi-finite over `A` at every
prime in the image of `Spec C₁`. -/
theorem isQuasiFiniteAtPrime_of_finite_quotient_component
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (I : Ideal A)
    (C₁ : Type w) (C₂ : Type z) [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Module.Finite (A ⧸ I) C₁]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* C₁ × C₂)
    (hcompat : ∀ a : A, algebraMap (A ⧸ I) C₁ (Ideal.Quotient.mk I a) =
      (e (Ideal.Quotient.mk _ (algebraMap A B a))).1) :
    let π : B →+* C₁ := (RingHom.fst C₁ C₂).comp
      (e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A B))))
    let T : Set (PrimeSpectrum B) := Set.range (PrimeSpectrum.comap π)
    ∀ q : PrimeSpectrum B, q ∈ T → IsQuasiFiniteAtPrime A B q := by
  classical
  let π : B →+* C₁ := (RingHom.fst C₁ C₂).comp
    (e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A B))))
  let f := PrimeSpectrum.comap π
  have hπ : Function.Surjective π :=
    Prod.fst_surjective.comp (e.surjective.comp Ideal.Quotient.mk_surjective)
  have hf := PrimeSpectrum.isClosedEmbedding_comap_of_surjective C₁ π hπ
  let g := Ideal.Quotient.mk (I.map (algebraMap A B))
  let k := PrimeSpectrum.comap ((RingHom.fst C₁ C₂).comp e.toRingHom)
  have hk : IsOpenMap k := by
    have heq : k = (PrimeSpectrum.homeomorphOfRingEquiv e).symm ∘
        (PrimeSpectrum.primeSpectrumProdHomeo (R := C₁) (S := C₂)).symm ∘
          Sum.inl := by
      funext x
      simp [k, Function.comp_def, PrimeSpectrum.primeSpectrumProdHomeo,
        PrimeSpectrum.primeSpectrumProd_symm_inl, PrimeSpectrum.homeomorphOfRingEquiv]
    rw [heq]
    exact (PrimeSpectrum.homeomorphOfRingEquiv e).symm.isOpenMap.comp
      ((PrimeSpectrum.primeSpectrumProdHomeo (R := C₁) (S := C₂)).symm.isOpenMap.comp isOpenMap_inl)
  have hg := PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ g
    Ideal.Quotient.mk_surjective
  obtain ⟨O, hO, hOk⟩ := hg.isInducing.isOpen_iff.mp
    (show IsOpen (Set.range k) by simpa using hk Set.univ isOpen_univ)
  have hfcomp : f = PrimeSpectrum.comap g ∘ k := by
    funext x
    simp [f, π, g, k, Function.comp_def]
  have hfO : Set.range f = O ∩ Set.range (PrimeSpectrum.comap g) := by
    rw [hfcomp, Set.range_comp, ← hOk, Set.image_preimage_eq_inter_range]
  have hcompat' : π.comp (algebraMap A B) =
      (algebraMap (A ⧸ I) C₁).comp (Ideal.Quotient.mk I) := by
    ext a
    exact (hcompat a).symm
  change ∀ q, q ∈ Set.range f → IsQuasiFiniteAtPrime A B q
  intro q hq
  obtain ⟨r, hr⟩ := hq
  let p₀ := r.comap (algebraMap (A ⧸ I) C₁)
  let S : Set (PrimeSpectrum C₁) :=
    PrimeSpectrum.comap (algebraMap (A ⧸ I) C₁) ⁻¹' {p₀}
  have hS : IsDiscrete S := QuasiFinite.isDiscrete_comap_preimage_singleton p₀
  have hD : IsDiscrete (f '' S) := hS.image hf.isInducing
  have hqD : q ∈ f '' S := ⟨r, rfl, hr⟩
  obtain ⟨U, hU, hUq⟩ := isOpen_inter_eq_singleton_of_mem_discrete hD hqD
  let p := q.comap (algebraMap A B)
  let F : Set (PrimeSpectrum B) := PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
  have hp : p = p₀.comap (Ideal.Quotient.mk I) := by
    dsimp [p]
    rw [← hr]
    change (r.comap π).comap (algebraMap A B) = _
    rw [← PrimeSpectrum.comap_comp_apply, hcompat', PrimeSpectrum.comap_comp_apply]
  have hDF : f '' S = Set.range f ∩ F := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨s, rfl⟩, ?_⟩
      change (s.comap π).comap (algebraMap A B) = p
      rw [← PrimeSpectrum.comap_comp_apply, hcompat', PrimeSpectrum.comap_comp_apply]
      rw [show s.comap (algebraMap (A ⧸ I) C₁) = p₀ from hs, ← hp]
    · rintro ⟨⟨s, rfl⟩, hs⟩
      refine ⟨s, ?_, rfl⟩
      apply PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
      change (s.comap π).comap (algebraMap A B) = p at hs
      rw [← PrimeSpectrum.comap_comp_apply, hcompat',
        PrimeSpectrum.comap_comp_apply, hp] at hs
      exact hs
  have hI : I ≤ p.asIdeal := by
    intro a ha
    rw [hp]
    change Ideal.Quotient.mk I a ∈ p₀.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact p₀.asIdeal.zero_mem
  have hFrange : F ⊆ Set.range (PrimeSpectrum.comap g) := by
    intro x hx
    rw [range_comap_of_surjective _ g Ideal.Quotient.mk_surjective]
    change RingHom.ker g ≤ x.asIdeal
    dsimp [g]
    rw [Ideal.mk_ker]
    apply Ideal.map_le_iff_le_comap.mpr
    change x.comap (algebraMap A B) = p at hx
    simpa [← PrimeSpectrum.comap_asIdeal, hx] using hI
  have hDO : f '' S = O ∩ F := by
    rw [hDF, hfO]
    exact (Set.inter_assoc _ _ _).trans
      (congrArg (O ∩ ·) (Set.inter_eq_right.mpr hFrange))
  have hsingle : IsOpen ({⟨q, rfl⟩} : Set F) := by
    have heq : (Subtype.val ⁻¹' (U ∩ O) : Set F) = {⟨q, rfl⟩} := by
      ext x
      have hx : x.1 ∈ F := x.2
      rw [hDO] at hUq
      have hm := Set.ext_iff.mp hUq x.1
      simpa [Set.mem_inter_iff, hx, Subtype.ext_iff] using hm
    rw [← heq]
    exact (hU.inter hO).preimage continuous_subtype_val
  unfold IsQuasiFiniteAtPrime
  change IsOpen ({(PrimeSpectrum.preimageHomeomorphFiber A B p) ⟨q, rfl⟩} : _)
  simpa only [Set.image_singleton] using
    (PrimeSpectrum.preimageHomeomorphFiber A B p).isOpenMap _ hsingle

end Algebra
