/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Quasi-finiteness at a prime and principal localization

Source: Stacks Project, Algebra, Lemma 10.122.6 (Tag 077H)
(blueprint: lem-weil-pbc-quasi-finite-at-prime-principal-localization).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem isOpen_singleton_fiber_iff
    {X X' Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (a : X → Y) (b : X' → Y') (i : X' → X) (j : Y' → Y)
    (hi : Topology.IsOpenEmbedding i) (hj : Function.Injective j)
    (hsq : ∀ x, a (i x) = j (b x)) (x : X') :
    IsOpen (X := a ⁻¹' {a (i x)}) {⟨i x, rfl⟩} ↔
      IsOpen (X := b ⁻¹' {b x}) {⟨x, rfl⟩} := by
  -- Injectivity on the base identifies the localized fibre with an inverse image.
  let A := a ⁻¹' {a (i x)}
  let B := b ⁻¹' {b x}
  have hB : B = i ⁻¹' A := by
    ext z
    change b z = b x ↔ a (i z) = a (i x)
    rw [hsq z, hsq x]
    exact hj.eq_iff.symm
  -- Restrict the open embedding and transport along that equality of sets.
  let e := Homeomorph.setCongr hB
  let k : B → A := (A.restrictPreimage i) ∘ e
  have hk : Topology.IsOpenEmbedding k := (hi.restrictPreimage A).comp e.isOpenEmbedding
  have hx : k ⟨x, rfl⟩ = ⟨i x, rfl⟩ := by rfl
  simpa only [Set.image_singleton, hx] using
    (hk.isOpen_iff_image_isOpen (s := {⟨x, rfl⟩})).symm

private theorem isQuasiFiniteAtPrime_iff_isOpen_fiber
    (R : Type*) (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FiniteType R S] (q : PrimeSpectrum S) :
    IsQuasiFiniteAtPrime R S q ↔
      IsOpen (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        {q.comap (algebraMap R S)}) {⟨q, rfl⟩} := by
  unfold IsQuasiFiniteAtPrime
  let e := PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S))
  simpa only [Set.image_singleton] using
    (e.isOpen_image (s := {⟨q, rfl⟩}))

/-- (blueprint: lem-weil-pbc-quasi-finite-at-prime-principal-localization)
Stacks Project, Algebra, Lemma 10.122.6 (Tag 077H): quasi-finiteness at a prime is
unchanged by principal localization of the base and target away from that prime.
The commuting square characterizes the unique induced map `φ'`. Its finite type
and the primality of the extended ideal are included in the conclusion.

Proof, following the nine steps of the node:
1. The localization universal property constructs the induced map. If `s₁, …, sₙ`
generate `S` over `R`, their images together with `1 / (φ(f)g)` generate the target
localization over `R_f` (localization-away-universal-property and finite-type-algebra).
2. Since `φ(f)g` avoids `q`, localization-prime-residue-field-iso gives the extended
prime, its contraction `q`, the contracted base prime `pR_f`, and the compatible
residue-field isomorphism `κ(p) ≅ κ(pR_f)`.
3. Fibre-ring-primes-bijection gives the two corresponding fibre primes. In the
original fibre, the image of `φ(f)` is a unit and the image of `φ(f)g` avoids its prime.
4. Algebra-tensor-pushout-universal-property and localization-away-universal-property
construct a map from the original fibre localized at that image to the new fibre.
5. The same universal properties construct the inverse map: localize the target
map and use the inverse residue-field isomorphism on the other tensor factor.
6. Check both composites on the tensor factors and localization generators;
uniqueness in these universal properties makes both composites the identity.
7. Contracting the transported fibre prime to `S` gives `q`, so uniqueness in
localization-prime-residue-field-iso and fibre-ring-primes-bijection identifies it
with the new fibre prime.
8. Principal-localization-open-immersion identifies the new fibre spectrum with
the principal open of the original fibre, carrying its distinguished prime to the
original distinguished prime (affine-spectrum and open-immersion).
9. A singleton in an open subspace is open there iff it is open in the whole space.
Apply ring-map-quasi-finite-at-prime to obtain the asserted equivalence. -/
theorem isQuasiFiniteAtPrime_iff_principalLocalization
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (f : R) (hf : f ∉ q.asIdeal.comap (algebraMap R S))
    (g : S) (hg : g ∉ q.asIdeal)
    (φ' : Localization.Away f →+* Localization.Away (algebraMap R S f * g))
    (hφ' : φ'.comp (algebraMap R (Localization.Away f)) =
      (algebraMap S (Localization.Away (algebraMap R S f * g))).comp (algebraMap R S)) :
    ∃ hft : @Algebra.FiniteType (Localization.Away f)
      (Localization.Away (algebraMap R S f * g)) _ _ φ'.toAlgebra,
    ∃ hq' : (q.asIdeal.map
      (algebraMap S (Localization.Away (algebraMap R S f * g)))).IsPrime,
      (IsQuasiFiniteAtPrime R S q ↔
        @IsQuasiFiniteAtPrime (Localization.Away f)
          (Localization.Away (algebraMap R S f * g)) _ _ φ'.toAlgebra hft
          ⟨q.asIdeal.map (algebraMap S (Localization.Away (algebraMap R S f * g))), hq'⟩) := by
  let h := algebraMap R S f * g
  let T := Localization.Away h
  let : Algebra (Localization.Away f) T := φ'.toAlgebra
  have htower : IsScalarTower R (Localization.Away f) T := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (RingHom.congr_fun hφ' r).symm
  let : FiniteType R T := inferInstance
  have hft : FiniteType (Localization.Away f) T :=
    FiniteType.of_restrictScalars_finiteType R (Localization.Away f) T
  have hh : h ∉ q.asIdeal := q.isPrime.mul_notMem hf hg
  have hd : Disjoint (Submonoid.powers h : Set S) (q.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    rintro z ⟨n, rfl⟩ hz
    exact hh (q.isPrime.mem_of_pow_mem n hz)
  have hq' : (q.asIdeal.map (algebraMap S T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h) T q.asIdeal q.isPrime hd
  let q' : PrimeSpectrum T := ⟨q.asIdeal.map (algebraMap S T), hq'⟩
  have hq : q'.comap (algebraMap S T) = q := by
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers h) T q.isPrime hd
  refine ⟨hft, hq', ?_⟩
  rw [isQuasiFiniteAtPrime_iff_isOpen_fiber R S q,
    isQuasiFiniteAtPrime_iff_isOpen_fiber (Localization.Away f) T q']
  have hsq : ∀ x : PrimeSpectrum T,
      (x.comap (algebraMap S T)).comap (algebraMap R S) =
        (x.comap φ').comap (algebraMap R (Localization.Away f)) := by
    intro x
    change x.comap ((algebraMap S T).comp (algebraMap R S)) =
      x.comap (φ'.comp (algebraMap R (Localization.Away f)))
    rw [hφ']
  have hi := PrimeSpectrum.localization_away_isOpenEmbedding T h
  have hj := PrimeSpectrum.localization_comap_injective (Localization.Away f)
    (Submonoid.powers f)
  change IsOpen (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {q.comap (algebraMap R S)}) {⟨q, rfl⟩} ↔
    IsOpen (X := PrimeSpectrum.comap φ' ⁻¹' {q'.comap φ'}) {⟨q', rfl⟩}
  rw [← hq]
  exact isOpen_singleton_fiber_iff
    (PrimeSpectrum.comap (algebraMap R S)) (PrimeSpectrum.comap φ')
    (PrimeSpectrum.comap (algebraMap S T))
    (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) hi hj hsq q'

end Algebra
