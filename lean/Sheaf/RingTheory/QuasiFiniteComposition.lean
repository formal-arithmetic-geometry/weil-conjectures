/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime

import Mathlib.Topology.DiscreteSubset

/-!
# Composition of quasi-finite ring maps

Source: Stacks Project, Algebra, Lemma Tag 00PO (`lemma-quasi-finite-composition`)
(blueprint: lem-trf-quasi-finite-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace RingHom

private theorem isDiscrete_fibers_of_isQuasiFiniteAtPrime
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FiniteType)
    (hq : ∀ q : PrimeSpectrum S,
      @Algebra.IsQuasiFiniteAtPrime R S _ _ f.toAlgebra hf q)
    (p : PrimeSpectrum R) : IsDiscrete (PrimeSpectrum.comap f ⁻¹' {p}) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.FiniteType R S := hf
  refine ⟨discreteTopology_iff_isOpen_singleton.mpr ?_⟩
  rintro ⟨q, hp⟩
  change q.comap f = p at hp
  subst p
  let e := PrimeSpectrum.preimageHomeomorphFiber R S (q.comap f)
  have hopen := hq q
  change IsOpen ({e ⟨q, rfl⟩} : Set (PrimeSpectrum ((q.comap f).asIdeal.Fiber S)))
    at hopen
  exact (e.isOpen_image (s := {⟨q, rfl⟩})).mp (by
    simpa only [Set.image_singleton] using hopen)

/-- Composing two finite-type ring maps which are quasi-finite at every target prime
again gives a finite-type ring map quasi-finite at every target prime.
Source: Stacks Project, Algebra, Lemma Tag 00PO (`lemma-quasi-finite-composition`)
(blueprint: lem-trf-quasi-finite-composition).

Proof:
1. Choose finite algebra generators `b₁, ..., bₘ` for `B` over `A` and
   `c₁, ..., cₙ` for `C` over `B`, using `def-weil-pbc-finite-type-algebra`.
   The images `g(b₁), ..., g(bₘ)` together with the `cᵢ` generate `C` over `A`:
   substitute polynomials in the `bᵢ` for the coefficients of polynomials in the `cᵢ`.
   This proves the finite-type conclusion, as in Stacks Tag 00F4.
2. Fix a prime `r` of `C`, contracting to `q` in `B` and `p` in `A`.
   The hypothesis `def-weil-pbc-ring-map-quasi-finite-at-prime` isolates the point
   over `q` in the spectrum of the fibre ring. Choose a basic open singleton
   (`def-weil-affine-spectrum`). By `def-weil-pbc-localization-at-prime`, its defining
   element has the form `j(b) / j(f(a))`, with `a` outside `p`. The denominator is
   a unit, so this is also the basic open of `j(b)`. The contraction bijection
   `lem-weil-pbc-fibre-ring-primes-bijection` shows that `b` avoids `q` and that `q`
   is the only prime over `p` avoiding `b`. Apply the same argument to `B → C` to
   obtain `c` outside `r` such that `r` is the only prime over `q` avoiding `c`.
3. The product `g(b) * c` avoids `r`. If a prime `s` of `C` lies over `p` and avoids
   this product, its contraction to `B` avoids `b`, hence equals `q`; since `s`
   also avoids `c`, it equals `r`. The fibre-prime bijection identifies the basic
   open of the image of `g(b) * c` with the singleton of the fibre prime of `r`.
   This singleton is open (`def-weil-affine-spectrum`), and Step 1 supplies the
   finite-type witness needed by `def-weil-pbc-ring-map-quasi-finite-at-prime`.
   Thus the composite is quasi-finite at the arbitrary prime `r`. -/
theorem finiteType_and_isQuasiFiniteAtPrime_comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : f.FiniteType) (hg : g.FiniteType)
    (hfq : ∀ q : PrimeSpectrum B, @Algebra.IsQuasiFiniteAtPrime A B _ _ f.toAlgebra hf q)
    (hgq : ∀ r : PrimeSpectrum C, @Algebra.IsQuasiFiniteAtPrime B C _ _ g.toAlgebra hg r) :
    ∃ hgf : (g.comp f).FiniteType, ∀ r : PrimeSpectrum C,
      @Algebra.IsQuasiFiniteAtPrime A C _ _ (g.comp f).toAlgebra hgf r := by
  -- Discrete fibres are preserved by composition of continuous maps.
  let hgf := hg.comp hf
  refine ⟨hgf, fun r ↦ ?_⟩
  let : Algebra A C := (g.comp f).toAlgebra
  let : Algebra.FiniteType A C := hgf
  let p := r.comap (g.comp f)
  have hd : IsDiscrete (PrimeSpectrum.comap (g.comp f) ⁻¹' {p}) := by
    have h := (isDiscrete_fibers_of_isQuasiFiniteAtPrime f hf hfq p).preimage'
      (PrimeSpectrum.continuous_comap g).continuousOn
      (isDiscrete_fibers_of_isQuasiFiniteAtPrime g hg hgq)
    exact h
  let := hd.1
  let e := PrimeSpectrum.preimageHomeomorphFiber A C p
  change IsOpen ({e ⟨r, rfl⟩} : Set (PrimeSpectrum (p.asIdeal.Fiber C)))
  simpa only [Set.image_singleton] using e.isOpenMap _ (isOpen_discrete {⟨r, rfl⟩})

end RingHom
