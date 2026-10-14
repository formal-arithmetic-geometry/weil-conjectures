/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Etaleness of an invariant principal open of an affine torsor -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A subgroup quotient of a finite etale torsor is etale on the fixed principal open.

Source: Stacks Project, Tag 03SF, finite Galois covers and permutation sets.
(blueprint: lem-sbc-affine-torsor-invariant-puncture-etale)

Proof: put V = D(algebraMap H C h), B = D(h). Finite faithful flatness is
preserved by localization, so V -> B is finite and faithfully flat. It is
etale because its composite with the open immersion B -> Spec H is etale.
It is connected and nonempty because C is a domain and the localized element
is nonzero. The group laws make each ρ ζ invertible. By hrot the deck-graph map
from the disjoint union of G copies of V to V ×_B V is bijective on geometric
fibres. Both schemes are finite etale over V; hence this map is an isomorphism.
Therefore V -> B is a G-torsor. Finite etale descent gives its quotient by K,
corresponding to the finite coset permutation set. Affine descent identifies
its coordinate ring with C[1/h]^K. This is (C^K)[1/h]: the denominator is fixed,
and an invariant fraction has invariant numerator because localization in the
domain at a nonzero element is injective. The intersection of equalizers F is
exactly C^K, so the quotient is the displayed open U. Its structural map to B
is finite etale; compose with B -> Spec H to obtain the claimed etale map.
For K trivial this is V itself; for K = G it is B. No assumption on the order
of G being invertible is required for a torsor quotient. -/
theorem affine_torsor_invariant_puncture_etale
    (H : CommRingCat.{u}) (h : H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C h ≠ 0)
    (hEt : Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))))
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C h) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (K : Subgroup G) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of F))
      (PrimeSpectrum.basicOpen (algebraMap H F h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H F))) := by sorry

end AlgebraicGeometry.Scheme
