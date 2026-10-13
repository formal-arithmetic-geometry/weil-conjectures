/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore

/-! # Descent along a connected affine torsor on a principal open

Source: Stacks Project, Tag 0EYG, normal-domain and intermediate-field paragraphs;
Tag 03SF, Galois covers and their quotients.
(blueprint: lem-sbc-affine-torsor-fixed-puncture-descent)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A split cover descends along a connected affine torsor to fixed-ring punctures.

Source: Stacks Project, Tag 03SF (quotients of Galois covers), and Tag 0EYG
(normal-domain and intermediate-field paragraphs).
(blueprint: lem-sbc-affine-torsor-fixed-puncture-descent)

Proof: Write h=iota(g). Finite faithful flatness of C over H makes its principal
open V a finite faithfully flat cover of D(h). The etale hypothesis and the
unique-rotation condition on field-valued points identify the finite etale
map from the disjoint union of G copies of V to V times_D(h) V with an
isomorphism: it is bijective on all geometric fibres. Since C is a domain and
h is nonzero, V is nonempty and connected. Pull the given splitting on T back
along k. The associativity of pullbacks and universality of scheme coproducts
give d copies of V, with their original projection to V. The torsor descent
datum permutes these copies, since every map between connected copies over V
is specified by its index. The cocycle identity is a G-action on Fin d.
Enumerate its finitely many orbits by Fin m, choose one representative from
each orbit, and take its stabilizer K. Effective finite etale descent
identifies the corresponding component with V/K. On affine rings this is
Spec of the K-invariants of C[1/h]. The action fixes h. If a/h^r is invariant,
then rho(zeta)(a)-a vanishes after localization for each zeta in K; since C
is a domain and h is nonzero, it already vanishes in C. Thus invariants
commute with this localization. The finite coproduct of these spectra is the
principal open D(h) in Spec of the product of the unlocalized fixed rings.
All identifications are over H, giving the stated projection equation. For
d=0 the orbit set is empty and the product is the zero ring, with empty Spec.
For the trivial group the torsor is an isomorphism, and this is the original
split cover. No normality or regularity is required for this descent step. -/
theorem affine_torsor_fixed_puncture_descent
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j] :
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens :=
      PrimeSpectrum.basicOpen (algebraMap H C (ι g))
    Etale (V.ι ≫ q) →
    (∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b) →
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec R) (k : V.toScheme ⟶ T),
      k ≫ t = V.ι ≫ q ≫ Spec.map (CommRingCat.ofHom ι) →
    ∀ (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t →
    ∃ (m : ℕ) (K : Fin m → Subgroup G),
      let B := ∀ k : Fin m,
        (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
      let N := Spec (CommRingCat.of B)
      let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
      let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
      ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
        θ.hom ≫ V.ι ≫ q =
        pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  dsimp
  intro hEt hrot T t k hk d δ hδ
  obtain ⟨m, Kp, hd, hKp⟩ := affine_torsor_orbit_data d
  let K : Fin m → Subgroup G := fun _ => ⊥
  obtain ⟨θ, hθ⟩ := affine_torsor_fixed_orbits
    R H g ι C G ρ hρone hρmul hne p j hj m K d hd hEt hrot T t k hk δ hδ
  exact ⟨m, K, θ, hθ⟩

end AlgebraicGeometry.Scheme
