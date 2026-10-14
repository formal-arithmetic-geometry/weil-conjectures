/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction
public import Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitPointLifting

/-! # Images of single stabilizer components

Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-component-image-orbit) -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Forward half of the orbit criterion; Source: Stacks Project, Tag 03SF.
Over geometric points, the finite étale cover is the disjoint union of the
deck graphs indexed by G, by the unique-rotation hypothesis. The invariant
subring construction is integral, so its basic-open map is universally
surjective. Pulling the open immersion and its section equation back along
this cover identifies its range with the union of the translated split
sections. Membership therefore supplies a deck label ζ with A(ζ)x = y;
membership is unchanged after extending the residue field to an algebraic
closure. (blueprint: lem-sbc-affine-torsor-component-image-orbit-forward) -/
theorem affine_torsor_component_image_orbit_forward
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
    [IsFinite j] [Etale j]
    (hEt : Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))))
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
    let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl)
    ∀ (f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι))) [IsOpenImmersion f],
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      ∀ (y : Fin d) (a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))),
        fixedSplitSectionOver p t k
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H C)))
          (Spec.map (CommRingCat.ofHom ι)) hk d δ hδ y a ∈ f.opensRange →
          ∃ ζ : G, fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
            p T t k hk d δ hδ ζ x = y := by sorry


/-- Backward half of the orbit criterion; Source: Stacks Project, Tag 03SF.
The same deck-graph decomposition shows that every translated section
labelled A(ζ)x lies in the pulled-back range. Since the invariant-ring map is
integral and surjective on the relevant basic opens, this membership descends
through the stabilizer quotient to the original open immersion. Thus a deck
label ζ with A(ζ)x = y gives membership of the explicit section over every
point a. (blueprint: lem-sbc-affine-torsor-component-image-orbit-backward) -/
theorem affine_torsor_component_image_orbit_backward
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
    [IsFinite j] [Etale j]
    (hEt : Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))))
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
    let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl)
    ∀ (f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι))) [IsOpenImmersion f],
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      ∀ (y : Fin d) (a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))),
        (∃ ζ : G, fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
            p T t k hk d δ hδ ζ x = y) →
        fixedSplitSectionOver p t k
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H C)))
          (Spec.map (CommRingCat.ofHom ι)) hk d δ hδ y a ∈ f.opensRange := by sorry

/-- Membership in one descended component is exactly membership in its label orbit.

Source: Stacks Project, Tag 03SF, stabilizer quotients of Galois covers.
Proof: write V = D(h) and B = D(ι g). The finite faithfully flat map V -> B is
finite étale, and the unique rotation condition makes V ×_B V the disjoint union
of the deck graphs indexed by G (check the finite étale map on geometric fibres).
For the subgroup K, C is integral over its invariant subring: each c satisfies
its monic orbit polynomial. Thus q:V -> D(h in C^K) is surjective, also after base
change. The two projection equations identify q followed by f with the explicit
section over H. Pulling this image back to V, the deck-graph description gives
exactly the union of the translates of that section. Their labels are the orbit
of x under fixedPunctureDescentAction, by the reconstruction and label laws.
In the pulled-back splitting the summands are disjoint, so a point on the y-th
section belongs to this image precisely when y is in that orbit. Membership in
an open subscheme is detected after extension of a residue field; hence this
geometric-fibre computation proves the equivalence for all ordinary points a.
For d = 0 the binder x is empty, and for G trivial the criterion selects x alone.
No completeness or distinctness of any representative family is assumed.
(blueprint: lem-sbc-affine-torsor-component-image-orbit) -/
theorem affine_torsor_component_image_orbit
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
    [IsFinite j] [Etale j]
    (hEt : Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))))
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
    let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl)
    ∀ (f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι))) [IsOpenImmersion f],
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      ∀ (y : Fin d) (a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))),
        fixedSplitSectionOver p t k
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H C)))
          (Spec.map (CommRingCat.ofHom ι)) hk d δ hδ y a ∈ f.opensRange ↔
          ∃ ζ : G, fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
            p T t k hk d δ hδ ζ x = y := by
  classical
  dsimp
  intro f _ hbase hy y a
  constructor
  · exact affine_torsor_component_image_orbit_forward R H g ι C G ρ hρone hρmul hne p j hj hEt
      hrot d T t k hk δ hδ x K hK f hbase hy y a
  · exact affine_torsor_component_image_orbit_backward R H g ι C G ρ hρone hρmul hne p j hj hEt
      hrot d T t k hk δ hδ x K hK f hbase hy y a

end AlgebraicGeometry.Scheme
