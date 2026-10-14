/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction


/-! # Monomorphy of a selected stabilizer section -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Exact stabilizers make a selected descended section a monomorphism.

Source: Stacks Project, Tag 03SF, the finite Galois cover/permutation-set argument.
(blueprint: lem-sbc-affine-torsor-stabilizer-section-mono)

Proof: set h = algebraMap H C (ι g), V = D(h), B = D(ι g).
The finite faithfully flat map V -> B is finite etale by hEt. The ring C is a
domain, so V is connected and nonempty. The rotations are automorphisms, with
inverses supplied by hρone and hρmul. The unique-rotation condition identifies
the canonical map from the disjoint union of their graphs to V ×_B V: it is a
map of finite etale V-schemes, bijective on every geometric fibre, hence an
isomorphism. Thus V -> B is a G-torsor. The quotient by K is finite etale over B.
It is U: its ring is C[1/h]^K = (C^K)[1/h], since h is fixed and localization
at h is injective. After the faithfully flat base change V -> B, U is the
disjoint union indexed by the K-cosets of G, each a copy of V. The splitting δ
pulls back along k to a splitting of Y over V. The base and section equations
identify the given f on these copies with the deck translates of the x-section.
The reconstruction and composition laws of fixedPunctureDescentAction identify
their labels. Two such labels agree exactly when the corresponding group
elements differ by K, by hK. Thus distinct copies map to distinct summands of
the split target, by identities on V; this is a monomorphism. Monomorphy descends
under the faithfully flat base change. Both source and its image lie over B,
whose inclusion in Spec H is a monomorphism, so the result is also a
monomorphism into the displayed pullback over Spec H. No finiteness or
etaleness of Y -> Spec R is needed: its pullback to V is already split by δ.
For K = G there is one copy, for K trivial all labels are distinct; d = 0
has no selected x. -/
theorem affine_torsor_stabilizer_section_mono
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
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
        pullback p (Spec.map (CommRingCat.ofHom ι))),
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      Mono f := by sorry


end AlgebraicGeometry.Scheme
