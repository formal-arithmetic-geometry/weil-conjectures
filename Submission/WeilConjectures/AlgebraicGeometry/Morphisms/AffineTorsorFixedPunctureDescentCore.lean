/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantDescent
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantOrbitProduct

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme


/-- Choose the actual orbit stabilizers and descend to their fixed-ring punctures.

Source: Stacks Project, Tag 03SF and affine descent, Tag 023R.
Proof: first descend the split cover to the explicitly constructed algebra of
equivariant functions. Evaluation on orbit representatives identifies that
algebra with the product of their stabilizer fixed rings. Restrict the resulting
H-algebra isomorphism to D(ι(g)) and compose the two isomorphisms over Spec H.
The number of orbits is at most the number of split components.
(blueprint: lem-sbc-affine-torsor-fixed-puncture-descent-core) -/
theorem affine_torsor_fixed_orbits
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
    (d : ℕ) :
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
    ∀ (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t →
    ∃ (m : ℕ) (K : Fin m → Subgroup G), m ≤ d ∧
    let B := ∀ k : Fin m,
      (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let N := Spec (CommRingCat.of B)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
      θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι))  := by
  dsimp only
  intro hEt hrot T t k hk δ hδ
  obtain ⟨α, ⟨e⟩⟩ := affine_torsor_equivariant_descent
    R H g ι C G ρ hρone hρmul hne p j hj d hEt hrot T t k hk δ hδ
  obtain ⟨m, K, hmd, ⟨a⟩⟩ := affine_torsor_equivariant_orbit_product
    H C G ρ hρone hρmul d α
  let A := affineTorsorEquivariantAlgebra H C G ρ d α
  let B := ∀ k : Fin m,
    (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let VA : (Spec (CommRingCat.of A)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H A (ι g))
  let VB : (Spec (CommRingCat.of B)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H B (ι g))
  let f := Spec.map (CommRingCat.ofHom a.symm.toRingHom)
  have hf : IsIso f := by
    change IsIso (Spec.map a.symm.toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  have hV : f ⁻¹ᵁ VB = VA := by
    change PrimeSpectrum.basicOpen (a.symm (algebraMap H B (ι g))) = _
    rw [a.symm.commutes]
  let b : VA.toScheme ≅ VB.toScheme :=
    (Spec (CommRingCat.of A)).isoOfEq hV.symm ≪≫ f.preimageIso VB
  have hbase : f ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
      Spec.map (CommRingCat.ofHom (algebraMap H A)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact a.symm.commutes x
  have hb : b.hom ≫ VB.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
      VA.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H A)) := by
    simp only [b, Iso.trans_hom, Category.assoc, Hom.preimageIso_hom_ι_assoc]
    rw [Scheme.isoOfEq_hom_ι_assoc, hbase]
  let θ := (Over.forget (Spec H)).mapIso e ≪≫ b
  refine ⟨m, K, hmd, θ, ?_⟩
  change e.hom.left ≫ b.hom ≫ VB.ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap H B)) = _
  rw [hb]
  exact Over.w e.hom


end AlgebraicGeometry.Scheme
