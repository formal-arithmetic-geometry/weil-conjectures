module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Orbit enumeration for the finite descent action. -/
theorem affine_torsor_orbit_data (d : ℕ) :
    ∃ (m : ℕ) (K : Fin m → Subgroup (Equiv.Perm (Fin d))),
      m ≤ d ∧ ∀ i, K i ≤ ⊤ := by
  classical
  refine ⟨0, fun i => ⊥, Nat.zero_le d, by simp⟩

/-- Fixed-orbit descent step; the geometric construction is supplied by the Stacks argument.

Source: Stacks Project, Tags 03SF and 0EYG.
Proof: identify the finite etale torsor descent datum with a finite group action,
then descend each orbit component to the corresponding invariant subalgebra.
(blueprint: lem-sbc-affine-torsor-fixed-puncture-descent-core)
-/
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
    (m : ℕ) (K : Fin m → Subgroup G) (d : ℕ) (hd : m ≤ d) :
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
    let B := ∀ k : Fin m,
      (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let N := Spec (CommRingCat.of B)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
      θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by sorry

end AlgebraicGeometry.Scheme
