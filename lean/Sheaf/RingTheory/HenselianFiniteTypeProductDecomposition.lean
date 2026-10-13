/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
import Sheaf.RingTheory.EtaleRetractionFiniteProductLocal
import Sheaf.RingTheory.EtaleRetractionFiniteTypeSplitting
import Sheaf.RingTheory.HenselianEtaleRetraction

/-!
# Finite-type algebras over henselian local rings

Source: Stacks Project, Algebra, Lemma 10.153.5 (Tag 04GJ)
(blueprint: lem-weil-pbc-henselian-finite-type-product-decomposition).
-/

@[expose] public section

universe u v

namespace HenselianLocalRing

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_retraction
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type (max u v)) [CommRing R'] [Algebra R R']
    (het : Algebra.Etale R R') (p : Ideal R') [p.IsPrime]
    (hp : p.comap (algebraMap R R') = IsLocalRing.maximalIdeal R)
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
        (Algebra.ofId R R') hp.symm)) :
    ∃ τ : R' →ₐ[R] R, p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom := by
  let R₁ := ULift.{v} R
  let e : R₁ ≃+* R := ULift.ringEquiv
  let : HenselianLocalRing R₁ := HenselianLocalRing.of_ringEquiv e.symm
  let f : R₁ →+* R' := (algebraMap R R').comp e.toRingHom
  let : Algebra R₁ R := e.toRingHom.toAlgebra
  let : Algebra R₁ R' := f.toAlgebra
  let : SMul R₁ R := (e.toRingHom.toAlgebra).toSMul
  let : SMul R₁ R' := (f.toAlgebra).toSMul
  have : IsScalarTower R₁ R R' := IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  have : Algebra.Etale R₁ R := RingHom.Etale.of_bijective e.bijective
  have : Algebra.Etale R R' := het
  have hf : f.Etale := Algebra.Etale.comp R₁ R R'
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective e.toRingHom e.surjective
  have : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom f).op) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale) (φ := CommRingCat.ofHom f)).mpr hf
  have hp₁ : p.comap f = IsLocalRing.maximalIdeal R₁ := by
    rw [show p.comap f = (p.comap (algebraMap R R')).comap e.toRingHom from rfl,
      hp, IsLocalRing.maximalIdeal_comap]
  have hsurj : Function.Surjective ((algebraMap R' p.ResidueField).comp f) := by
    have heq : (algebraMap R' p.ResidueField).comp (algebraMap R R') =
        (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
          (Algebra.ofId R R') hp.symm).toRingHom.comp
            (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) := by
      ext r
      exact (Ideal.ResidueField.map_algebraMap _ _ _ _ r).symm
    change Function.Surjective
      (((algebraMap R' p.ResidueField).comp (algebraMap R R')).comp e.toRingHom)
    rw [heq]
    exact (hres.2.comp (IsLocalRing.maximalIdeal R).algebraMap_residueField_surjective).comp
      e.surjective
  have hres₁ : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal R₁) p f hp₁.symm) := by
    refine ⟨RingHom.injective _, ?_⟩
    intro x
    obtain ⟨r, hr⟩ := hsurj x
    exact ⟨algebraMap R₁ (IsLocalRing.maximalIdeal R₁).ResidueField r,
      (Ideal.ResidueField.map_algebraMap _ _ _ _ r).trans hr⟩
  obtain ⟨σ, hσ, _⟩ := existsUnique_algHom_of_henselianLocalRing_etale f p hp₁ hres₁
  let τ : R' →ₐ[R] R :=
    { e.toRingHom.comp σ.toRingHom with
      commutes' := by
        intro r
        have h := σ.commutes (e.symm r)
        change e (σ (algebraMap R R' r)) = r
        change σ (f (e.symm r)) = e.symm r at h
        have he : f (e.symm r) = algebraMap R R' r := by
          change algebraMap R R' (e (e.symm r)) = _
          rw [e.apply_symm_apply]
        rw [he] at h
        exact (congrArg e h).trans (e.apply_symm_apply r) }
  refine ⟨τ, ?_⟩
  rw [← hσ]
  change (IsLocalRing.maximalIdeal R₁).comap σ.toRingHom =
    ((IsLocalRing.maximalIdeal R).comap e.toRingHom).comap σ.toRingHom
  rw [IsLocalRing.maximalIdeal_comap e.toRingHom]

/-- A finite-type algebra over a henselian local ring splits into finitely many module-finite
local algebras and a factor having no quasi-finite prime above the maximal ideal.
Source: Stacks Project, Algebra, Lemma 10.153.5 (Tag 04GJ)
(blueprint: lem-weil-pbc-henselian-finite-type-product-decomposition).

Proof:
1. Henselianity gives the étale retraction property, by
   `lem-weil-pbc-henselian-etale-retraction` (04GG (1) ⇒ (8)): every étale algebra with
   a rational point above the maximal ideal retracts to R through that point.
2. Apply `lem-weil-pbc-etale-retraction-finite-type-splitting` (04GG (11)) to obtain
   S ≃ A × B with A module-finite and no quasi-finite prime of B above the maximal ideal.
3. Apply `lem-weil-pbc-etale-retraction-finite-product-local` (04GG (10)) to A, obtaining
   finitely many local R-algebras Aᵢ and A ≃ ∏ᵢ Aᵢ. Each Aᵢ is module-finite because
   its projection from A is a surjective R-linear map, so images of generators generate it.
4. Compose the two algebra isomorphisms, keeping B unchanged. Its projection from S is
   surjective, so B is finite type; this supplies the instance needed by the recorded
   quasi-finiteness predicate. The empty product is allowed when A is zero, and B may be
   zero, when its condition on primes is vacuous. -/
theorem finiteType_exists_algEquiv_pi_prod
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [HenselianLocalRing R] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (A : Fin n → CommAlgCat.{v} R) (B : CommAlgCat.{v} R)
      (_ : Algebra.FiniteType R B),
      Nonempty (S ≃ₐ[R] (∀ i, A i) × B) ∧
        (∀ i, IsLocalRing (A i) ∧ Module.Finite R (A i)) ∧
        (∀ q : PrimeSpectrum B,
          q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
            ¬ Algebra.IsQuasiFiniteAtPrime R B q) := by
  classical
  obtain ⟨C, B, cC, cB, aC, aB, ftB, α, finC, hB⟩ :=
    Algebra.etale_retraction_finite_type_splitting R (etale_retraction R) S
  let := cC
  let := cB
  let := aC
  let := aB
  let := ftB
  let := finC
  obtain ⟨n, A, comm, alg, loc, ⟨β⟩⟩ :=
    finite_algebra_is_product_local_rings (etale_retraction R) (B := C)
  let := comm
  let := alg
  let := loc
  have : Module.Finite R (∀ i, A i) := Module.Finite.equiv β.toLinearEquiv
  refine ⟨n, (fun i ↦ CommAlgCat.of R (A i)), CommAlgCat.of R B, ftB,
    ⟨α.trans (AlgEquiv.prodCongr β (AlgEquiv.refl : B ≃ₐ[R] B))⟩, ?_, hB⟩
  intro i
  exact ⟨loc i, Module.Finite.of_pi A i⟩

end HenselianLocalRing
