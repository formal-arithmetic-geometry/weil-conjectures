/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite

/-!
# Surjectivity of restriction on inertia in a Galois tower

Source: Stacks Project, More on Algebra, Tag 0BSX,
`lemma-one-orbit-geometric-galois-compare`, inertia-surjectivity clause.
(blueprint: lem-dl-a1-inertia-restriction-surjective)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Ideal

/-- Restriction from upper inertia has image exactly the inertia at the contracted prime.
Thus it induces a surjective group homomorphism between these inertia subgroups.
Here `inertia` means trivial action on the quotient ring; this automatically stabilizes
its ideal and is equivalent to trivial action on the fraction field of the quotient.

Source: Stacks Project, More on Algebra, Tag 0BSX,
`lemma-one-orbit-geometric-galois-compare`, inertia-surjectivity clause.
(blueprint: lem-dl-a1-inertia-restriction-surjective)

Proof:
1. Let B and C be the integral closures in L and M, and let f : B → C be inclusion.
   Restriction commutes with f, so upper inertia restricts to lower inertia.
2. The Galois group Gal(M/L) fixes precisely L. An invariant element of C therefore
   comes from y in L; integrality descends along L → M, so y belongs to B. Thus B
   is the invariant ring of Gal(M/L) acting on C. This action is continuous when C
   is discrete: the stabilizer of each element is open in the Krull topology.
3. Lift a lower inertia element h to tau in Gal(M/K). Its translate of r contracts
   to the same prime of B as r. Profinite invariant-ring prime transitivity supplies
   rho in Gal(M/L) with rho(tau(r)) = r. Then d = rho * tau fixes r and restricts to h.
4. The action of d on C/r fixes B/q because h belongs to lower inertia. Profinite
   invariant-ring quotient lifting supplies epsilon in Gal(M/L) fixing r and having
   the same action on C/r as d. Hence epsilon⁻¹ * d acts trivially modulo r and
   restricts to h. This proves the reverse subgroup image inclusion. -/
theorem inertia_map_restrictNormalHom
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M]
    (r : Ideal (integralClosure A M)) [r.IsPrime] :
    (r.inertia (M ≃ₐ[K] M)).map (AlgEquiv.restrictNormalHom L) =
      (r.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom).inertia
        (L ≃ₐ[K] L) := by
  classical
  let : DistribMulAction (M ≃ₐ[K] M) (Ideal (integralClosure A M)) :=
    Ideal.pointwiseDistribMulAction
  let : DistribMulAction (L ≃ₐ[K] L) (Ideal (integralClosure A L)) :=
    Ideal.pointwiseDistribMulAction
  let : DistribMulAction (M ≃ₐ[L] M) (Ideal (integralClosure A M)) :=
    Ideal.pointwiseDistribMulAction
  let : MulAction (M ≃ₐ[L] M) (Set (M ≃ₐ[L] M)) := Set.mulActionSet
  let f := (IsScalarTower.toAlgHom A L M).mapIntegralClosure
  let : Algebra (integralClosure A L) (integralClosure A M) := f.toRingHom.toAlgebra
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have hequiv (σ : M ≃ₐ[K] M) (b : integralClosure A L) :
      f ((AlgEquiv.restrictNormalHom L σ) • b) = σ • f b := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes σ L b
  have : SMulCommClass (M ≃ₐ[L] M) (integralClosure A L) (integralClosure A M) := by
    refine ⟨fun σ b c ↦ Subtype.ext ?_⟩
    change σ (algebraMap L M (b : L) * (c : M)) =
      algebraMap L M (b : L) * σ (c : M)
    rw [map_mul, σ.commutes]
  have : Algebra.IsInvariant (integralClosure A L) (integralClosure A M) (M ≃ₐ[L] M) := by
    refine ⟨fun b hb ↦ ?_⟩
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (b : M)).mpr
      (fun σ ↦ congrArg Subtype.val (hb σ))
    have hyint : IsIntegral A y :=
      (isIntegral_algebraMap_iff (algebraMap L M).injective).mp (hy.symm ▸ b.property)
    exact ⟨⟨y, hyint⟩, Subtype.ext hy⟩
  let : TopologicalSpace (integralClosure A M) := ⊥
  have : DiscreteTopology (integralClosure A M) := ⟨rfl⟩
  have : ContinuousSMul (M ≃ₐ[L] M) (integralClosure A M) := by
    refine ⟨continuous_prod_of_discrete_right.mpr fun b ↦
      continuous_discrete_rng.mpr fun c ↦ ?_⟩
    rw [isOpen_iff_forall_mem_open]
    intro σ hσ
    refine ⟨σ • (MulAction.stabilizer (M ≃ₐ[L] M) (b : M) : Set (M ≃ₐ[L] M)), ?_,
      (stabilizer_isOpen_of_isIntegral (b : M)).smul σ, ⟨1, one_mem _, mul_one σ⟩⟩
    rintro _ ⟨τ, hτ, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hσ ⊢
    rw [← hσ]
    apply Subtype.ext
    change (σ * τ) • (b : M) = σ • (b : M)
    rw [mul_smul, show τ • (b : M) = b from hτ]
  have hover (η : M ≃ₐ[L] M) : AlgEquiv.restrictNormalHom L (η.restrictScalars K) = 1 := by
    ext x
    apply (algebraMap L M).injective
    exact (AlgEquiv.restrictNormal_commutes (η.restrictScalars K) L x).trans
      (η.commutes x)
  let q := r.comap f.toRingHom
  have hcontract (σ : M ≃ₐ[K] M) :
      (σ • r).comap f.toRingHom = (AlgEquiv.restrictNormalHom L σ) • q := by
    ext b
    change f b ∈ σ • r ↔ b ∈ (AlgEquiv.restrictNormalHom L σ) • q
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change σ⁻¹ • f b ∈ r ↔ f ((AlgEquiv.restrictNormalHom L σ)⁻¹ • b) ∈ r
    rw [← map_inv, hequiv]
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩ b
    change f ((AlgEquiv.restrictNormalHom L σ) • b - b) ∈ r
    rw [map_sub, hequiv]
    exact hσ _
  · intro δ hδ
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) (E := M) δ
    have hpr : (τ • r).under (integralClosure A L) = r.under (integralClosure A L) := by
      change (τ • r).comap f.toRingHom = q
      rw [hcontract, hτ]
      exact Ideal.inertia_le_stabilizer q hδ
    obtain ⟨ρ, hρ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (G := M ≃ₐ[L] M) (τ • r) r hpr
    let d := ρ.restrictScalars K * τ
    have hd : d • r = r := by
      rw [mul_smul]
      exact hρ.symm
    have hdres : AlgEquiv.restrictNormalHom L d = δ := by
      dsimp [d]
      rw [map_mul, hover, one_mul, hτ]
    have : r.LiesOver q := ⟨rfl⟩
    let dbar := Ideal.quotientEquiv r r
      (MulSemiringAction.toRingAut (M ≃ₐ[K] M) (integralClosure A M) d) hd.symm
    let dalg : (integralClosure A M ⧸ r) ≃ₐ[integralClosure A L ⧸ q]
        (integralClosure A M ⧸ r) :=
      AlgEquiv.ofRingEquiv (f := dbar) (by
        intro x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk r (d • f b) = Ideal.Quotient.mk r (f b)
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        rw [← hequiv, ← map_sub, hdres]
        exact hδ b)
    obtain ⟨ε, hε⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := M ≃ₐ[L] M) q r dalg
    let υ := ε.1.restrictScalars K
    have hυfix : υ • r = r := ε.property
    have hdε (b : integralClosure A M) : d • b - υ • b ∈ r := by
      have h := congrArg (fun e ↦ e (Ideal.Quotient.mk r b)) hε
      change Ideal.Quotient.mk r (υ • b) = Ideal.Quotient.mk r (d • b) at h
      exact (Ideal.Quotient.eq_zero_iff_mem).mp (by rw [map_sub, h, sub_self])
    refine ⟨υ⁻¹ * d, ?_, ?_⟩
    · intro b
      change (υ⁻¹ * d) • b - b ∈ r
      rw [← Ideal.smul_mem_pointwise_smul_iff (a := υ), hυfix,
        smul_sub, mul_smul, smul_inv_smul]
      exact hdε b
    · rw [map_mul, map_inv, hover, inv_one, one_mul, hdres]

end Ideal

