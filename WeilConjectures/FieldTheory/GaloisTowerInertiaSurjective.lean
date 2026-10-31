/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

/-! # Decomposition and inertia in a Galois tower

Source: Stacks Project, Tag 0BSX, `lemma-one-orbit-geometric-galois-compare`, and
Tag 0BTD, `lemma-normal-pione-quotient-inertia`
(blueprint: lem-dl-a1-galois-tower-inertia-surjective).

The equalities of subgroup images assert that restriction induces surjections. Inertia
is Mathlib's subgroup of automorphisms acting trivially modulo the prime. This is exactly
triviality on the fraction field of the quotient: an automorphism fixes that field if and
only if it fixes its subring of integral fractions with denominator one.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

universe uA uF uL uM

open scoped Pointwise

namespace Ideal

/-- Restriction in a possibly infinite Galois tower maps the decomposition and inertia
subgroups onto those of the contracted prime. No residue field is assumed perfect.

Source: Stacks Project, Tag 0BSX, `lemma-one-orbit-geometric-galois-compare`
(blueprint: lem-dl-a1-galois-tower-inertia-surjective).

Proof:
1. By `lem-weil-pbc-integral-closure-algebraic-extension-normal`, the integral closure B
of A in L is a normal domain with fraction field L. Integral transitivity
(`lem-sfb-integral-element-tower-descent`) identifies the integral closure of B in M
with C. Normality and separability descend from M/F to M/L, so the prime-orbit and
residue-action assertions of `lem-dl-a1-galois-integral-closure-orbits-residues` apply.
2. Restriction preserves integral equations, contraction of the prime, and the induced
quotient and fraction-field actions. Thus it maps each of the two subgroups into the
corresponding subgroup downstairs.
3. Lift a decomposition automorphism using
`lem-dl-a1-galois-field-restriction-surjective` (Mathlib's
`AlgEquiv.restrictNormalHom_surjective`). The lifted prime and the chosen prime have the
same contraction. The prime-orbit assertion over B supplies an automorphism over L
which corrects the lift to preserve the chosen prime.
4. For an inertia automorphism downstairs choose the decomposition lift from step 3.
Its residue automorphism fixes the lower residue field. Residue-action surjectivity
over B supplies a prime-preserving automorphism over L with the same residue action.
Its inverse times the decomposition lift has trivial residue action and the required
restriction. This argument uses the actual residue fields, without perfection.
5. For the finite-quotient consequence take M to be a separable closure. Points of the
normalizations on an affine normal chart are precisely these primes, and contraction
is the map on points. The second image equality gives the assertion in Tag 0BTD. -/
theorem galoisTower_stabilizer_inertia_map
    {A : Type uA} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {F : Type uF} [Field F] [Algebra A F] [IsFractionRing A F]
    {L : Type uL} [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    {M : Type uM} [Field M] [Algebra F M] [Algebra L M] [Algebra A M]
    [IsScalarTower F L M] [IsScalarTower A F M] [IsScalarTower A L M]
    [IsGalois F M] [IsGalois F L]
    (r : Ideal (integralClosure A M)) [r.IsPrime] :
    (MulAction.stabilizer Gal(M/F) r).map (AlgEquiv.restrictNormalHom L) =
      MulAction.stabilizer Gal(L/F)
        (r.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom) ∧
    (r.inertia Gal(M/F)).map (AlgEquiv.restrictNormalHom L) =
      (r.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom).inertia
        Gal(L/F) := by
  classical
  let : DistribMulAction Gal(M/F) (Ideal (integralClosure A M)) :=
    Ideal.pointwiseDistribMulAction
  let : DistribMulAction Gal(L/F) (Ideal (integralClosure A L)) :=
    Ideal.pointwiseDistribMulAction
  let : DistribMulAction Gal(M/L) (Ideal (integralClosure A M)) :=
    Ideal.pointwiseDistribMulAction
  let : MulAction Gal(M/L) (Set Gal(M/L)) := Set.mulActionSet
  let f := (IsScalarTower.toAlgHom A L M).mapIntegralClosure
  let : Algebra (integralClosure A L) (integralClosure A M) := f.toRingHom.toAlgebra
  have hG : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  have hequiv (σ : Gal(M/F)) (b : integralClosure A L) :
      f ((AlgEquiv.restrictNormalHom L σ) • b) = σ • f b := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes σ L b
  have hcomm : SMulCommClass Gal(M/L) (integralClosure A L) (integralClosure A M) := by
    refine ⟨fun σ b c ↦ Subtype.ext ?_⟩
    change σ (algebraMap L M (b : L) * (c : M)) =
      algebraMap L M (b : L) * σ (c : M)
    rw [map_mul, σ.commutes]
  letI : Algebra.IsInvariant (integralClosure A L) (integralClosure A M) Gal(M/L) := by
    refine ⟨fun b hb ↦ ?_⟩
    obtain ⟨y, hy⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (b : M)).mpr
        (fun σ ↦ congrArg Subtype.val (hb σ))
    have hyint : IsIntegral A y :=
      (isIntegral_algebraMap_iff (algebraMap L M).injective).mp (hy.symm ▸ b.property)
    exact ⟨⟨y, hyint⟩, Subtype.ext hy⟩
  letI : TopologicalSpace (integralClosure A M) := ⊥
  letI : DiscreteTopology (integralClosure A M) := ⟨rfl⟩
  letI : ContinuousSMul Gal(M/L) (integralClosure A M) := by
    refine ⟨continuous_prod_of_discrete_right.mpr fun b ↦
      continuous_discrete_rng.mpr fun c ↦ ?_⟩
    rw [isOpen_iff_forall_mem_open]
    intro σ hσ
    refine ⟨σ • (MulAction.stabilizer Gal(M/L) (b : M) : Set Gal(M/L)), ?_,
      (stabilizer_isOpen_of_isIntegral (b : M)).smul σ, ⟨1, one_mem _, mul_one σ⟩⟩
    rintro _ ⟨τ, hτ, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hσ ⊢
    rw [← hσ]
    apply Subtype.ext
    change (σ * τ) • (b : M) = σ • (b : M)
    rw [mul_smul, show τ • (b : M) = b from hτ]
  have hover (η : Gal(M/L)) : AlgEquiv.restrictNormalHom L (η.restrictScalars F) = 1 := by
    ext x
    apply (algebraMap L M).injective
    exact (AlgEquiv.restrictNormal_commutes (η.restrictScalars F) L x).trans
      (η.commutes x)
  let q := r.comap f.toRingHom
  have hcontract (σ : Gal(M/F)) :
      (σ • r).comap f.toRingHom = (AlgEquiv.restrictNormalHom L σ) • q := by
    ext b
    change f b ∈ σ • r ↔ b ∈ (AlgEquiv.restrictNormalHom L σ) • q
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change σ⁻¹ • f b ∈ r ↔ f ((AlgEquiv.restrictNormalHom L σ)⁻¹ • b) ∈ r
    rw [← map_inv, hequiv]
  have hstab_le :
      (MulAction.stabilizer Gal(M/F) r).map (AlgEquiv.restrictNormalHom L) ≤
        MulAction.stabilizer Gal(L/F) q := by
    rintro _ ⟨σ, hσ, rfl⟩
    change σ • r = r at hσ
    change (AlgEquiv.restrictNormalHom L σ) • q = q
    rw [← hcontract σ, hσ]
  have hstab_ge :
      MulAction.stabilizer Gal(L/F) q ≤
        (MulAction.stabilizer Gal(M/F) r).map (AlgEquiv.restrictNormalHom L) := by
    intro τ hτ
    obtain ⟨σ, hστ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) (E := M) τ
    have hpr : (σ • r).under (integralClosure A L) = r.under (integralClosure A L) := by
      change (σ • r).comap f.toRingHom = q
      rw [hcontract, hστ]
      exact hτ
    obtain ⟨ρ, hρ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (G := Gal(M/L)) (σ • r) r hpr
    let d := ρ.restrictScalars F * σ
    have hd : d • r = r := by
      rw [mul_smul]
      exact hρ.symm
    have hdres : AlgEquiv.restrictNormalHom L d = τ := by
      dsimp [d]
      rw [map_mul, hover, one_mul, hστ]
    exact ⟨d, hd, hdres⟩
  have hstab :
      (MulAction.stabilizer Gal(M/F) r).map (AlgEquiv.restrictNormalHom L) =
        MulAction.stabilizer Gal(L/F) q := le_antisymm hstab_le hstab_ge
  have hinertia_le :
      (r.inertia Gal(M/F)).map (AlgEquiv.restrictNormalHom L) ≤ q.inertia Gal(L/F) := by
    rintro _ ⟨σ, hσ, rfl⟩ b
    change f ((AlgEquiv.restrictNormalHom L σ) • b - b) ∈ r
    rw [map_sub, hequiv]
    exact hσ _
  have hinertia_ge : q.inertia Gal(L/F) ≤
      (r.inertia Gal(M/F)).map (AlgEquiv.restrictNormalHom L) := by
    intro δ hδ
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) (E := M) δ
    have hpr : (τ • r).under (integralClosure A L) = r.under (integralClosure A L) := by
      change (τ • r).comap f.toRingHom = q
      rw [hcontract, hτ]
      exact Ideal.inertia_le_stabilizer q hδ
    obtain ⟨ρ, hρ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (G := Gal(M/L)) (τ • r) r hpr
    let d := ρ.restrictScalars F * τ
    have hd : d • r = r := by
      rw [mul_smul]
      exact hρ.symm
    have hdres : AlgEquiv.restrictNormalHom L d = δ := by
      dsimp [d]
      rw [map_mul, hover, one_mul, hτ]
    letI : r.LiesOver q := ⟨rfl⟩
    let dbar := Ideal.quotientEquiv r r
      (MulSemiringAction.toRingAut Gal(M/F) (integralClosure A M) d) hd.symm
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
      (G := Gal(M/L)) q r dalg
    let υ := ε.1.restrictScalars F
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
  exact ⟨hstab, le_antisymm hinertia_le hinertia_ge⟩

/-- The inertia at a point of a finite Galois normalization is exactly the image of inertia
at any chosen point above it in the separable-closure normalization.

Source: Stacks Project, Tag 0BTD, `lemma-normal-pione-quotient-inertia`, proof using
Tag 0BSX (blueprint: lem-dl-a1-galois-tower-inertia-surjective).

Proof: apply the inertia equality of `galoisTower_stabilizer_inertia_map` to the separable
closure M of F and the finite Galois extension L/F. The integral closures describe the
normalizations on affine normal charts, and contraction describes their map on points.
No maximality or residue-field perfection is needed. -/
theorem separableClosure_inertia_map
    {A : Type uA} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {F : Type uF} [Field F] [Algebra A F] [IsFractionRing A F]
    {L : Type uL} [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    {M : Type uM} [Field M] [Algebra F M] [Algebra L M] [Algebra A M]
    [IsScalarTower F L M] [IsScalarTower A F M] [IsScalarTower A L M]
    [IsSepClosure F M] [IsGalois F L] [FiniteDimensional F L]
    (r : Ideal (integralClosure A M)) [r.IsPrime] :
    (r.inertia Gal(M/F)).map (AlgEquiv.restrictNormalHom L) =
      (r.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom).inertia
        Gal(L/F) := by
  exact (galoisTower_stabilizer_inertia_map r).2

end Ideal
