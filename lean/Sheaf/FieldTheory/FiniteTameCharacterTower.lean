/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.FieldTheory.FiniteDVRTameInertia
public import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Invariant.Basic

/-!
# Wild inertia surjectivity and scaled tame characters in finite towers

Source: Stacks Project, More on Algebra, Tags 0BU7 and 0BU8,
`literature/stacks-project/more-algebra.tex`, Lemma `lemma-compare-inertia` and
Remark `remark-canonical-inertia-character`.
(blueprint: lem-exc-finite-tame-character-tower)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped Pointwise

namespace IsDiscreteValuationRing

private theorem restriction_equivariant
    (A : Type u) [CommRing A]
    (K : Type v) [Field K] [Algebra A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [Normal K L]
    (σ : Gal(M/K)) (x : integralClosure A L) :
    (IsScalarTower.toAlgHom A L M).mapIntegralClosure
      ((AlgEquiv.restrictNormalHom L σ) • x) =
    σ • (IsScalarTower.toAlgHom A L M).mapIntegralClosure x := by
  apply Subtype.ext
  exact AlgEquiv.restrictNormal_commutes σ L x
private theorem restriction_stabilizer_mem
    (A : Type u) [CommRing A]
    (K : Type v) [Field K] [Algebra A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [Normal K L]
    (N : Ideal (integralClosure A M)) (P : Ideal (integralClosure A L))
    (hP : P = N.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom)
    (σ : Gal(M/K)) (hσ : σ ∈ MulAction.stabilizer Gal(M/K) N) :
    AlgEquiv.restrictNormalHom L σ ∈ MulAction.stabilizer Gal(L/K) P := by
  change σ • N = N at hσ
  change (AlgEquiv.restrictNormalHom L σ) • P = P
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hP]
  change (IsScalarTower.toAlgHom A L M).mapIntegralClosure
      ((AlgEquiv.restrictNormalHom L σ)⁻¹ • x) ∈ N ↔
    (IsScalarTower.toAlgHom A L M).mapIntegralClosure x ∈ N
  rw [← map_inv, restriction_equivariant A K L M]
  rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hσ]
private theorem restriction_inertia_mem
    (A : Type u) [CommRing A]
    (K : Type v) [Field K] [Algebra A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [Normal K L]
    (N : Ideal (integralClosure A M)) (P : Ideal (integralClosure A L))
    (hP : P = N.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom)
    (σ : Gal(M/K)) (hσ : σ ∈ N.inertia Gal(M/K)) :
    AlgEquiv.restrictNormalHom L σ ∈ P.inertia Gal(L/K) := by
  intro x
  rw [hP]
  change (IsScalarTower.toAlgHom A L M).mapIntegralClosure
    ((AlgEquiv.restrictNormalHom L σ) • x - x) ∈ N
  rw [map_sub, restriction_equivariant A K L M]
  exact hσ _

/-- Restriction is surjective on decomposition and inertia groups at compatible primes.

Source: Stacks Project, More on Algebra, Tag 0BSX, lemma-one-orbit-geometric-galois-compare.
(blueprint: lem-exc-finite-tame-character-tower)

Proof: Both integral closures are normal domains with fraction fields L and M, and the
upper closure is also the integral closure of the lower one in M. Restriction of field
Galois automorphisms is surjective. Given a lower decomposition element, lift it to M.
Its translate of the upper prime has the same contraction. Prime conjugacy over the lower
normalization supplies an automorphism over L correcting the lift to fix the upper prime.
For a lower inertia element, the corrected lift acts on the upper residue field fixing
the lower residue field. Surjectivity of the residue action for the extension M/L supplies
an automorphism over L with the same residue action. Multiplying by its inverse produces
an inertia lift. Contraction proves preservation of stabilizers; applying the integral
closure inclusion to sigma(b)-b proves preservation of inertia. These restrictions are
homomorphisms because restriction of field automorphisms is a homomorphism. -/
private theorem finite_normalization_restriction_surjective
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (𝔫M : Ideal (integralClosure A M)) [𝔫M.IsMaximal]
    (𝔫L : Ideal (integralClosure A L)) [𝔫L.IsMaximal]
    (hcomp : 𝔫L = Ideal.comap
      (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M) :
    ∃ (rD : MulAction.stabilizer Gal(M/K) 𝔫M →* MulAction.stabilizer Gal(L/K) 𝔫L),
      Function.Surjective rD ∧
      (∀ σ : MulAction.stabilizer Gal(M/K) 𝔫M,
        (rD σ).1 = AlgEquiv.restrictNormalHom L σ.1) ∧
    ∃ (rI : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L)),
      Function.Surjective rI ∧
      (∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        (rI σ).1.1 = AlgEquiv.restrictNormalHom L σ.1.1)  := by
  classical
  let f := (IsScalarTower.toAlgHom A L M).mapIntegralClosure
  let : Algebra (integralClosure A L) (integralClosure A M) := f.toRingHom.toAlgebra
  have : FiniteDimensional L M := Module.Finite.right K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have : SMulCommClass Gal(M/L) (integralClosure A L) (integralClosure A M) := by
    refine ⟨fun σ b c ↦ Subtype.ext ?_⟩
    change σ (algebraMap L M (b : L) * (c : M)) =
      algebraMap L M (b : L) * σ (c : M)
    rw [map_mul, σ.commutes]
  have : Algebra.IsInvariant (integralClosure A L) (integralClosure A M) Gal(M/L) := by
    refine ⟨fun b hb ↦ ?_⟩
    obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) (b : M)).mpr
      (fun σ ↦ congrArg Subtype.val (hb σ))
    have hyint : IsIntegral A y :=
      (isIntegral_algebraMap_iff (algebraMap L M).injective).mp (hy.symm ▸ b.property)
    exact ⟨⟨y, hyint⟩, Subtype.ext hy⟩
  have hover (η : Gal(M/L)) : AlgEquiv.restrictNormalHom L (η.restrictScalars K) = 1 := by
    ext x
    apply (algebraMap L M).injective
    exact (AlgEquiv.restrictNormal_commutes (η.restrictScalars K) L x).trans
      (η.commutes x)
  have hcontract (σ : Gal(M/K)) :
      (σ • 𝔫M).comap f.toRingHom = (AlgEquiv.restrictNormalHom L σ) • 𝔫L := by
    ext b
    change f b ∈ σ • 𝔫M ↔ b ∈ (AlgEquiv.restrictNormalHom L σ) • 𝔫L
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, hcomp]
    change σ⁻¹ • f b ∈ 𝔫M ↔ f ((AlgEquiv.restrictNormalHom L σ)⁻¹ • b) ∈ 𝔫M
    rw [← map_inv, restriction_equivariant A K L M]
  let rD : MulAction.stabilizer Gal(M/K) 𝔫M →*
      MulAction.stabilizer Gal(L/K) 𝔫L :=
    ((AlgEquiv.restrictNormalHom L).comp
      (MulAction.stabilizer Gal(M/K) 𝔫M).subtype).codRestrict _
        (fun σ ↦ restriction_stabilizer_mem A K L M 𝔫M 𝔫L hcomp σ σ.property)
  have hrD : Function.Surjective rD := by
    intro δ
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) (E := M) δ.1
    have hpr : (τ • 𝔫M).under (integralClosure A L) = 𝔫M.under (integralClosure A L) := by
      change (τ • 𝔫M).comap f.toRingHom = 𝔫M.comap f.toRingHom
      rw [hcontract, hτ, ← hcomp]
      exact δ.property
    obtain ⟨η, hη⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      (integralClosure A L) (integralClosure A M) Gal(M/L) (τ • 𝔫M) 𝔫M hpr
    have hfix : (η.restrictScalars K * τ) • 𝔫M = 𝔫M := by
      rw [mul_smul]
      exact hη.symm
    refine ⟨⟨η.restrictScalars K * τ, hfix⟩, Subtype.ext ?_⟩
    change AlgEquiv.restrictNormalHom L (η.restrictScalars K * τ) = δ.1
    rw [map_mul, hover, one_mul, hτ]
  let rI : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
      𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L) :=
    (rD.comp (𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M)).subtype).codRestrict _
      fun σ ↦ restriction_inertia_mem A K L M 𝔫M 𝔫L hcomp σ.1.1 σ.property
  refine ⟨rD, hrD, fun _ ↦ rfl, rI, ?_, fun _ ↦ rfl⟩
  intro δ
  obtain ⟨τ, hτ⟩ := hrD δ.1
  have : 𝔫M.LiesOver 𝔫L := ⟨hcomp⟩
  let τbar := Ideal.quotientEquiv 𝔫M 𝔫M
    (MulSemiringAction.toRingAut Gal(M/K) (integralClosure A M) τ.1) τ.property.symm
  let τalg : (integralClosure A M ⧸ 𝔫M) ≃ₐ[integralClosure A L ⧸ 𝔫L]
      (integralClosure A M ⧸ 𝔫M) :=
    AlgEquiv.ofRingEquiv (f := τbar) (by
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk 𝔫M (τ.1 • f b) = Ideal.Quotient.mk 𝔫M (f b)
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      rw [← restriction_equivariant A K L M, ← map_sub]
      have hδ := δ.property b
      have heq : AlgEquiv.restrictNormalHom L τ.1 = δ.1.1 :=
        congrArg Subtype.val hτ
      rw [heq]
      exact hcomp ▸ hδ)
  obtain ⟨η, hη⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(M/L) 𝔫L 𝔫M τalg
  let υ := η.1.restrictScalars K
  have hυfix : υ • 𝔫M = 𝔫M := η.property
  have hτres (b : integralClosure A M) : τ.1 • b - υ • b ∈ 𝔫M := by
    have h := congrArg (fun e ↦ e (Ideal.Quotient.mk 𝔫M b)) hη
    change Ideal.Quotient.mk 𝔫M (υ • b) = Ideal.Quotient.mk 𝔫M (τ.1 • b) at h
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (by rw [map_sub, h, sub_self])
  have hinertia : (υ⁻¹ * τ.1) ∈ 𝔫M.inertia Gal(M/K) := by
    intro b
    change (υ⁻¹ * τ.1) • b - b ∈ 𝔫M
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := υ), hυfix,
      smul_sub, mul_smul, smul_inv_smul]
    exact hτres b
  have hfix : (υ⁻¹ * τ.1) ∈ MulAction.stabilizer Gal(M/K) 𝔫M :=
    Ideal.inertia_le_stabilizer 𝔫M hinertia
  refine ⟨⟨⟨υ⁻¹ * τ.1, hfix⟩, hinertia⟩, Subtype.ext (Subtype.ext ?_)⟩
  change AlgEquiv.restrictNormalHom L (υ⁻¹ * τ.1) = δ.1.1
  rw [map_mul, map_inv, hover, inv_one, one_mul]
  exact congrArg Subtype.val hτ

private theorem local_embedding_injective
    {B : Type*} [CommRing B] [IsDomain B] {F : Type*} [Field F]
    [Algebra B F] (N : Ideal B) [N.IsPrime]
    (j : Localization.AtPrime N →+* F)
    (hj : ∀ b : B, j (algebraMap B (Localization.AtPrime N) b) = algebraMap B F b)
    (hinj : Function.Injective (algebraMap B F)) : Function.Injective j := by
  apply IsLocalization.injective_of_map_algebraMap_zero (Localization.AtPrime N)
    (M := N.primeCompl) j
  intro b hb
  rw [hj] at hb
  have h : b = 0 := hinj (hb.trans (map_zero _).symm)
  simp only [h, map_zero]

private theorem local_inertia_action
    {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]
    (N : Ideal B) [N.IsPrime] (σ : N.inertia (MulAction.stabilizer G N)) :
    ∃ s : Localization.AtPrime N ≃+* Localization.AtPrime N,
      (∀ b : B, s (algebraMap B (Localization.AtPrime N) b) =
        algebraMap B (Localization.AtPrime N) (σ.1.1 • b)) ∧
      ∀ x, IsLocalRing.residue (Localization.AtPrime N) (s x) =
        IsLocalRing.residue (Localization.AtPrime N) x := by
  have hs : σ.1.1 • N = N := σ.1.property
  have hc : N = N.comap (MulSemiringAction.toRingAut G B σ.1.1) := by
    ext b
    change b ∈ N ↔ σ.1.1 • b ∈ N
    exact (Ideal.smul_mem_pointwise_smul_iff (a := σ.1.1)).symm.trans
      (by rw [hs])
  let s := Localization.localRingEquiv N N (MulSemiringAction.toRingAut G B σ.1.1) hc
  have hsmap (b : B) : s (algebraMap B (Localization.AtPrime N) b) =
      algebraMap B (Localization.AtPrime N) (σ.1.1 • b) :=
    Localization.localRingHom_to_map N N _ hc b
  refine ⟨s, hsmap, ?_⟩
  suffices h : (IsLocalRing.residue (Localization.AtPrime N)).comp s.toRingHom =
      IsLocalRing.residue (Localization.AtPrime N) from RingHom.congr_fun h
  apply IsLocalization.ringHom_ext N.primeCompl
  ext b
  change IsLocalRing.residue (Localization.AtPrime N)
      (s (algebraMap B (Localization.AtPrime N) b)) = algebraMap B N.ResidueField b
  rw [hsmap]
  change algebraMap B N.ResidueField (σ.1.1 • b) = algebraMap B N.ResidueField b
  rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
  exact σ.property b

set_option maxHeartbeats 600000 in
-- Comparing the localized field embeddings requires dependent instance synthesis.
/-- Comparing local uniformizers gives multiplicativity of ramification indices and
compatibility of the raw inertia characters. No surjectivity of the inertia map is required.

Source: Stacks Project, More on Algebra, Tag 0BU7, final paragraph.
(blueprint: lem-exc-finite-tame-character-tower)

Proof: The inclusion of the two integral closures localizes to a local injective map
C_L -> C_M, commuting with the specified embeddings into L and M. A base uniformizer
is nonzero and nonunit in C_L, so eL is positive. Choose uniformizers tL and tM. In C_M
write tL = u*tM^r with u a unit. A base uniformizer is a unit times tL^eL, and taking
C_M-valuations gives eM = r*eL. An upper inertia automorphism extends to C_M and fixes
its residue field. Applying it to tL = u*tM^r and dividing gives
sigma(tL)/tL = sigma(u)/u * (sigma(tM)/tM)^r. The first factor has residue one.
The two character formulas identify the remaining residues, and their comparison uses
exactly the localized inclusion's canonical residue-field map. -/
private theorem finite_normalization_character_comparison
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (𝔫M : Ideal (integralClosure A M)) [𝔫M.IsMaximal]
    (𝔫L : Ideal (integralClosure A L)) [𝔫L.IsMaximal]
    (hcomp : 𝔫L = Ideal.comap
      (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M)
    (hCL : IsDiscreteValuationRing (Localization.AtPrime 𝔫L))
      (hCM : IsDiscreteValuationRing (Localization.AtPrime 𝔫M))
      (jL : Localization.AtPrime 𝔫L →+* L) (jM : Localization.AtPrime 𝔫M →+* M)
    (hjL : ∀ b : integralClosure A L,
        jL (algebraMap (integralClosure A L) (Localization.AtPrime 𝔫L) b) = (b : L))
    (hjM : ∀ b : integralClosure A M,
        jM (algebraMap (integralClosure A M) (Localization.AtPrime 𝔫M) b) = (b : M))
    (eL eM : ℕ)
    (heL : ∀ πA : A, Irreducible πA →
        @addVal (Localization.AtPrime 𝔫L) _ _ hCL
          (algebraMap A (Localization.AtPrime 𝔫L) πA) = (eL : ℕ∞))
    (heM : ∀ πA : A, Irreducible πA →
        @addVal (Localization.AtPrime 𝔫M) _ _ hCM
          (algebraMap A (Localization.AtPrime 𝔫M) πA) = (eM : ℕ∞))
    (χL : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L) →*
        rootsOfUnity eL 𝔫L.ResidueField)
      (χM : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        rootsOfUnity eM 𝔫M.ResidueField)
    (hχL : ∀ t : Localization.AtPrime 𝔫L, Irreducible t →
        ∀ σ : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L),
          ∃ a : (Localization.AtPrime 𝔫L)ˣ,
            jL (a : Localization.AtPrime 𝔫L) = σ.1.1 (jL t) / jL t ∧
            ((χL σ : 𝔫L.ResidueFieldˣ) : 𝔫L.ResidueField) =
              IsLocalRing.residue (Localization.AtPrime 𝔫L) a)
    (hχM : ∀ t : Localization.AtPrime 𝔫M, Irreducible t →
        ∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
          ∃ a : (Localization.AtPrime 𝔫M)ˣ,
            jM (a : Localization.AtPrime 𝔫M) = σ.1.1 (jM t) / jM t ∧
            ((χM σ : 𝔫M.ResidueFieldˣ) : 𝔫M.ResidueField) =
              IsLocalRing.residue (Localization.AtPrime 𝔫M) a)
    (rI : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
      𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L))
    (hrI : ∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
      (rI σ).1.1 = AlgEquiv.restrictNormalHom L σ.1.1) :
    0 < eL ∧ ∃ r : ℕ, 0 < r ∧ eM = r * eL ∧
      ∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        Units.map (Ideal.ResidueField.map 𝔫L 𝔫M
            (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom hcomp).toMonoidHom
            (χL (rI σ) : 𝔫L.ResidueFieldˣ) = (χM σ : 𝔫M.ResidueFieldˣ) ^ r := by
  classical
  let f := (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom
  let g := Localization.localRingHom 𝔫L 𝔫M f hcomp
  have jLinj : Function.Injective jL :=
    local_embedding_injective 𝔫L jL hjL Subtype.val_injective
  have jMinj : Function.Injective jM :=
    local_embedding_injective 𝔫M jM hjM Subtype.val_injective
  have hcomm : jM.comp g = (algebraMap L M).comp jL := by
    apply IsLocalization.ringHom_ext 𝔫L.primeCompl
    ext b
    change jM (g (algebraMap _ _ b)) = algebraMap L M (jL (algebraMap _ _ b))
    rw [Localization.localRingHom_to_map, hjM, hjL]
    rfl
  have hcomm' (x) : jM (g x) = algebraMap L M (jL x) :=
    RingHom.congr_fun hcomm x
  have ginj : Function.Injective g := by
    intro x y h
    apply jLinj
    apply (algebraMap L M).injective
    simpa only [RingHom.comp_apply] using
      (RingHom.congr_fun hcomm x).symm.trans ((congrArg jM h).trans
        (RingHom.congr_fun hcomm y))
  have glocal : IsLocalHom g := Localization.isLocalHom_localRingHom 𝔫L 𝔫M f hcomp
  obtain ⟨tL, htL⟩ := exists_irreducible (Localization.AtPrime 𝔫L)
  obtain ⟨tM, htM⟩ := exists_irreducible (Localization.AtPrime 𝔫M)
  obtain ⟨r, u, hu⟩ := eq_unit_mul_pow_irreducible
    (show g tL ≠ 0 from fun h ↦ htL.ne_zero (ginj (h.trans (map_zero g).symm))) htM
  have hrpos : 0 < r := by
    by_contra h
    have hr : r = 0 := Nat.eq_zero_of_not_pos h
    have hunit : IsUnit (g tL) := by simp [hu, hr]
    exact htL.not_isUnit (IsLocalHom.map_nonunit tL hunit)
  obtain ⟨π, hπ⟩ := exists_irreducible A
  have hπL : algebraMap A (Localization.AtPrime 𝔫L) π ≠ 0 := by
    intro h
    have h' := congrArg jL h
    rw [IsScalarTower.algebraMap_apply A (integralClosure A L)
      (Localization.AtPrime 𝔫L), hjL, map_zero] at h'
    have hAL : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    exact hπ.ne_zero (hAL (by simpa only [Subalgebra.coe_algebraMap, map_zero] using h'))
  obtain ⟨e, v, hv⟩ := eq_unit_mul_pow_irreducible hπL htL
  have he : eL = e := by
    have h := heL π hπ
    rw [hv, addVal_def' v htL] at h
    exact ENat.natCast_inj.mp h.symm
  subst e
  have heLpos : 0 < eL := by
    by_contra h
    have he0 : eL = 0 := Nat.eq_zero_of_not_pos h
    have hmem : algebraMap A (integralClosure A L) π ∈ 𝔫L := by
      have hmax : 𝔫L.comap (algebraMap A (integralClosure A L)) =
          IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫L)
      change π ∈ 𝔫L.comap (algebraMap A (integralClosure A L))
      rw [hmax]
      exact hπ.not_isUnit
    have hnonunit : ¬ IsUnit (algebraMap A (Localization.AtPrime 𝔫L) π) := by
      rw [IsScalarTower.algebraMap_apply A (integralClosure A L)
        (Localization.AtPrime 𝔫L)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔫L _).mpr hmem
    apply hnonunit
    simp [hv, he0]
  have hgπ : g (algebraMap A (Localization.AtPrime 𝔫L) π) =
      algebraMap A (Localization.AtPrime 𝔫M) π := by
    rw [IsScalarTower.algebraMap_apply A (integralClosure A L)
      (Localization.AtPrime 𝔫L), Localization.localRingHom_to_map]
    change algebraMap (integralClosure A M) (Localization.AtPrime 𝔫M)
      ((IsScalarTower.toAlgHom A L M).mapIntegralClosure
        (algebraMap A (integralClosure A L) π)) = _
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hgunit : addVal (Localization.AtPrime 𝔫M) (g (v : Localization.AtPrime 𝔫L)) = 0 :=
    addVal_eq_zero_of_unit (Units.map g.toMonoidHom v)
  have heML : eM = r * eL := by
    have h := congrArg (addVal (Localization.AtPrime 𝔫M)) (congrArg g hv)
    rw [hgπ, heM π hπ, map_mul, map_pow, addVal_mul,
      hgunit, hu, addVal_pow,
      addVal_def' u htM, zero_add, nsmul_eq_mul, ← Nat.cast_mul] at h
    exact ENat.natCast_inj.mp h |>.trans (Nat.mul_comm _ _)
  refine ⟨heLpos, r, hrpos, heML, ?_⟩
  intro σ
  obtain ⟨s, hs, hsres⟩ := local_inertia_action 𝔫M σ
  have hjs : jM.comp s.toRingHom = σ.1.1.toRingHom.comp jM := by
    apply IsLocalization.ringHom_ext 𝔫M.primeCompl
    ext b
    change jM (s (algebraMap _ _ b)) = σ.1.1 (jM (algebraMap _ _ b))
    rw [hs, hjM, hjM]
    rfl
  have hjs' (x) : jM (s x) = σ.1.1 (jM x) := RingHom.congr_fun hjs x
  obtain ⟨aL, haL, hresL⟩ := hχL tL htL (rI σ)
  obtain ⟨aM, haM, hresM⟩ := hχM tM htM σ
  have hsM : s tM = (aM : Localization.AtPrime 𝔫M) * tM := by
    apply jMinj
    rw [map_mul, haM, hjs']
    exact (div_mul_cancel₀ _ (by simpa only [map_zero] using jMinj.ne htM.ne_zero)).symm
  have hsL : s (g tL) = g (aL : Localization.AtPrime 𝔫L) * g tL := by
    apply jMinj
    rw [map_mul, hjs', hcomm',
      hcomm', haL, hrI,
      map_div₀]
    have hrestrict : algebraMap L M ((AlgEquiv.restrictNormalHom L σ.1.1) (jL tL)) =
        σ.1.1 (algebraMap L M (jL tL)) :=
      AlgEquiv.restrictNormal_commutes σ.1.1 L (jL tL)
    rw [hrestrict]
    exact (div_mul_cancel₀ _ (by simpa only [map_zero] using
      (algebraMap L M).injective.ne (jLinj.ne htL.ne_zero))).symm
  have hcancel : g (aL : Localization.AtPrime 𝔫L) * (u : Localization.AtPrime 𝔫M) =
      s u * (aM : Localization.AtPrime 𝔫M) ^ r := by
    apply mul_right_cancel₀ (pow_ne_zero r htM.ne_zero)
    calc
      _ = g (aL : Localization.AtPrime 𝔫L) * g tL := by rw [hu]; ring
      _ = s (g tL) := hsL.symm
      _ = _ := by rw [hu, map_mul, map_pow, hsM, mul_pow]; ring
  apply Units.ext
  change (Ideal.ResidueField.map 𝔫L 𝔫M f hcomp)
    ((χL (rI σ) : 𝔫L.ResidueFieldˣ) : 𝔫L.ResidueField) =
      ((χM σ : 𝔫M.ResidueFieldˣ) : 𝔫M.ResidueField) ^ r
  rw [hresL, IsLocalRing.ResidueField.map_residue, hresM]
  have hred := congrArg (IsLocalRing.residue (Localization.AtPrime 𝔫M)) hcancel
  rw [map_mul, map_mul, map_pow, hsres] at hred
  exact mul_left_cancel₀ ((IsLocalRing.residue (Localization.AtPrime 𝔫M)).isUnit_map
    u.isUnit).ne_zero ((mul_comm _ _).trans hred)

private theorem wild_kernel_lift
    {G : Type u} {H : Type v} {C : Type w} [Group G] [Group H] [Group C]
    (f : G →* H) (χ : G →* C) (P : Subgroup H)
    (n : ℕ) (hf : Function.Surjective f)
    (hχ : ∀ x, χ x ^ n = 1) (hP : ∀ x, χ x = 1 → f x ∈ P)
    (hcop : Nat.Coprime (Nat.card P) n) :
    ∃ r : χ.ker →* P, Function.Surjective r ∧ ∀ x, (r x : H) = f x := by
  let r : χ.ker →* P := (f.comp χ.ker.subtype).codRestrict P fun x => hP x x.property
  refine ⟨r, ?_, fun _ => rfl⟩
  intro y
  obtain ⟨z, hz⟩ := hcop.pow_left_bijective.surjective y
  obtain ⟨x, hx⟩ := hf z
  have hxn : x ^ n ∈ χ.ker := by
    change χ (x ^ n) = 1
    rw [map_pow, hχ]
  refine ⟨⟨x ^ n, hxn⟩, ?_⟩
  apply Subtype.ext
  change f (x ^ n) = (y : H)
  rw [map_pow, hx]
  exact congrArg (fun a : P => (a : H)) hz

private theorem rescale_character
    {G : Type u} [Group G] {k : Type v} [Field k]
    (e n q : ℕ) (χ : G →* rootsOfUnity e k)
    (heq : rootsOfUnity e k = rootsOfUnity n k)
    (hcard : Nat.card (rootsOfUnity n k) = n)
    (hcop : Nat.Coprime n q)
    (hsurj : Function.Surjective χ) :
    ∃ ψ : G →* rootsOfUnity n k,
      (∀ x, (ψ x : kˣ) = (χ x : kˣ) ^ q) ∧
      Function.Surjective ψ ∧ ψ.ker = χ.ker := by
  let χ₀ : G →* rootsOfUnity n k :=
    ((rootsOfUnity e k).subtype.comp χ).codRestrict _ fun x ↦ heq ▸ (χ x).property
  have hχ₀ : Function.Surjective χ₀ := by
    intro y
    obtain ⟨x, hx⟩ := hsurj ⟨y, heq.symm ▸ y.property⟩
    exact ⟨x, Subtype.ext (congrArg (fun z : rootsOfUnity e k ↦ (z : kˣ)) hx)⟩
  have hbij : Function.Bijective (fun z : rootsOfUnity n k ↦ z ^ q) := by
    exact (show Nat.Coprime (Nat.card (rootsOfUnity n k)) q by
      rw [hcard]; exact hcop).pow_left_bijective
  let ψ := (powMonoidHom q : rootsOfUnity n k →* rootsOfUnity n k).comp χ₀
  refine ⟨ψ, fun _ ↦ rfl, hbij.surjective.comp hχ₀, ?_⟩
  ext x
  change χ₀ x ^ q = 1 ↔ χ x = 1
  rw [← one_pow q, hbij.injective.eq_iff]
  constructor
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity n k ↦ (z : kˣ)) h
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity e k ↦ (z : kˣ)) h


private theorem character_surjective_of_quotient
    {G : Type*} [Group G] {k : Type*} [Field k] {e n : ℕ}
    (χ : G →* rootsOfUnity e k)
    (heq : rootsOfUnity e k = rootsOfUnity n k)
    (θ : (G ⧸ χ.ker) ≃* rootsOfUnity n k)
    (hθ : ∀ x, (θ (QuotientGroup.mk x) : kˣ) = (χ x : kˣ)) :
    Function.Surjective χ := by
  intro z
  let zn : rootsOfUnity n k := ⟨z, heq ▸ z.property⟩
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (θ.symm zn)
  refine ⟨x, Subtype.ext ?_⟩
  rw [← hθ, hx, θ.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
-- The tower combines two large dependent normalization records.
/-- Restriction in a finite Galois tower is surjective on decomposition, inertia and wild
inertia groups. The canonical tame characters have the wild kernels and commute with the
power map whose exponent is the ratio of the prime-to-residue-characteristic indices.

The first clause establishes maximality of the contracted ideal. The remaining clauses
use any maximal ideal equal to that contraction. The local embeddings `jL`, `jM` extend the
inclusions of the integral closures. As in `finite_normalization_tame_inertia`, the raw
characters are characterized by the residue of `σ(t)/t` for every local uniformizer, and
the indices are the normalized additive valuations of every base uniformizer. Thus the
existential characters and embeddings are fixed by their defining formulas.

Source: Stacks Project, More on Algebra, Tags 0BU7 and 0BU8.
(blueprint: lem-exc-finite-tame-character-tower)

Proof:
1. The integral closure in M is integral over the integral closure in L
   (`def-weil-pbc-integral-closure`). A monic equation for the inverse of a nonzero
   element shows that a field integral over a subdomain forces that subdomain to be a field.
   Apply this to the quotient by the contracted maximal ideal; it is maximal.
2. Apply `lem-exc-finite-dvr-tame-inertia` to L/K and M/K. This supplies the local DVRs,
   the embeddings extending the inclusions, normalized indices, uniformizer characters,
   finite p-group wild kernels, and cyclic tame quotients of order the prime-to-p indices.
3. The extension M/L is finite Galois. A Gal(M/L)-fixed element of the upper
   normalization lies in L by `lem-weil-pbc-finite-galois-fixed-field`; integrality
   descends through the field embedding, so it belongs to the lower normalization.
   This supplies the invariant-ring hypothesis for prime conjugacy and residue lifting.
4. Lift an element of the lower decomposition group by
   `lem-weil-pbc-normal-subextension-automorphism-extends`. The image of the upper prime
   and the chosen upper prime lie over the same lower prime. Apply prime conjugacy in
   `lem-exc-finite-galois-prime-residue-lifting` over the lower normalization and correct
   the lift by an automorphism over L. This proves decomposition surjectivity.
5. For a lower inertia element, the residue action of such a lift fixes the lower residue
   field. The residue-lifting clause of the same prime-residue lemma supplies an
   automorphism over L with that residue action. Correct the lift by its inverse to
   obtain upper inertia. Contraction and residue-field injection show that restriction
   maps the decomposition and inertia groups into the lower groups.
6. The local inclusion sends a lower uniformizer to u times the r-th power of an upper
   uniformizer, with u a unit and r positive. Apply the normalized valuations of
   `def-sc-discrete-valuation-ring` to get eM = r eL, hence nL divides nM.
7. Applying upper inertia to that uniformizer equation and reducing cancels σ(u)/u.
   The uniformizer formula of `lem-exc-finite-dvr-tame-inertia` therefore gives the raw
   character relation χL(σ|L) = χM(σ)^r. In particular wild inertia maps into wild inertia.
8. Lift a lower wild element γ to upper inertia τ. Since χM(τ)^nM = 1, τ^nM is wild.
   The order of γ divides a p-power by `lem-exc-finite-dvr-tame-inertia`; choose h with
   h nM congruent to 1 modulo that p-power. Then τ^(h nM) is a wild lift of γ.
9. Raise the raw identity to qL and use r qL = qM (nM/nL). This is the asserted scaled
   character identity under the canonical residue-field embedding.
10. Raising to qX is an automorphism of the nX-th roots of unity, since qX is a p-power
    and nX is prime to p (use a Bezout inverse). The surjectivity and kernels from
    `lem-exc-finite-dvr-tame-inertia` are preserved. Thus the identity describes the
    induced transition on the tame quotients, and that transition is surjective. -/
theorem finite_tame_character_tower
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (𝔫M : Ideal (integralClosure A M)) [𝔫M.IsMaximal] :
    (Ideal.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M).IsMaximal ∧
    ∀ (𝔫L : Ideal (integralClosure A L)) [𝔫L.IsMaximal]
      (hcomp : 𝔫L = Ideal.comap
        (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M),
    ∃ (hCL : IsDiscreteValuationRing (Localization.AtPrime 𝔫L))
      (hCM : IsDiscreteValuationRing (Localization.AtPrime 𝔫M))
      (jL : Localization.AtPrime 𝔫L →+* L) (jM : Localization.AtPrime 𝔫M →+* M),
      (∀ b : integralClosure A L,
        jL (algebraMap (integralClosure A L) (Localization.AtPrime 𝔫L) b) = (b : L)) ∧
      (∀ b : integralClosure A M,
        jM (algebraMap (integralClosure A M) (Localization.AtPrime 𝔫M) b) = (b : M)) ∧
    ∃ (eL eM : ℕ),
      (∀ πA : A, Irreducible πA →
        @addVal (Localization.AtPrime 𝔫L) _ _ hCL
          (algebraMap A (Localization.AtPrime 𝔫L) πA) = (eL : ℕ∞)) ∧
      (∀ πA : A, Irreducible πA →
        @addVal (Localization.AtPrime 𝔫M) _ _ hCM
          (algebraMap A (Localization.AtPrime 𝔫M) πA) = (eM : ℕ∞)) ∧
    ∃ (χL : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L) →*
        rootsOfUnity eL 𝔫L.ResidueField)
      (χM : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        rootsOfUnity eM 𝔫M.ResidueField),
      (∀ t : Localization.AtPrime 𝔫L, Irreducible t →
        ∀ σ : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L),
          ∃ a : (Localization.AtPrime 𝔫L)ˣ,
            jL (a : Localization.AtPrime 𝔫L) = σ.1.1 (jL t) / jL t ∧
            ((χL σ : 𝔫L.ResidueFieldˣ) : 𝔫L.ResidueField) =
              IsLocalRing.residue (Localization.AtPrime 𝔫L) a) ∧
      (∀ t : Localization.AtPrime 𝔫M, Irreducible t →
        ∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
          ∃ a : (Localization.AtPrime 𝔫M)ˣ,
            jM (a : Localization.AtPrime 𝔫M) = σ.1.1 (jM t) / jM t ∧
            ((χM σ : 𝔫M.ResidueFieldˣ) : 𝔫M.ResidueField) =
              IsLocalRing.residue (Localization.AtPrime 𝔫M) a) ∧
    ∃ (qL nL qM nM : ℕ),
      (∃ aL : ℕ, qL = p ^ aL) ∧ (∃ aM : ℕ, qM = p ^ aM) ∧
      Nat.Coprime nL p ∧ Nat.Coprime nM p ∧
      eL = qL * nL ∧ eM = qM * nM ∧ nL ∣ nM ∧
    ∃ (rD : MulAction.stabilizer Gal(M/K) 𝔫M →* MulAction.stabilizer Gal(L/K) 𝔫L),
      Function.Surjective rD ∧
      (∀ σ : MulAction.stabilizer Gal(M/K) 𝔫M,
        (rD σ).1 = AlgEquiv.restrictNormalHom L σ.1) ∧
    ∃ (rI : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L)),
      Function.Surjective rI ∧
      (∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        (rI σ).1.1 = AlgEquiv.restrictNormalHom L σ.1.1) ∧
    ∃ (rP : χM.ker →* χL.ker),
      Function.Surjective rP ∧ (∀ σ : χM.ker, (rP σ).1 = rI σ.1) ∧
    ∃ (χLcan : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L) →*
        rootsOfUnity nL 𝔫L.ResidueField)
      (χMcan : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        rootsOfUnity nM 𝔫M.ResidueField),
      (∀ σ : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L),
        (χLcan σ : 𝔫L.ResidueFieldˣ) = (χL σ : 𝔫L.ResidueFieldˣ) ^ qL) ∧
      (∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        (χMcan σ : 𝔫M.ResidueFieldˣ) = (χM σ : 𝔫M.ResidueFieldˣ) ^ qM) ∧
      Function.Surjective χLcan ∧ Function.Surjective χMcan ∧
      χLcan.ker = χL.ker ∧ χMcan.ker = χM.ker ∧
      ∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        Units.map (Ideal.ResidueField.map 𝔫L 𝔫M
            (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom hcomp).toMonoidHom
            (χLcan (rI σ) : 𝔫L.ResidueFieldˣ) =
          (χMcan σ : 𝔫M.ResidueFieldˣ) ^ (nM / nL) := by
  classical
  let f := (IsScalarTower.toAlgHom A L M).mapIntegralClosure
  have hf : f.toRingHom.IsIntegral := by
    apply RingHom.IsIntegral.tower_top (algebraMap A (integralClosure A L))
    rw [AlgHom.toRingHom_eq_coe, f.comp_algebraMap]
    exact fun b => integralClosure.isIntegral b
  constructor
  · exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f.toRingHom hf 𝔫M
  · intro 𝔫L _ hcomp
    obtain ⟨hCL, jL, hjL, hjLfrac, ρL, hρL, hρLfin, eL, heL, χL, hχL,
      hPLnormal, hPLfinite, hPLcard, hrootsL, hcyclicL, hcardL, θL, hθL⟩ :=
      (finite_normalization_tame_inertia A K L p).2 𝔫L
    obtain ⟨hCM, jM, hjM, hjMfrac, ρM, hρM, hρMfin, eM, heM, χM, hχM,
      hPMnormal, hPMfinite, hPMcard, hrootsM, hcyclicM, hcardM, θM, hθM⟩ :=
      (finite_normalization_tame_inertia A K M p).2 𝔫M
    obtain ⟨rD, hrDsurj, hrD, rI, hrIsurj, hrI⟩ :=
      finite_normalization_restriction_surjective A K L M 𝔫M 𝔫L hcomp
    obtain ⟨heLpos, r, hrpos, heML, hraw⟩ :=
      finite_normalization_character_comparison A K L M 𝔫M 𝔫L hcomp
        hCL hCM jL jM hjL hjM eL eM heL heM χL χM hχL hχM rI hrI
    have heMpos : 0 < eM := heML ▸ Nat.mul_pos hrpos heLpos
    let qL := p ^ eL.factorization p
    let qM := p ^ eM.factorization p
    let nL := eL / qL
    let nM := eM / qM
    have hcopL : Nat.Coprime nL p :=
      (Nat.coprime_ordCompl (Fact.out : p.Prime) heLpos.ne').symm
    have hcopM : Nat.Coprime nM p :=
      (Nat.coprime_ordCompl (Fact.out : p.Prime) heMpos.ne').symm
    have heLsplit : eL = qL * nL := (Nat.ordProj_mul_ordCompl_eq_self eL p).symm
    have heMsplit : eM = qM * nM := (Nat.ordProj_mul_ordCompl_eq_self eM p).symm
    have hnLpos : 0 < nL := Nat.ordCompl_pos p heLpos.ne'
    have hdvd : nL ∣ nM :=
      Nat.ordCompl_dvd_ordCompl_of_dvd ⟨r, by rw [heML, mul_comm]⟩ p
    have hexponent : r * qL = qM * (nM / nL) := by
      apply Nat.eq_of_mul_eq_mul_right hnLpos
      calc
        r * qL * nL = r * eL := by rw [heLsplit]; ac_rfl
        _ = eM := heML.symm
        _ = qM * (nM / nL) * nL := by
          rw [mul_assoc, Nat.div_mul_cancel hdvd, ← heMsplit]
    have hχLsurj : Function.Surjective χL :=
      character_surjective_of_quotient χL hrootsL θL hθL
    have hχMsurj : Function.Surjective χM :=
      character_surjective_of_quotient χM hrootsM θM hθM
    obtain ⟨χLcan, hχLcan, hχLcanSurj, hχLcanKer⟩ :=
      rescale_character (k := 𝔫L.ResidueField) eL nL qL χL hrootsL hcardL
        (hcopL.pow_right _) hχLsurj
    obtain ⟨χMcan, hχMcan, hχMcanSurj, hχMcanKer⟩ :=
      rescale_character (k := 𝔫M.ResidueField) eM nM qM χM hrootsM hcardM
        (hcopM.pow_right _) hχMsurj
    have hwildMap : ∀ x, χM x = 1 → rI x ∈ χL.ker := by
      intro x hx
      change χL (rI x) = 1
      apply Subtype.ext
      apply Units.map_injective
        (Ideal.ResidueField.map 𝔫L 𝔫M f.toRingHom hcomp).injective
      simpa only [hx, OneMemClass.coe_one, one_pow, map_one] using hraw x
    have hwildPow : ∀ x, χM x ^ nM = 1 := by
      intro x
      apply Subtype.ext
      exact (mem_rootsOfUnity nM _).mp (hrootsM ▸ (χM x).property)
    have hwildCoprime : Nat.Coprime (Nat.card χL.ker) nM := by
      obtain ⟨a, ha⟩ := hPLcard
      rw [ha]
      exact hcopM.symm.pow_left a
    obtain ⟨rP, hrPsurj, hrP⟩ :=
      wild_kernel_lift rI χM χL.ker nM hrIsurj hwildPow hwildMap hwildCoprime
    refine ⟨hCL, hCM, jL, jM, hjL, hjM, eL, eM, heL, heM, χL, χM,
      hχL, hχM, qL, nL, qM, nM, ⟨_, rfl⟩, ⟨_, rfl⟩, hcopL, hcopM,
      heLsplit, heMsplit, hdvd, rD, hrDsurj, hrD, rI, hrIsurj, hrI,
      rP, hrPsurj, hrP, χLcan, χMcan, hχLcan, hχMcan,
      hχLcanSurj, hχMcanSurj, hχLcanKer, hχMcanKer, ?_⟩
    intro σ
    rw [hχLcan, map_pow, hraw, ← pow_mul, hexponent, pow_mul, hχMcan]


end IsDiscreteValuationRing
