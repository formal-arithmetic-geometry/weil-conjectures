/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Smooth.Local
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular local algebras with rational residue field are smooth

Let `k` be a field. We show that a local `k`-algebra which is a regular quotient of a regular
local ring `P`, formally smooth over `k` with `Ω[P⁄k]` finite free, and whose residue field is `k`,
is formally smooth over `k`. This uses the Jacobian criterion
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`: at a rational
point the differential identifies `𝔪 / 𝔪²` with `κ ⊗ Ω[P⁄k]`
(`IsLocalRing.cotangentDerivation`), and the kernel `I` of `P → S` satisfies `I ∩ 𝔪² ⊆ 𝔪 I`
since `S` is regular (`IsRegularLocalRing.inf_sq_le_mul`).

## Main results

- `Algebra.FormallySmooth.of_isRegularLocalRing`: a regular local quotient with rational residue
  field of a regular local `k`-algebra `P` (formally smooth with `Ω[P⁄k]` finite free) is formally
  smooth over `k`.
- `Algebra.IsSmoothAt.of_isRegularLocalRing`: a finitely generated `k`-algebra is smooth at a
  prime with residue field `k` at which it is regular.
- `Algebra.IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed`: over an algebraically closed field,
  a finitely generated algebra is smooth at every maximal ideal at which it is regular.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

/-- If `K` is a quotient of the ring `P` and `1 ⊗ v = 0` in `K ⊗[P] N`, then `v` lies in
`I • N`, where `I` is the kernel of `P → K`. -/
lemma TensorProduct.mem_ker_smul_top_of_one_tmul_eq_zero {P K N : Type*} [CommRing P] [CommRing K]
    [Algebra P K] [AddCommGroup N] [Module P N] (hK : Function.Surjective (algebraMap P K))
    {v : N} (h : (1 : K) ⊗ₜ[P] v = 0) :
    v ∈ (RingHom.ker (algebraMap P K)) • (⊤ : Submodule P N) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P K) hK
  have h' := congrArg (e.symm.toLinearMap.rTensor N) h
  rw [LinearMap.rTensor_tmul, map_zero, AlgEquiv.toLinearMap_apply, map_one] at h'
  have h'' := congrArg (quotTensorEquivQuotSMul N (RingHom.ker (Algebra.ofId P K))) h'
  rw [quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h''
  exact h''

namespace IsLocalRing

variable {k P : Type u} [Field k] [CommRing P] [IsLocalRing P] [Algebra k P]

/-- At a rational point, the map `a ↦ a - a(x)` to the cotangent space `𝔪 / 𝔪²` is a
`k`-derivation. Here `a(x) ∈ k` is the residue of `a`, which lies in `k` since the residue field
of `P` is `k`. -/
noncomputable def cotangentDerivation
    (hk : Function.Surjective (algebraMap k (ResidueField P))) :
    Derivation k P (CotangentSpace P) := by
  let e : k ≃+* ResidueField P :=
    RingEquiv.ofBijective (algebraMap k (ResidueField P)) ⟨(algebraMap k _).injective, hk⟩
  let c : P →+* P := (algebraMap k P).comp (e.symm.toRingHom.comp (residue P))
  have hc (a : P) : a - c a ∈ maximalIdeal P := by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    change _ = residue P (algebraMap k P _)
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact (e.apply_symm_apply _).symm
  have hcalg (t : k) : c (algebraMap k P t) = algebraMap k P t := by
    change algebraMap k P (e.symm (residue P (algebraMap k P t))) = _
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      show algebraMap k (ResidueField P) t = e t from rfl, e.symm_apply_apply]
  refine Derivation.mk'
    { toFun a := (maximalIdeal P).toCotangent ⟨a - c a, hc a⟩
      map_add' a b := by
        rw [← map_add]
        congr 1
        ext
        simp only [map_add, Submodule.coe_add]
        ring
      map_smul' t a := by
        rw [RingHom.id_apply, ← algebraMap_smul P t ((maximalIdeal P).toCotangent _),
          ← LinearMap.map_smul]
        congr 1
        ext
        simp only [Algebra.smul_def, map_mul, hcalg, SetLike.val_smul, Algebra.algebraMap_self,
          RingHom.id_apply]
        ring } fun a b ↦ ?_
  change (maximalIdeal P).toCotangent ⟨a * b - c (a * b), _⟩ =
    a • (maximalIdeal P).toCotangent ⟨b - c b, _⟩ + b • (maximalIdeal P).toCotangent ⟨a - c a, _⟩
  rw [← map_smul, ← map_smul, ← map_add]
  rw [← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
  have : a * b - c (a * b) - (a * (b - c b) + b * (a - c a)) = - ((a - c a) * (b - c b)) := by
    rw [map_mul]; ring
  simp only [Submodule.coe_sub, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
  rw [this, neg_mem_iff, pow_two]
  exact Ideal.mul_mem_mul (hc a) (hc b)

lemma cotangentDerivation_apply_of_mem
    (hk : Function.Surjective (algebraMap k (ResidueField P))) {y : P}
    (hy : y ∈ maximalIdeal P) :
    cotangentDerivation hk y = (maximalIdeal P).toCotangent ⟨y, hy⟩ := by
  change (maximalIdeal P).toCotangent ⟨_, _⟩ = _
  congr 2
  simp [(residue_eq_zero_iff y).2 hy]

/-- At a rational point of a local `k`-algebra `P`, an element `y ∈ 𝔪` whose differential vanishes
at the closed point lies in `𝔪²`. -/
theorem mem_maximalIdeal_sq_of_one_tmul_D_eq_zero
    (hk : Function.Surjective (algebraMap k (ResidueField P))) {K : Type*} [CommRing K]
    [Nontrivial K] [Algebra P K] (hK : Function.Surjective (algebraMap P K)) {y : P}
    (hy : y ∈ maximalIdeal P) (h : (1 : K) ⊗ₜ[P] KaehlerDifferential.D k P y = 0) :
    y ∈ maximalIdeal P ^ 2 := by
  have h' := congrArg ((cotangentDerivation hk).liftKaehlerDifferential.lTensor K) h
  rw [LinearMap.lTensor_tmul, map_zero, Derivation.liftKaehlerDifferential_comp_D,
    cotangentDerivation_apply_of_mem hk hy] at h'
  have h'' := TensorProduct.mem_ker_smul_top_of_one_tmul_eq_zero hK h'
  have hle : RingHom.ker (algebraMap P K) ≤ maximalIdeal P :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  have h3 := Submodule.smul_mono_left (N := (⊤ : Submodule P (CotangentSpace P))) hle h''
  refine (Ideal.toCotangent_eq_zero _ ⟨y, hy⟩).1 ?_
  refine Submodule.smul_induction_on h3 (fun a ha w _ ↦ ?_) (fun a b ha hb ↦ by rw [ha, hb,
    add_zero])
  obtain ⟨z, rfl⟩ := (maximalIdeal P).toCotangent_surjective w
  rw [← map_smul, Ideal.toCotangent_eq_zero, pow_two]
  exact Ideal.mul_mem_mul ha z.2

end IsLocalRing

namespace Algebra

/-- **Regular local rings with rational residue field are formally smooth.** Let `P` be a
regular local `k`-algebra, formally smooth over `k` with `Ω[P⁄k]` finite free, and let `S` be a
regular local quotient of `P` whose residue field is `k`. Then `S` is formally smooth over `k`. By
the Jacobian criterion it suffices that `κ ⊗ I → κ ⊗ Ω[P⁄k]` is injective, where `I` is the kernel
of `P → S`: an element of `I` with vanishing differential at the closed point lies in `𝔪²`, hence
in `𝔪 I` since `S` is regular. -/
theorem FormallySmooth.of_isRegularLocalRing {k P S : Type u} [Field k] [CommRing P]
    [CommRing S] [Algebra k P] [Algebra k S] [Algebra P S] [IsScalarTower k P S]
    [IsRegularLocalRing P] [IsRegularLocalRing S] [FormallySmooth k P] [Module.Free P Ω[P⁄k]]
    [Module.Finite P Ω[P⁄k]] (hPS : Function.Surjective (algebraMap P S))
    (hk : Function.Surjective (algebraMap k (ResidueField S))) : FormallySmooth k S := by
  set I := RingHom.ker (algebraMap P S)
  rw [FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P hPS
    (IsNoetherian.noetherian I)]
  have : IsRegularLocalRing (P ⧸ I) :=
    .of_ringEquiv (RingHom.quotientKerEquivOfSurjective hPS).symm
  have : IsLocalHom (algebraMap P S) := .of_surjective _ hPS
  set K := ResidueField S
  have hPK : Function.Surjective (algebraMap P K) := by
    rw [IsScalarTower.algebraMap_eq P S K]
    exact Ideal.Quotient.mk_surjective.comp hPS
  have hkP : Function.Surjective (algebraMap k (ResidueField P)) := by
    intro a
    obtain ⟨p, rfl⟩ := residue_surjective a
    obtain ⟨t, ht⟩ := hk (residue S (algebraMap P S p))
    refine ⟨t, ?_⟩
    have e1 : residue S (algebraMap k S t) = algebraMap k (ResidueField S) t := by
      rw [IsScalarTower.algebraMap_apply k S (ResidueField S), ResidueField.algebraMap_eq]
    have hS : algebraMap P S (p - algebraMap k P t) ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff, map_sub, map_sub, ← IsScalarTower.algebraMap_apply k P S, e1,
        ht, sub_self]
    have hP : p - algebraMap k P t ∈ maximalIdeal P :=
      (mem_maximalIdeal _).2 fun hu ↦ (mem_maximalIdeal _).1 hS (hu.map _)
    rw [← sub_eq_zero, IsScalarTower.algebraMap_apply k P (ResidueField P),
      ResidueField.algebraMap_eq, ← map_sub, residue_eq_zero_iff, ← neg_sub, neg_mem_iff]
    exact hP
  have hIm : I ≤ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top _)
  have hker : ∀ a ∈ maximalIdeal P, algebraMap P K a = 0 := fun a ha ↦ by
    rw [IsScalarTower.algebraMap_apply P S K, ResidueField.algebraMap_eq, residue_eq_zero_iff]
    exact map_nonunit _ a ha
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨f, rfl⟩ := TensorProduct.mk_surjective P I K hPK z
  rw [TensorProduct.mk_apply, KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul,
    KaehlerDifferential.kerToTensor_apply] at hz
  have h2 := mem_maximalIdeal_sq_of_one_tmul_D_eq_zero hkP hPK (hIm f.2) hz
  have h3 := IsRegularLocalRing.inf_sq_le_mul I ⟨f.2, h2⟩
  rw [← Ideal.smul_eq_mul, ← Submodule.mem_smul_top_iff] at h3
  rw [TensorProduct.mk_apply]
  refine Submodule.smul_induction_on h3 (fun a ha w _ ↦ ?_) (fun a b ha hb ↦ ?_)
  · rw [tmul_smul, smul_tmul', Algebra.smul_def, mul_one, hker a ha, zero_tmul]
  · rw [tmul_add, ha, hb, add_zero]

/-- **A finitely generated algebra over a field is smooth at a regular rational point.** Let `A`
be a finitely generated `k`-algebra and `q` a prime of `A` with residue field `k` such that `A_q`
is a regular local ring. Then `A` is smooth over `k` at `q`. -/
theorem IsSmoothAt.of_isRegularLocalRing {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [FiniteType k A] (q : Ideal A) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)]
    (hq : Function.Surjective (algebraMap k (ResidueField (Localization.AtPrime q)))) :
    IsSmoothAt k q := by
  obtain ⟨n, φ, hφ⟩ := FiniteType.iff_quotient_mvPolynomial''.1 ‹_›
  set Q := q.comap φ.toRingHom
  let P := Localization.AtPrime Q
  let ψ : P →+* Localization.AtPrime q := Localization.localRingHom Q q φ.toRingHom rfl
  let : Algebra P (Localization.AtPrime q) := ψ.toAlgebra
  have : IsScalarTower k P (Localization.AtPrime q) := .of_algebraMap_eq fun t ↦ by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) P,
      Localization.localRingHom_to_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsRegularLocalRing P := isRegularRing_iff.1 inferInstance Q
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    obtain ⟨a, rfl⟩ := hφ a
    obtain ⟨s', hs'⟩ := hφ s
    have hs : s' ∈ Q.primeCompl := by
      change φ s' ∉ q
      rw [hs']
      exact s.2
    refine ⟨IsLocalization.mk' P a ⟨s', hs⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial (Fin n) k) P
  have : Module.Free P Ω[P⁄k] := .of_equiv hbc.equiv
  have : Module.Finite P Ω[P⁄k] := .equiv hbc.equiv
  exact FormallySmooth.of_isRegularLocalRing (P := P) hψ hq

/-- A finitely generated algebra over an algebraically closed field `k` is smooth at every
maximal ideal at which it is regular: the residue field is a finite extension of `k`, hence
equal to `k`. -/
theorem IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed {k A : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [FiniteType k A] (q : Ideal A) [q.IsMaximal]
    [IsRegularLocalRing (Localization.AtPrime q)] : IsSmoothAt k q := by
  refine IsSmoothAt.of_isRegularLocalRing q ?_
  have : FiniteType k q.ResidueField :=
    .of_surjective (IsScalarTower.toAlgHom k A q.ResidueField)
      q.algebraMap_residueField_surjective
  have : Module.Finite k q.ResidueField := finite_of_finite_type_of_isJacobsonRing k _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2

end Algebra
