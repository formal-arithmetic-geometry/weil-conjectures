/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Local
public import WeilConjectures.RingTheory.Regular.Hartogs
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Etale.Field

/-!
# Integral closures in étale algebras over the fraction field of a normal domain

Let `O` be a Noetherian integrally closed domain with fraction field `K`, `L` an étale
`K`-algebra and `C` the integral closure of `O` in `L`. Then `C` is finite over `O`
(`RingTheory.DepthTwo.finite_integralClosure_of_etale`), and if `[a, b]` is a regular sequence
in `O` then `C` is its own Hartogs extension along `(a, b)`: an element `f ∈ L` with
`aⁿ f ∈ C` and `bᵐ f ∈ C` lies in `C` (`RingTheory.DepthTwo.hartogs_integralClosure_eq`).

Both reduce to the case of a finite separable field extension, where `C` is contained in the
`O`-span of the dual of an integral basis for the trace form; the elements of the Hartogs
extension have traces in `O_a ∩ O_b = O`.

These are steps of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open TensorProduct Polynomial

namespace RingTheory.DepthTwo

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

/-- If `[a, b]` is a regular sequence on the domain `O` with `b ≠ 0`, then an element `c` of the
fraction field with `aⁿ c ∈ O` and `bᵐ c ∈ O` lies in `O` (`O_a ∩ O_b = O`). -/
lemma mem_range_of_pow_smul_mem_range {a b : O}
    (hab : RingTheory.Sequence.IsWeaklyRegular O [a, b]) (hb : b ≠ 0) {c : K} {n m : ℕ}
    (ha : a ^ n • c ∈ (algebraMap O K).range) (hb' : b ^ m • c ∈ (algebraMap O K).range) :
    c ∈ (algebraMap O K).range := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb'
  obtain ⟨hr, hs⟩ := RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_and_mem_smul_top hab
  have hbreg : IsSMulRegular O b := fun x y h ↦ mul_left_cancel₀ hb h
  have hinj := IsFractionRing.injective O K
  have huv : b ^ m • u = a ^ n • v := hinj (by
    simp only [smul_eq_mul, map_mul, map_pow, hu, hv, Algebra.smul_def]
    ring)
  obtain ⟨z, hz, -⟩ := RingTheory.Sequence.exists_eq_smul_of_pow_smul_sub hr hbreg hs
    (N := 0) (k := n) (l := m) (m := u) (n := v) (by rw [huv, sub_self, smul_zero])
  refine ⟨z, ?_⟩
  have ha0 : algebraMap O K (a ^ n) ≠ 0 := by
    intro h0
    have : a ^ n = 0 := hinj (by rw [h0, map_zero])
    have h1 : (a ^ n) • (1 : O) = a ^ n • 0 := by rw [this, zero_smul, smul_zero]
    exact one_ne_zero ((hr.pow n) h1)
  apply mul_left_cancel₀ ha0
  rw [← map_mul, ← smul_eq_mul, ← hz, hu, Algebra.smul_def]

variable [IsIntegrallyClosed O] [IsNoetherianRing O]

section Field

/-- **Hartogs extension in a finite separable extension.** Let `F` be a finite separable
extension of `K = Frac(O)` and `[a, b]` a regular sequence in `O`. The Hartogs extension of the
integral closure `C` of `O` in `F` along `(a, b)` is contained in `C`. -/
lemma hartogs_integralClosure_le_of_field (K : Type*) [Field K] [Algebra O K]
    [IsFractionRing O K] {F : Type*} [Field F] [Algebra O F] [Algebra K F] [IsScalarTower O K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] {a b : O}
    (hab : RingTheory.Sequence.IsWeaklyRegular O [a, b]) (hb : b ≠ 0) :
    hartogs a b (integralClosure O F) ≤ integralClosure O F := by
  classical
  obtain ⟨s, bas, hbas⟩ := FiniteDimensional.exists_is_basis_integral O K F
  have hspan : Subalgebra.toSubmodule (hartogs a b (integralClosure O F)) ≤
      Submodule.span O (Set.range <| (Algebra.traceForm K F).dualBasis
        (traceForm_nondegenerate K F) bas) := by
    rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis,
      ← LinearMap.BilinForm.le_flip_dualSubmodule, Submodule.span_le]
    rintro _ ⟨i, rfl⟩ y ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    simp only [LinearMap.BilinForm.flip_apply, Algebra.traceForm_apply]
    refine Submodule.mem_one.mpr ?_
    have htr (c : O) (k : ℕ) (hk : c ^ k • y ∈ integralClosure O F) :
        c ^ k • Algebra.trace K F (y * bas i) ∈ (algebraMap O K).range := by
      have : c ^ k • Algebra.trace K F (y * bas i) = Algebra.trace K F (c ^ k • y * bas i) := by
        rw [smul_mul_assoc, ← algebraMap_smul K (c ^ k) (y * bas i), LinearMap.map_smul,
          algebraMap_smul]
      rw [this]
      exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (hk.mul (hbas i)))
    exact mem_range_of_pow_smul_mem_range hab hb (htr a n hn) (htr b m hm)
  have : IsNoetherian O (Submodule.span O (Set.range <| (Algebra.traceForm K F).dualBasis
      (traceForm_nondegenerate K F) bas)) := isNoetherian_span_of_finite O (Set.finite_range _)
  have : Module.Finite O (hartogs a b (integralClosure O F)) :=
    Module.Finite.of_injective (Submodule.inclusion hspan) (Submodule.inclusion_injective _)
  intro y hy
  exact (Algebra.IsIntegral.isIntegral (R := O) (⟨y, hy⟩ : hartogs a b (integralClosure O F))).map
    (hartogs a b (integralClosure O F)).val

end Field

omit [IsDomain O] [IsIntegrallyClosed O] [IsNoetherianRing O] in
/-- An element of a finite product of algebras is integral if all its components are. -/
lemma isIntegral_pi {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, CommRing (A i)]
    [∀ i, Algebra O (A i)] {x : ∀ i, A i} (hx : ∀ i, IsIntegral O (x i)) : IsIntegral O x := by
  have := Fintype.ofFinite ι
  choose p hp hpx using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ fun i _ ↦ hp i, ?_⟩
  rw [← Polynomial.aeval_def]
  funext j
  rw [Pi.zero_apply, ← Pi.evalAlgHom_apply O A j (aeval x _), ← Polynomial.aeval_algHom_apply,
    map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (hpx j)

variable (K) {L : Type*} [CommRing L] [Algebra O L] [Algebra K L] [IsScalarTower O K L]
  [Algebra.Etale K L]

include K in
/-- The integral closure of a Noetherian integrally closed domain `O` in an étale algebra over its
fraction field is finite over `O`. -/
theorem finite_integralClosure_of_etale : Module.Finite O (integralClosure O L) := by
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K L).1 inferInstance
  let _ (i : I) : Algebra O (Ai i) := ((algebraMap K (Ai i)).comp (algebraMap O K)).toAlgebra
  have (i : I) : IsScalarTower O K (Ai i) := .of_algebraMap_eq' rfl
  have (i : I) : Module.Finite K (Ai i) := (hAi i).1
  have (i : I) : Algebra.IsSeparable K (Ai i) := (hAi i).2
  have (i : I) : Module.Finite O (integralClosure O (Ai i)) :=
    IsIntegralClosure.finite O K (Ai i) (integralClosure O (Ai i))
  let ψ (i : I) : L →ₐ[O] Ai i := (Pi.evalAlgHom O Ai i).comp ((e : L →ₐ[K] _).restrictScalars O)
  let φ : integralClosure O L →ₗ[O] (∀ i, integralClosure O (Ai i)) := LinearMap.pi fun i ↦
    ((ψ i).toLinearMap.comp (integralClosure O L).val.toLinearMap).codRestrict
      (integralClosure O (Ai i)).toSubmodule fun x ↦ x.2.map (ψ i)
  refine Module.Finite.of_injective φ fun x y hxy ↦ Subtype.ext (e.injective (funext fun i ↦ ?_))
  exact congrArg Subtype.val (congrFun hxy i)

include K in
/-- **Hartogs extension of integral closures.** Let `L` be an étale algebra over the fraction
field `K` of a Noetherian integrally closed domain `O`, and `[a, b]` a regular sequence in `O`.
Then the integral closure `C` of `O` in `L` is its own Hartogs extension along `(a, b)`. -/
theorem hartogs_integralClosure_eq {a b : O} (hab : RingTheory.Sequence.IsWeaklyRegular O [a, b])
    (hb : b ≠ 0) : hartogs a b (integralClosure O L) = integralClosure O L := by
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K L).1 inferInstance
  let _ (i : I) : Algebra O (Ai i) := ((algebraMap K (Ai i)).comp (algebraMap O K)).toAlgebra
  have (i : I) : IsScalarTower O K (Ai i) := .of_algebraMap_eq' rfl
  have (i : I) : Module.Finite K (Ai i) := (hAi i).1
  have (i : I) : Algebra.IsSeparable K (Ai i) := (hAi i).2
  let e' : L ≃ₐ[O] (∀ i, Ai i) := e.restrictScalars O
  refine le_antisymm (fun f ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ ↦ ?_) le_hartogs
  have hc (i : I) : IsIntegral O (e' f i) := by
    have hmem (c : O) (k : ℕ) (hk : c ^ k • f ∈ integralClosure O L) :
        c ^ k • e' f i ∈ integralClosure O (Ai i) := by
      have := (hk : IsIntegral O (c ^ k • f)).map ((Pi.evalAlgHom O Ai i).comp e'.toAlgHom)
      exact (mem_integralClosure_iff _ _).2 (by simpa using this)
    exact hartogs_integralClosure_le_of_field K hab hb ⟨⟨n, hmem a n hn⟩, ⟨m, hmem b m hm⟩⟩
  have := (isIntegral_pi hc).map e'.symm.toAlgHom
  exact (mem_integralClosure_iff _ _).2 (by simpa using this)

end RingTheory.DepthTwo
