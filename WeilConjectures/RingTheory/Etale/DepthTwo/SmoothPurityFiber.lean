/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.RegularLocalRing.Smooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The fibre of a smooth algebra through a diagonal point

Let `B` be an `R₀`-algebra, `P` a prime of `B` over the prime `q` of `R₀`, `κ(q)` and `κ(P)` the
residue fields and `F = κ(q) ⊗_{R₀} B` the fibre of `B` over `q`. The prime `P` corresponds to the
prime `RingTheory.DepthTwo.fiberPrime q P` of `F`, the kernel of `F → κ(P)`; when `B` is smooth
over `R₀`, the local ring of `F` there is a regular local ring, hence a domain
(`RingTheory.DepthTwo.isDomain_localization_fiberPrime`).

The main result `RingTheory.DepthTwo.exists_diagonal_fiber` produces, for `β ∈ B` with nonzero
image in that local ring, a ring map `ψ` from `B ⊗_{R₀} B` to a nonzero ring `E` which inverts the
elements outside the diagonal prime over `P`, kills `1 ⊗ P` and does not make `β ⊗ 1` nilpotent:
`E` is the local ring of `F ⊗_{κ(q)} κ(P)` (the fibre of the second projection through the
diagonal point) at the diagonal point, which is flat over the local ring of `F` at `P`.

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct

namespace RingTheory.DepthTwo

variable {R₀ B : Type u} [CommRing R₀] [CommRing B] [Algebra R₀ B]
  (q : Ideal R₀) [q.IsPrime] (P : Ideal B) [P.IsPrime] (hP : q = P.comap (algebraMap R₀ B))

/-- A base change `F ⊗_k K` along an algebra `K` over a field `k` is flat over `F`. (This is an
instance, stated separately to help instance search when `F` is itself a tensor product.) -/
lemma flat_tensorProduct_of_field (k K F : Type*) [Field k] [CommRing K] [Algebra k K]
    [CommRing F] [Algebra k F] : Module.Flat F (F ⊗[k] K) :=
  inferInstance

/-- The map `κ(q) ⊗_{R₀} B → κ(P)` from the fibre of `B` over `q` to the residue field at a prime
`P` over `q`. -/
noncomputable def fiberToResidueField : q.Fiber B →ₐ[R₀] P.ResidueField :=
  Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ q P (Algebra.ofId R₀ B) hP)
    (IsScalarTower.toAlgHom R₀ B P.ResidueField) fun _ _ ↦ .all _ _

/-- The prime of the fibre `κ(q) ⊗_{R₀} B` corresponding to a prime `P` of `B` over `q`. -/
noncomputable def fiberPrime : Ideal (q.Fiber B) := RingHom.ker (fiberToResidueField q P hP)

instance : (fiberPrime q P hP).IsPrime := RingHom.ker_isPrime _

lemma fiberToResidueField_one_tmul (b : B) :
    fiberToResidueField q P hP (1 ⊗ₜ b) = algebraMap B P.ResidueField b := by
  simp [fiberToResidueField]

lemma comap_fiberPrime :
    (fiberPrime q P hP).comap (Algebra.TensorProduct.includeRight : B →ₐ[R₀] q.Fiber B) = P := by
  ext b
  simp [fiberPrime, fiberToResidueField_one_tmul]

/-- The map from the local ring `B_P` to the local ring of the fibre at `P`. -/
noncomputable def fiberLocalRingHom :
    Localization.AtPrime P →+* Localization.AtPrime (fiberPrime q P hP) :=
  Localization.localRingHom P _ (Algebra.TensorProduct.includeRight : B →ₐ[R₀] q.Fiber B)
    (comap_fiberPrime q P hP).symm

lemma fiberLocalRingHom_algebraMap (b : B) :
    fiberLocalRingHom q P hP (algebraMap B _ b) = algebraMap (q.Fiber B) _ (1 ⊗ₜ b) :=
  Localization.localRingHom_to_map _ _ _ _ _

/-- The local rings of the fibre of a smooth algebra are domains (they are regular). -/
instance isDomain_localization_fiberPrime [Algebra.Smooth R₀ B] :
    IsDomain (Localization.AtPrime (fiberPrime q P hP)) :=
  have := Algebra.Smooth.isRegularLocalRing_localization q.ResidueField (q.Fiber B)
    (fiberPrime q P hP)
  inferInstance

/-- **The fibre of the second projection through the diagonal point.** Let `β ∈ B` have nonzero
image in the local ring of the fibre `κ(q) ⊗ B` at `P`, and suppose that this local ring is a
domain. Then there is a ring map `ψ : B ⊗_{R₀} B → E` to a nonzero ring which inverts the elements
whose product is not in `P`, kills `1 ⊗ P`, and such that no power of `ψ (β ⊗ 1)` vanishes. -/
theorem exists_diagonal_fiber [IsDomain (Localization.AtPrime (fiberPrime q P hP))] (β : B)
    (hβ : algebraMap (q.Fiber B) (Localization.AtPrime (fiberPrime q P hP)) (1 ⊗ₜ β) ≠ 0) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Nontrivial E) (ψ : B ⊗[R₀] B →+* E),
      (∀ x, Algebra.TensorProduct.lmul' R₀ x ∉ P → IsUnit (ψ x)) ∧
      (∀ m ∈ P, ψ (1 ⊗ₜ m) = 0) ∧ ∀ n : ℕ, ψ (β ⊗ₜ 1) ^ n ≠ 0 := by
  let κq := q.ResidueField
  let κP := P.ResidueField
  let F := q.Fiber B
  let A := Localization.AtPrime (fiberPrime q P hP)
  let ι := Ideal.ResidueField.mapₐ q P (Algebra.ofId R₀ B) hP
  let : Algebra κq κP := ι.toRingHom.toAlgebra
  have : IsScalarTower R₀ κq κP := .of_algebraMap_eq fun r ↦ (ι.commutes r).symm
  let D := F ⊗[κq] κP
  -- the map `D → κ(P)` and the diagonal prime of `D`
  let χF : F →ₐ[κq] κP := Algebra.TensorProduct.lift (Algebra.ofId κq κP)
    (IsScalarTower.toAlgHom R₀ B κP) fun _ _ ↦ .all _ _
  have : IsScalarTower κq κq F := IsScalarTower.left _
  have : IsScalarTower κq κq κP := IsScalarTower.left _
  let χ : D →ₐ[κq] κP := Algebra.TensorProduct.lift χF (AlgHom.id κq κP) fun _ _ ↦ .all _ _
  let ΔD := RingHom.ker χ
  have : ΔD.IsPrime := RingHom.ker_isPrime _
  let E := Localization.AtPrime ΔD
  have hχF (y : F) : χF y = fiberToResidueField q P hP y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul c b =>
      rw [Algebra.TensorProduct.lift_tmul, fiberToResidueField, Algebra.TensorProduct.lift_tmul,
        Algebra.ofId_apply, RingHom.algebraMap_toAlgebra]
      rfl
  have hχ (y : F) (c : κP) : χ (y ⊗ₜ c) = χF y * c := Algebra.TensorProduct.lift_tmul _ _ _ y c
  have hcomap : fiberPrime q P hP = ΔD.comap (algebraMap F D) := by
    ext y
    rw [Ideal.mem_comap, fiberPrime, RingHom.mem_ker, RingHom.mem_ker, ← hχF]
    exact (by rw [mul_one] : χF y * 1 = χF y) ▸ (hχ y 1).symm ▸ Iff.rfl
  -- the map `B ⊗ B → D`
  let f₁ : B →ₐ[R₀] D := ((Algebra.TensorProduct.includeLeft : F →ₐ[κq] D).restrictScalars R₀).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[R₀] F)
  let f₂ : B →ₐ[R₀] D := ((Algebra.TensorProduct.includeRight : κP →ₐ[κq] D).restrictScalars
    R₀).comp (IsScalarTower.toAlgHom R₀ B κP)
  have hf₁ (b : B) : f₁ b = ((1 : κq) ⊗ₜ b : F) ⊗ₜ (1 : κP) := rfl
  have hf₂ (b : B) : f₂ b = (1 : F) ⊗ₜ algebraMap B κP b := rfl
  let ψ₀ : B ⊗[R₀] B →ₐ[R₀] D := Algebra.TensorProduct.lift f₁ f₂ fun _ _ ↦ .all _ _
  have hψ₀ (b₁ b₂ : B) : ψ₀ (b₁ ⊗ₜ b₂) = f₁ b₁ * f₂ b₂ := Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hχψ (x : B ⊗[R₀] B) :
      χ (ψ₀ x) = algebraMap B κP (Algebra.TensorProduct.lmul' R₀ x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul b₁ b₂ =>
      rw [hψ₀, map_mul, hf₁, hf₂, hχ, hχ, hχF, fiberToResidueField_one_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      have h1 : χF (1 : F) = 1 := map_one _
      rw [h1, one_mul, mul_one]
  -- flatness of `E` over the local ring `A` of the fibre
  let : Algebra A E := (Localization.localRingHom _ ΔD (algebraMap F D) hcomap).toAlgebra
  have hAE (y : F) : algebraMap A E (algebraMap F A y) = algebraMap D E (algebraMap F D y) :=
    Localization.localRingHom_to_map _ _ _ _ _
  have : IsScalarTower F A E := .of_algebraMap_eq fun y ↦ by
    rw [hAE, ← IsScalarTower.algebraMap_apply]
  have : Module.Flat F D := flat_tensorProduct_of_field κq κP F
  have : Module.Flat D E := IsLocalization.flat E ΔD.primeCompl
  have : IsScalarTower F D E := inferInstance
  have : Module.Flat F E := Module.Flat.trans F D E
  have : Module.Flat A E :=
    (Module.flat_iff_of_isLocalization A (fiberPrime q P hP).primeCompl E).2 inferInstance
  refine ⟨E, inferInstance, inferInstance, (algebraMap D E).comp ψ₀.toRingHom, fun x hx ↦ ?_,
    fun m hm ↦ ?_, fun n ↦ ?_⟩
  · refine IsLocalization.map_units E (M := ΔD.primeCompl) ⟨ψ₀ x, fun h ↦ hx ?_⟩
    have : χ (ψ₀ x) = 0 := h
    rwa [hχψ, Ideal.algebraMap_residueField_eq_zero] at this
  · have : algebraMap B κP m = 0 := (Ideal.algebraMap_residueField_eq_zero).2 hm
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hψ₀, hf₂, this,
      TensorProduct.tmul_zero, mul_zero, map_zero]
  · have hβ' : (algebraMap D E).comp ψ₀.toRingHom (β ⊗ₜ 1) =
        algebraMap A E (algebraMap F A (1 ⊗ₜ β)) := by
      rw [hAE]
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hψ₀, map_one,
        mul_one, hf₁]
      rfl
    rw [hβ', ← map_pow]
    intro h0
    have hreg : IsSMulRegular E (algebraMap F A (1 ⊗ₜ β) ^ n) :=
      Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero (pow_ne_zero n hβ))
    refine one_ne_zero (hreg (?_ : _ • (1 : E) = _ • 0))
    rw [smul_zero, Algebra.smul_def, mul_one, h0]

end RingTheory.DepthTwo
