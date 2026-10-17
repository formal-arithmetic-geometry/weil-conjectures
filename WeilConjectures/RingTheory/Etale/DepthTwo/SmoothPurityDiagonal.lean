/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Diagonal
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityFiber
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.FiniteStability

/-!
# Étaleness at a point of a smooth algebra through the diagonal

Let `B` be a smooth algebra over a Noetherian ring `R₀`, `P` a prime of `B` over `q` and
`O = B_P`. Let `T` be a finite `O`-algebra, `a ∈ R₀` and `b ∈ O` such that `(a, b)` is a regular
pair on `T` and `T` is étale over `D(a)` and over `D(b)`. If `b` has nonzero image in the local
ring of the fibre `κ(q) ⊗ B` at `P`, then `T` is étale over `O`
(`RingTheory.DepthTwo.etale_of_smooth_of_diagonal`).

This applies `RingTheory.DepthTwo.etale_of_diagonal` to the local ring `R = (B ⊗_{R₀} B)_{Δ(P)}`
of the diagonal, with the first projection as structure map, the multiplication as section and
the swap as involution. The required prime of the completion `R^` comes from
`RingTheory.DepthTwo.exists_diagonal_fiber` and the faithful flatness of `R → R^`.

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing

namespace RingTheory.DepthTwo

variable {R₀ B : Type u} [CommRing R₀] [CommRing B] [Algebra R₀ B]

/-- **Étaleness through the diagonal of a smooth algebra.** See the module docstring. -/
theorem etale_of_smooth_of_diagonal [IsNoetherianRing R₀] [Algebra.Smooth R₀ B]
    (q : Ideal R₀) [q.IsPrime] (P : Ideal B) [P.IsPrime] (hP : q = P.comap (algebraMap R₀ B))
    {T : Type*} [CommRing T] [Algebra (Localization.AtPrime P) T]
    [Module.Finite (Localization.AtPrime P) T] {a : R₀} {b : Localization.AtPrime P}
    (hT : IsRegularPair (algebraMap R₀ (Localization.AtPrime P) a) b T)
    [Algebra.Etale (Localization.Away (algebraMap R₀ (Localization.AtPrime P) a))
      (Localization.Away (algebraMap R₀ (Localization.AtPrime P) a) ⊗[Localization.AtPrime P] T)]
    [Algebra.Etale (Localization.Away b) (Localization.Away b ⊗[Localization.AtPrime P] T)]
    (hb : fiberLocalRingHom q P hP b ≠ 0) :
    Algebra.Etale (Localization.AtPrime P) T := by
  let O := Localization.AtPrime P
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R₀ B
  let Bt := B ⊗[R₀] B
  let μ : Bt →ₐ[R₀] B := Algebra.TensorProduct.lmul' R₀
  let Δ := P.comap μ
  let R := Localization.AtPrime Δ
  have : Algebra.FiniteType R₀ Bt := .trans (S := B) inferInstance inferInstance
  have : IsNoetherianRing Bt := Algebra.FiniteType.isNoetherianRing R₀ Bt
  have hΔ₁ : P = Δ.comap (Algebra.TensorProduct.includeLeft : B →ₐ[R₀] Bt) := by
    ext x
    simp only [Δ, μ, Ideal.mem_comap]
    rw [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  -- the structure maps
  let : Algebra O R := (Localization.localRingHom P Δ
    (Algebra.TensorProduct.includeLeft : B →ₐ[R₀] Bt) hΔ₁).toAlgebra
  let : Algebra R O := (Localization.localRingHom Δ P μ rfl).toAlgebra
  have hOR (x : B) : algebraMap O R (algebraMap B O x) = algebraMap Bt R (x ⊗ₜ 1) :=
    Localization.localRingHom_to_map _ _ _ _ _
  have hRO (x : Bt) : algebraMap R O (algebraMap Bt R x) = algebraMap B O (μ x) :=
    Localization.localRingHom_to_map _ _ _ _ _
  have : IsScalarTower O R O := .of_algebraMap_eq' <| IsLocalization.ringHom_ext P.primeCompl <|
    RingHom.ext fun x ↦ by
      simp only [RingHom.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hOR, hRO, Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  have : IsScalarTower B O R := .of_algebraMap_eq fun x ↦ (hOR x).symm
  have : Algebra.FormallySmooth O R := Algebra.FormallySmooth.localization_base P.primeCompl
  have : Module.Flat O R := (Module.flat_iff_of_isLocalization O P.primeCompl R).2 inferInstance
  -- the swap
  let c : Bt ≃ₐ[R₀] Bt := Algebra.TensorProduct.comm R₀ B B
  have hμc (x : Bt) : μ (c x) = μ x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul x y =>
      rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, mul_comm]
  have hc : Δ = Δ.comap (c.toRingEquiv : Bt →+* Bt) := by
    ext x
    simp only [Δ, Ideal.mem_comap]
    rw [RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, hμc]
  let τ : R ≃+* R := Localization.localRingEquiv Δ Δ c.toRingEquiv hc
  have hτ₀ (x : Bt) : τ (algebraMap Bt R x) = algebraMap Bt R (c x) :=
    Localization.localRingHom_to_map Δ Δ _ hc x
  have hcc (x : Bt) : c (c x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x y => rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul]
  have hτ (r : R) : τ (τ r) = r := by
    have : τ.toRingHom.comp τ.toRingHom = RingHom.id R :=
      IsLocalization.ringHom_ext Δ.primeCompl <| RingHom.ext fun x ↦ by
        simp only [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom]
        rw [hτ₀, hτ₀, hcc]
    exact congrArg (· r) this
  have hτμ (r : R) : algebraMap R O (τ r) = algebraMap R O r := by
    have : (algebraMap R O).comp τ.toRingHom = algebraMap R O :=
      IsLocalization.ringHom_ext Δ.primeCompl <| RingHom.ext fun x ↦ by
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [hτ₀, hRO, hRO, hμc]
    exact congrArg (· r) this
  have ha : τ (algebraMap O R (algebraMap R₀ O a)) = algebraMap O R (algebraMap R₀ O a) := by
    rw [IsScalarTower.algebraMap_apply R₀ B O, hOR, hτ₀, Algebra.TensorProduct.comm_tmul,
      Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  -- the point of the fibre of the second projection
  obtain ⟨⟨β, s⟩, hbs⟩ := IsLocalization.mk'_surjective P.primeCompl b
  dsimp only at hbs
  subst hbs
  let A := Localization.AtPrime (fiberPrime q P hP)
  have hβ : algebraMap (q.Fiber B) A (1 ⊗ₜ β) ≠ 0 := by
    intro h0
    apply hb
    have h1 := congrArg (fiberLocalRingHom q P hP)
      (IsLocalization.mk'_spec O β s)
    rw [map_mul, fiberLocalRingHom_algebraMap, fiberLocalRingHom_algebraMap, h0] at h1
    have hs : (1 : q.ResidueField) ⊗ₜ (s : B) ∈ (fiberPrime q P hP).primeCompl := fun hs ↦
      s.2 ((SetLike.ext_iff.1 (comap_fiberPrime q P hP) (s : B)).1 hs)
    exact ((IsLocalization.map_units A ⟨_, hs⟩).mul_left_eq_zero).1 h1
  obtain ⟨E, _, _, ψ, hψu, hψP, hψβ⟩ := exists_diagonal_fiber q P hP β hβ
  let ψR : R →+* E := IsLocalization.lift (M := Δ.primeCompl) (S := R) fun x ↦ hψu x.1 x.2
  have hψR (x : Bt) : ψR (algebraMap Bt R x) = ψ x := IsLocalization.lift_eq _ _
  set y := τ (algebraMap O R (IsLocalization.mk' O β s))
  have hC1 (n : ℕ) : y ^ n ∉ (maximalIdeal O).map (algebraMap O R) := by
    intro hn
    let g := ψR.comp τ.toRingHom
    have hJ : (maximalIdeal O).map (algebraMap O R) ≤ RingHom.ker g := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hOR, hτ₀,
        Algebra.TensorProduct.comm_tmul, hψR]
      exact hψP m hm
    have h0 : g (y ^ n) = 0 := hJ hn
    have hgy : g y = ψR (algebraMap O R (IsLocalization.mk' O β s)) := by
      simp only [g, y, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        hτ]
    have hz : ψR (algebraMap O R (IsLocalization.mk' O β s)) *
        ψR (algebraMap O R (algebraMap B O s)) = ψ (β ⊗ₜ 1) := by
      rw [← map_mul, ← map_mul, IsLocalization.mk'_spec, hOR, hψR]
    apply hψβ n
    rw [← hz, mul_pow, ← hgy, ← map_pow, h0, zero_mul]
  -- the prime of the completion
  let I := RingHom.ker (algebraMap R O)
  have hI : I ≠ ⊤ := RingHom.ker_ne_top _
  have : Module.FaithfullyFlat R (AdicCompletion I R) := faithfullyFlat_adicCompletion I hI
  have hC2 : algebraMap R (AdicCompletion I R) y ∉
      ((maximalIdeal O).map (algebraMap O (AdicCompletion I R))).radical := by
    rintro ⟨n, hn⟩
    rw [IsScalarTower.algebraMap_eq O R (AdicCompletion I R), ← Ideal.map_map, ← map_pow] at hn
    apply hC1 n
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion I R)
      ((maximalIdeal O).map (algebraMap O R))]
    exact hn
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf] at hC2
  push Not at hC2
  obtain ⟨Q, ⟨hJQ, hQ⟩, hyQ⟩ := hC2
  have hQO : Ideal.comap (algebraMap O (AdicCompletion I R)) Q = maximalIdeal O :=
    le_antisymm (IsLocalRing.le_maximalIdeal
      (Ideal.comap_ne_top (algebraMap O (AdicCompletion I R)) hQ.ne_top))
      (Ideal.map_le_iff_le_comap.1 hJQ)
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing Δ.primeCompl R inferInstance
  have : IsNoetherianRing O := IsLocalization.isNoetherianRing P.primeCompl O inferInstance
  exact etale_of_diagonal (O := O) (R := R) τ hτ hτμ ha hT Q hQO hyQ

end RingTheory.DepthTwo
