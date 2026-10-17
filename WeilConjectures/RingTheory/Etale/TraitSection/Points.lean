/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.TraitSection.Rigidity
public import WeilConjectures.RingTheory.Invariant.TensorIntegralClosure
public import WeilConjectures.RingTheory.Invariant.Kummer
public import WeilConjectures.RingTheory.DiscreteValuationRing.AdjoinRoot
public import WeilConjectures.Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Points along a section after a tame Kummer base change

Let `A` be a discrete valuation ring with uniformizer `ϖ` and fraction field `K`, `R` a local
`A`-algebra with an `A`-algebra section `σ : R → A`, `M` an `R`-algebra and `χⱼ : M → K` ring
maps over `σ` which are pairwise distinct on the elements of `M` integral over `R`. Let
`R' = R[t] ⧸ (tⁿ - ϖ)` and `T'` the integral closure of `R'` in `R' ⊗[R] M`, formally unramified
and essentially of finite type over `R'`. Then the `χⱼ` induce pairwise distinct points
`T' → κ(R')`, invariant under the Kummer action when `ζ ∈ A` is an `n`-th root of unity
(`Algebra.TraitSection.exists_points_kummer`).

Proof: `σ` extends to `σ' : R' → A₂ = A[t] ⧸ (tⁿ - ϖ)` (a discrete valuation ring with fraction
field `A₂ ⊗[A] K`), and `σ' ⊗ χⱼ` maps `T'` to `A₂` by integrality, Kummer-equivariantly. The
residues are distinct by rigidity of maps out of unramified algebras
(`Algebra.FormallyUnramified.algHom_eq_of_isLocalRing`) and invariant since the Kummer action is
trivial on `κ(A₂) ≅ κ(R')`.

This is used in the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

open Polynomial IsLocalRing TensorProduct

namespace Algebra.TraitSection

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
  {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [IsLocalRing R] [Algebra A R]
  [Fact (algebraMap A R ϖ ∈ maximalIdeal R)]
  {M : Type*} [CommRing M] [Algebra R M]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

set_option maxHeartbeats 1600000 in
/-- **Points along a section after a tame Kummer base change.** See the module docstring. -/
theorem exists_points_kummer (hϖ : Irreducible ϖ) (σ : R →ₐ[A] A) {k : ℕ}
    (χ : Fin k → (M →+* K))
    (hχ : ∀ j, (χ j).comp (algebraMap R M) = (algebraMap A K).comp σ.toRingHom)
    (hχinj : ∀ j l, (∀ m : M, IsIntegral R m → χ j m = χ l m) → j = l)
    [Algebra.FormallyUnramified (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)))
      (integralClosure (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)))
        (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)) ⊗[R] M))]
    [Algebra.EssFiniteType (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)))
      (integralClosure (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)))
        (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)) ⊗[R] M))]
    {ζ : A} (hζ : ζ ^ n = 1) :
    ∃ ψ : Fin k → (integralClosure (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)))
        (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)) ⊗[R] M) →ₐ[AdjoinRoot (X ^ n -
          C (algebraMap A R ϖ))] ResidueField (AdjoinRoot (X ^ n - C (algebraMap A R ϖ)))),
      Function.Injective ψ ∧
      haveI hζR : algebraMap A R ζ ^ n = 1 := by rw [← map_pow, hζ, map_one]
      letI := AdjoinRoot.kummerAction n (algebraMap A R ϖ) hζR
      haveI : SMulCommClass (Multiplicative (ZMod n)) R
          (AdjoinRoot (X ^ n - C (algebraMap A R ϖ))) :=
        AdjoinRoot.smulCommClass_kummerAction n (algebraMap A R ϖ) hζR
      ∀ j (g : Multiplicative (ZMod n)) t,
        ψ j (Algebra.IsInvariant.integralClosureMap (R := R)
          (R' := AdjoinRoot (X ^ n - C (algebraMap A R ϖ))) (M := M)
          (Multiplicative (ZMod n)) g t) = ψ j t := by
  classical
  set R' := AdjoinRoot (X ^ n - C (algebraMap A R ϖ))
  set A₂ := AdjoinRoot (X ^ n - C ϖ)
  have hn0 : n ≠ 0 := NeZero.ne n
  have : Fact (ϖ ∈ maximalIdeal A) := ⟨hϖ.not_isUnit⟩
  have h₂ := AdjoinRoot.isAdjoinRoot (X ^ n - C ϖ)
  have : IsDomain A₂ := h₂.isDomain_of_X_pow_sub_C hϖ hn0
  have : IsDiscreteValuationRing A₂ := h₂.isDiscreteValuationRing_of_X_pow_sub_C hϖ hn0
  have hinjA : Function.Injective (algebraMap A A₂) :=
    AdjoinRoot.injective_algebraMap_X_pow_sub_C n ϖ
  -- the fraction field `K₂ = A₂ ⊗[A] K`
  let K₂ := A₂ ⊗[A] K
  have : IsFractionRing A₂ K₂ := by
    refine IsFractionRing.tensorProduct_of_comap_eq_bot hinjA (fun q hq hq0 ↦ ?_) K
    by_contra hne
    have hmax : q.IsMaximal := hq.isMaximal hne
    have hroot : h₂.root ∈ q := h₂.root_mem_of_isMaximal hϖ hn0 q
    have : algebraMap A A₂ ϖ ∈ q := by
      rw [← h₂.root_pow_eq]
      exact q.pow_mem_of_mem hroot n (Nat.pos_of_ne_zero hn0)
    have h0 : ϖ ∈ q.comap (algebraMap A A₂) := this
    rw [hq0, Ideal.mem_bot] at h0
    exact hϖ.ne_zero h0
  have hinjK₂ : Function.Injective (algebraMap A₂ K₂) := IsFractionRing.injective A₂ K₂
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have hincR : Function.Injective (Algebra.TensorProduct.includeRight : K →ₐ[A] K₂) :=
    Algebra.TensorProduct.includeRight_injective hinjA
  -- the extension `σ' : R' → A₂` of the section
  have hσϖ : σ (algebraMap A R ϖ) = ϖ := σ.commutes ϖ
  let σ' : R' →+* A₂ := AdjoinRoot.lift ((algebraMap A A₂).comp σ.toRingHom)
    (AdjoinRoot.root _) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, AdjoinRoot.root_X_pow_sub_C_pow]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hσϖ]
      exact sub_eq_zero.2 rfl)
  have hσ'alg (r : R) : σ' (algebraMap R R' r) = algebraMap A A₂ (σ r) := by
    rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
    rfl
  have hσ'root : σ' (AdjoinRoot.root _) = AdjoinRoot.root _ := AdjoinRoot.lift_root _
  have hσ'surj : Function.Surjective σ' := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    refine ⟨AdjoinRoot.mk _ (p.map (algebraMap A R)), ?_⟩
    have hc : ((algebraMap A A₂).comp σ.toRingHom).comp (algebraMap A R) = algebraMap A A₂ := by
      ext a
      simp
    rw [AdjoinRoot.lift_mk, eval₂_map, hc, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  have : IsLocalHom σ' := IsLocalHom.of_surjective σ' hσ'surj
  let κ : ResidueField R' ≃+* ResidueField A₂ := RingEquiv.ofBijective (ResidueField.map σ')
    ⟨(ResidueField.map σ').injective, fun y ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective y
      obtain ⟨r, rfl⟩ := hσ'surj a
      exact ⟨residue R' r, ResidueField.map_residue σ' r⟩⟩
  -- the maps `Ξⱼ = σ' ⊗ χⱼ : R' ⊗[R] M → K₂`
  letI : Algebra R K₂ := ((algebraMap A K₂).comp σ.toRingHom).toAlgebra
  have hRK₂ (r : R) : algebraMap R K₂ r = algebraMap A K₂ (σ r) := rfl
  let f : R' →ₐ[R] K₂ :=
    { (algebraMap A₂ K₂).comp σ' with
      commutes' := fun r ↦ (congrArg (algebraMap A₂ K₂) (hσ'alg r)).trans rfl }
  let g (j : Fin k) : M →ₐ[R] K₂ :=
    { (Algebra.TensorProduct.includeRight : K →ₐ[A] K₂).toRingHom.comp (χ j) with
      commutes' := fun r ↦ by
        have := congr($(hχ j) r)
        simp only [RingHom.comp_apply] at this
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, this,
          AlgHom.commutes]
        exact (Algebra.TensorProduct.includeRight.commutes (σ r)).trans rfl }
  let Ξ (j : Fin k) : R' ⊗[R] M →ₐ[R] K₂ :=
    Algebra.TensorProduct.lift f (g j) fun _ _ ↦ Commute.all _ _
  have hΞtmul (j : Fin k) (a : R') (m : M) : Ξ j (a ⊗ₜ m) = σ' a ⊗ₜ χ j m := by
    rw [Algebra.TensorProduct.lift_tmul]
    change (σ' a ⊗ₜ[A] (1 : K)) * ((1 : A₂) ⊗ₜ[A] χ j m) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hΞalg (j : Fin k) (a : R') : Ξ j (algebraMap R' _ a) = algebraMap A₂ K₂ (σ' a) := by
    exact (hΞtmul j a 1).trans (by rw [map_one]; rfl)
  -- the maps `ρⱼ : T' → A₂`
  have hmem (j : Fin k) (t : integralClosure R' (R' ⊗[R] M)) :
      ∃ a : A₂, algebraMap A₂ K₂ a = Ξ j t := by
    have hint : IsIntegral A₂ (Ξ j (t : R' ⊗[R] M)) :=
      IsIntegral.map_of_comp_eq σ' (Ξ j).toRingHom (RingHom.ext fun a ↦ (hΞalg j a).symm) t.2
    exact IsIntegrallyClosed.isIntegral_iff.1 hint
  choose ρ hρ using hmem
  letI : Algebra R' A₂ := σ'.toAlgebra
  let ρh (j : Fin k) : integralClosure R' (R' ⊗[R] M) →ₐ[R'] A₂ :=
    { toFun := ρ j
      map_one' := hinjK₂ (by simp [hρ])
      map_mul' x y := hinjK₂ (by simp [hρ])
      map_zero' := hinjK₂ (by simp [hρ])
      map_add' x y := hinjK₂ (by simp [hρ])
      commutes' r := hinjK₂ ((hρ j _).trans (hΞalg j r)) }
  have hρh (j : Fin k) (t) : algebraMap A₂ K₂ (ρh j t) = Ξ j t := hρ j t
  let ψ (j : Fin k) : integralClosure R' (R' ⊗[R] M) →ₐ[R'] ResidueField R' :=
    { κ.symm.toRingHom.comp ((residue A₂).comp (ρh j).toRingHom) with
      commutes' := fun r ↦ by
        have h1 : (ρh j) (algebraMap R' _ r) = σ' r := (ρh j).commutes r
        exact (congrArg (fun x ↦ κ.symm (residue A₂ x)) h1).trans
          (κ.symm_apply_apply (residue R' r)) }
  have hψ (j : Fin k) (t) : ψ j t = κ.symm (residue A₂ (ρh j t)) := rfl
  refine ⟨ψ, fun j l hjl ↦ hχinj j l fun m hm ↦ ?_, ?_⟩
  · have hres : ρh j = ρh l := Algebra.FormallyUnramified.algHom_eq_of_isLocalRing _ _ fun t ↦ by
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      have := congr($hjl t)
      rw [hψ, hψ] at this
      exact κ.symm.injective this
    have hmT : Algebra.TensorProduct.includeRight m ∈ integralClosure R' (R' ⊗[R] M) :=
      (hm.map (Algebra.TensorProduct.includeRight : M →ₐ[R] R' ⊗[R] M)).tower_top
    have h2 := congr(algebraMap A₂ K₂ ($hres ⟨_, hmT⟩))
    rw [hρh, hρh] at h2
    simp only [Algebra.TensorProduct.includeRight_apply, hΞtmul, map_one] at h2
    exact hincR h2
  · intro j g t
    have hζR : algebraMap A R ζ ^ n = 1 := by rw [← map_pow, hζ, map_one]
    let Γ := Multiplicative (ZMod n)
    letI := AdjoinRoot.kummerAction n (algebraMap A R ϖ) hζR
    have : SMulCommClass Γ R R' := AdjoinRoot.smulCommClass_kummerAction n (algebraMap A R ϖ) hζR
    letI := AdjoinRoot.kummerAction n ϖ hζ
    have : SMulCommClass Γ A A₂ := AdjoinRoot.smulCommClass_kummerAction n ϖ hζ
    letI := Algebra.IsInvariant.tensorAction (R := A) (R' := A₂) (M := K) Γ
    letI := Algebra.IsInvariant.tensorAction (R := R) (R' := R') (M := M) Γ
    -- `σ'` is equivariant
    have he1 (a : R') : σ' (g • a) = g • σ' a := by
      have key : σ'.comp (AdjoinRoot.kummerAut n (algebraMap A R ϖ) hζR g.toAdd).toRingHom =
          (AdjoinRoot.kummerAut n ϖ hζ g.toAdd).toRingHom.comp σ' := by
        refine AdjoinRoot.ringHom_ext (RingHom.ext fun r ↦ ?_) ?_
        · have h := hσ'alg r
          rw [AdjoinRoot.algebraMap_eq] at h
          exact (congrArg σ' (AdjoinRoot.kummerAut_of n (algebraMap A R ϖ) hζR _ r)).trans
            (h.trans (((AdjoinRoot.kummerAut n ϖ hζ g.toAdd).commutes (σ r)).symm.trans
              (congrArg (AdjoinRoot.kummerAut n ϖ hζ g.toAdd) h.symm)))
        · have h := hσ'alg (algebraMap A R ζ ^ (Multiplicative.toAdd g).val)
          rw [AdjoinRoot.algebraMap_eq] at h
          rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
            AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AdjoinRoot.kummerAut_root, map_mul, h,
            hσ'root, AdjoinRoot.kummerAut_root, ← map_pow, σ.commutes, AdjoinRoot.algebraMap_eq,
            Algebra.algebraMap_self, RingHom.id_apply]
      exact congr($key a)
    -- `Ξⱼ` is equivariant
    have he2 (x : R' ⊗[R] M) : Ξ j (g • x) = g • Ξ j x := by
      induction x with
      | zero => simp only [smul_zero, map_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a m =>
        rw [Algebra.IsInvariant.tensorAction_smul_tmul, hΞtmul, hΞtmul,
          Algebra.IsInvariant.tensorAction_smul_tmul, he1]
    have he3 : ρh j (Algebra.IsInvariant.integralClosureMap Γ g t) = g • ρh j t := hinjK₂ <|
      calc algebraMap A₂ K₂ (ρh j (Algebra.IsInvariant.integralClosureMap Γ g t))
          = Ξ j (g • (t : R' ⊗[R] M)) := hρh j _
        _ = g • Ξ j t := he2 _
        _ = g • algebraMap A₂ K₂ (ρh j t) := by rw [hρh]
        _ = algebraMap A₂ K₂ (g • ρh j t) := Algebra.IsInvariant.tensorAction_smul_algebraMap g _
    rw [hψ, hψ, he3, AdjoinRoot.residue_kummerAction_smul n ϖ hζ
      (AdjoinRoot.root_mem_maximalIdeal n ϖ) g]

end Algebra.TraitSection
