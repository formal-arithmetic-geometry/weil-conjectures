/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Local
public import WeilConjectures.RingTheory.Etale.DepthTwo.Lift
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Auxiliary results for étaleness through the diagonal

* Regular pairs are stable under adding a nilpotent element to the second element
  (`RingTheory.DepthTwo.IsRegularPair.add_right`), under flat base change
  (`RingTheory.DepthTwo.IsRegularPair.lTensor`) and under linear equivalences.
* A ring endomorphism `τ` of `R` with `τ(I) ⊆ I` induces an endomorphism of the `I`-adic
  completion (`RingTheory.DepthTwo.adicCompletionMap`).
* Ring homomorphisms out of a tensor product (`RingTheory.DepthTwo.tensorLift`), when the target is
  not an algebra over the base ring.
* An endomorphism of a finite module which is the identity modulo an ideal contained in the
  Jacobson radical is bijective (`RingTheory.DepthTwo.bijective_of_sub_mem_smul_top`).
* Étaleness over a basic open is transported along a semilinear automorphism
  (`RingTheory.DepthTwo.etale_away_of_semilinear`).
-/

@[expose] public section

open scoped Pointwise

open TensorProduct

namespace RingTheory.DepthTwo

section Regular

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- If `y` is `M`-regular and `j` acts nilpotently on `M`, then `y + j` is `M`-regular. -/
lemma isSMulRegular_add_of_pow_smul_eq_zero {y j : A} (hy : IsSMulRegular M y) {k : ℕ}
    (hj : ∀ m : M, j ^ k • m = 0) : IsSMulRegular M (y + j) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  have h1 : y • m = (-j) • m := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, ← add_smul, hm]
  have h2 (n : ℕ) : y ^ n • m = (-j) ^ n • m := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_smul, ih, smul_comm, h1, ← mul_smul, ← pow_succ]
  refine (hy.pow k) ?_
  beta_reduce
  rw [h2, neg_pow, mul_smul, hj]
  simp

/-- A regular pair `(x, y)` stays regular after adding to `y` an element acting nilpotently. -/
lemma IsRegularPair.add_right {x y j : A} (h : IsRegularPair x y M) {k : ℕ}
    (hj : ∀ m : M, j ^ k • m = 0) : IsRegularPair x (y + j) M := by
  obtain ⟨hx, hy, hxy⟩ := h
  refine ⟨hx, isSMulRegular_add_of_pow_smul_eq_zero hy hj, fun m hm ↦ ?_⟩
  set N : Submodule A M := x • ⊤
  have hyN : IsSMulRegular (M ⧸ N) y := by
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro q hq
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul] at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    exact hxy m hq
  have hjN (q : M ⧸ N) : j ^ k • q = 0 := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, hj, Submodule.Quotient.mk_zero]
  have := (isSMulRegular_iff_right_eq_zero_of_smul.1
    (isSMulRegular_add_of_pow_smul_eq_zero hyN hjN)) (Submodule.Quotient.mk m)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.Quotient.mk_eq_zero] at this
  exact this hm

/-- A regular pair on `M` stays regular on `N ⊗ M` for a flat module `N`. -/
lemma IsRegularPair.lTensor {a b : A} (h : IsRegularPair a b M) (N : Type*) [AddCommGroup N]
    [Module A N] [Module.Flat A N] : IsRegularPair a b (N ⊗[A] M) :=
  isRegularPair_of_isWeaklyRegular (isWeaklyRegular_of_isRegularPair h).isWeaklyRegular_lTensor
    (h.2.1.lTensor N)

/-- Regular pairs are transported along linear equivalences. -/
lemma IsRegularPair.of_linearEquiv {a b : A} {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (h : IsRegularPair a b M) : IsRegularPair a b N :=
  isRegularPair_of_isWeaklyRegular
    ((e.isWeaklyRegular_congr [a, b]).1 (isWeaklyRegular_of_isRegularPair h))
    fun x y hxy ↦ e.symm.injective (h.2.1 (by
      beta_reduce at hxy ⊢
      rw [← map_smul, ← map_smul, hxy]))

/-- A regular pair of elements of `O` on `M` is a regular pair of their images in an `O`-algebra
`B` acting compatibly on `M`. -/
lemma isRegularPair_algebraMap {O : Type*} [CommRing O] [Algebra O A] [Module O M]
    [IsScalarTower O A M] {a b : O} (h : IsRegularPair a b M) :
    IsRegularPair (algebraMap O A a) (algebraMap O A b) M := by
  have hs (c : O) (x : M) : algebraMap O A c • x = c • x := algebraMap_smul A c x
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x y hxy ↦ h1 (by simpa only [hs] using hxy),
    fun x y hxy ↦ h2 (by simpa only [hs] using hxy), fun m hm ↦ ?_⟩
  obtain ⟨y, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
  rw [hs, hs] at hy
  obtain ⟨z, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (h3 m ((Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy⟩))
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z, hz.1, (hs a z).trans hz.2⟩

end Regular

section Completion

variable {R : Type*} [CommRing R] (I : Ideal R)

lemma factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]
  have h := AdicCompletion.AdicCauchySequence.mk_eq_mk hle c
  rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at h
  exact Ideal.Quotient.eq.2 h

lemma pow_le_comap_pow {τ : R →+* R} (hτ : I ≤ I.comap τ) (n : ℕ) :
    I ^ n ≤ (I ^ n).comap τ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hτ) n

/-- The ring endomorphism of the `I`-adic completion induced by a ring endomorphism `τ` of `R`
with `τ(I) ⊆ I`. -/
noncomputable def adicCompletionMap (τ : R →+* R) (hτ : I ≤ I.comap τ) :
    AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I
    (fun n ↦ (Ideal.quotientMap (I ^ n) τ (pow_le_comap_pow I hτ n)).comp
      (AdicCompletion.evalₐ I n).toRingHom) fun {m n} hle ↦ by
    ext x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← factorPow_evalₐ I hle x]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [← hy, Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

variable {I}

@[simp]
lemma evalₐ_adicCompletionMap (τ : R →+* R) (hτ : I ≤ I.comap τ) (n : ℕ)
    (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionMap I τ hτ x) =
      Ideal.quotientMap (I ^ n) τ (pow_le_comap_pow I hτ n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ _ _

@[simp]
lemma adicCompletionMap_algebraMap (τ : R →+* R) (hτ : I ≤ I.comap τ) (r : R) :
    adicCompletionMap I τ hτ (algebraMap R (AdicCompletion I R) r) =
      algebraMap R (AdicCompletion I R) (τ r) := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, AlgHom.commutes, AlgHom.commutes]
  rfl

lemma adicCompletionMap_adicCompletionMap {τ : R →+* R} (hτ : I ≤ I.comap τ)
    (hττ : ∀ r, τ (τ r) = r) (x : AdicCompletion I R) :
    adicCompletionMap I τ hτ (adicCompletionMap I τ hτ x) = x := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, evalₐ_adicCompletionMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk, hττ]

lemma evalOneₐ_adicCompletionMap {τ : R →+* R} (hτ : I ≤ I.comap τ) (h : ∀ r, τ r - r ∈ I)
    (x : AdicCompletion I R) :
    AdicCompletion.evalOneₐ I (adicCompletionMap I τ hτ x) = AdicCompletion.evalOneₐ I x := by
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← AdicCompletion.factorₐ_evalₐ_one,
    evalₐ_adicCompletionMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 x)
  rw [← hy, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
  exact Ideal.Quotient.eq.2 (h y)

end Completion

section Tensor

variable {O A B E : Type*} [CommRing O] [CommRing A] [CommRing B] [CommRing E] [Algebra O A]
  [Algebra O B]

/-- The ring homomorphism `A ⊗[O] B → E` given by ring homomorphisms `f : A → E`, `g : B → E`
which agree on `O`. -/
noncomputable def tensorLift (f : A →+* E) (g : B →+* E)
    (h : ∀ x, f (algebraMap O A x) = g (algebraMap O B x)) : A ⊗[O] B →+* E :=
  letI : Algebra O E := (f.comp (algebraMap O A)).toAlgebra
  (Algebra.TensorProduct.lift (R := O) (S := O) { f with commutes' := fun _ ↦ rfl }
    { g with commutes' := fun x ↦ (h x).symm } fun _ _ ↦ Commute.all _ _).toRingHom

@[simp]
lemma tensorLift_tmul (f : A →+* E) (g : B →+* E)
    (h : ∀ x, f (algebraMap O A x) = g (algebraMap O B x)) (a : A) (b : B) :
    tensorLift f g h (a ⊗ₜ b) = f a * g b :=
  rfl

/-- Two ring homomorphisms out of a tensor product agreeing on pure tensors are equal. -/
lemma ringHom_ext_tmul {F G : A ⊗[O] B →+* E} (h : ∀ a b, F (a ⊗ₜ b) = G (a ⊗ₜ b)) :
    F = G := by
  refine RingHom.ext fun x ↦ ?_
  induction x with
  | zero => simp
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Tensor

/-- An endomorphism `g` of a finite module with `x - g x ∈ K M` for all `x`, for an ideal `K`
contained in the Jacobson radical, is bijective (Nakayama). -/
lemma bijective_of_sub_mem_smul_top {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] {K : Ideal A} (hK : K ≤ Ideal.jacobson ⊥) (g : M →ₗ[A] M)
    (hg : ∀ x, x - g x ∈ K • (⊤ : Submodule A M)) : Function.Bijective g := by
  have hs : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hK fun x _ ↦ ?_
    have : x = g x + (x - g x) := by abel
    rw [this]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self g x) (hg x)
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism g hs, hs⟩

section Transport

/-- Étale ring homomorphisms are stable under composition (universe polymorphic version of
`RingHom.Etale.stableUnderComposition`). -/
lemma etale_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S}
    {g : S →+* T} (hf : f.Etale) (hg : g.Etale) : (g.comp f).Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.comp R S T

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]

/-- Étaleness over a basic open `D(s)` is transported along a ring automorphism `σ` of `D` which
is semilinear with respect to a ring automorphism `θ` of `A`: then `D` is étale over `D(θ s)`. -/
lemma etale_away_of_semilinear (θ : A ≃+* A) (σ : D ≃+* D)
    (hσ : ∀ x, σ (algebraMap A D x) = algebraMap A D (θ x)) (s : A)
    [Algebra.Etale (Localization.Away s) (Localization.Away s ⊗[A] D)] :
    Algebra.Etale (Localization.Away (θ s)) (Localization.Away (θ s) ⊗[A] D) := by
  set L := Localization.Away s
  set L' := Localization.Away (θ s)
  have hM : (Submonoid.powers s).map θ.toMonoidHom = Submonoid.powers (θ s) := by
    rw [Submonoid.map_powers]
    rfl
  let e₁ : L ≃+* L' := IsLocalization.ringEquivOfRingEquiv L L' θ hM
  have he₁ (x : A) : e₁ (algebraMap A L x) = algebraMap A L' (θ x) :=
    IsLocalization.ringEquivOfRingEquiv_eq hM x
  have he₁' (x : A) : e₁.symm (algebraMap A L' x) = algebraMap A L (θ.symm x) := by
    rw [RingEquiv.symm_apply_eq, he₁, RingEquiv.apply_symm_apply]
  have hσ' (x : A) : σ.symm (algebraMap A D x) = algebraMap A D (θ.symm x) := by
    rw [RingEquiv.symm_apply_eq, hσ, RingEquiv.apply_symm_apply]
  let u : L ⊗[A] D →+* L' ⊗[A] D :=
    tensorLift (Algebra.TensorProduct.includeLeftRingHom.comp e₁.toRingHom)
      ((Algebra.TensorProduct.includeRight : D →ₐ[A] L' ⊗[A] D).toRingHom.comp σ.toRingHom)
      fun x ↦ by
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, 
          he₁, hσ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeLeftRingHom_apply,
          Algebra.TensorProduct.includeRight_apply]
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := D),
          TensorProduct.smul_tmul]
  let v : L' ⊗[A] D →+* L ⊗[A] D :=
    tensorLift (Algebra.TensorProduct.includeLeftRingHom.comp e₁.symm.toRingHom)
      ((Algebra.TensorProduct.includeRight : D →ₐ[A] L ⊗[A] D).toRingHom.comp σ.symm.toRingHom)
      fun x ↦ by
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, 
          he₁', hσ', AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeLeftRingHom_apply,
          Algebra.TensorProduct.includeRight_apply]
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := D),
          TensorProduct.smul_tmul]
  have hvu : v.comp u = RingHom.id _ := ringHom_ext_tmul fun l d ↦ by simp [u, v]
  have huv : u.comp v = RingHom.id _ := ringHom_ext_tmul fun l d ↦ by simp [u, v]
  let e₂ : L ⊗[A] D ≃+* L' ⊗[A] D := RingEquiv.ofRingHom u v huv hvu
  have hcomp : algebraMap L' (L' ⊗[A] D) =
      (e₂.toRingHom.comp (algebraMap L (L ⊗[A] D))).comp e₁.symm.toRingHom := by
    ext l
    simp [e₂, u]
    rfl
  rw [← RingHom.etale_algebraMap, hcomp]
  refine etale_comp
    (RingHom.Etale.of_bijective e₁.symm.bijective)
    (etale_comp ?_ (RingHom.Etale.of_bijective e₂.bijective))
  rw [RingHom.etale_algebraMap]
  infer_instance

/-- If `T` is étale over `D(b)` and `b` is invertible in the `O`-algebra `L`, then `L ⊗ T` is
étale over `L`. -/
lemma etale_tensor_of_isUnit {O T : Type*} [CommRing O] [CommRing T] [Algebra O T] (b : O)
    [Algebra.Etale (Localization.Away b) (Localization.Away b ⊗[O] T)] (L : Type*) [CommRing L]
    [Algebra O L] (hb : IsUnit (algebraMap O L b)) : Algebra.Etale L (L ⊗[O] T) := by
  let _ : Algebra (Localization.Away b) L := (awayLift b hb).toRingHom.toAlgebra
  have : IsScalarTower O (Localization.Away b) L :=
    .of_algebraMap_eq fun x ↦ ((awayLift b hb).commutes x).symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange O (Localization.Away b) L L T)

end Transport

end RingTheory.DepthTwo
