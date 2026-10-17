/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Splitting
public import WeilConjectures.RingTheory.Smooth.SectionTruncation
public import WeilConjectures.RingTheory.Etale.DepthTwo.Diagonal.Basic
public import WeilConjectures.RingTheory.Etale.DepthTwo.Diagonal.LiftQuotient
public import WeilConjectures.RingTheory.AdicCompletionNoetherian
public import WeilConjectures.RingTheory.FiniteModuleComplete
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Étaleness through the diagonal

Let `O` be a Noetherian local ring and `R` a Noetherian local ring which is formally smooth and
flat over `O` (through `p₂ = algebraMap O R`) with a section `μ : R → O`, and let `τ` be an
involution of `R` with `μ ∘ τ = μ`; put `p₁ = τ ∘ p₂`. Geometrically, `R` is the local ring of
`X ×_S X` at a diagonal point `Δ(x)`, `p₁, p₂` are the two projections, `μ` is the diagonal and
`τ` swaps the factors; `O = 𝒪_{X,x}`.

Let `T` be a finite `O`-algebra and `a, b ∈ O` such that `(a, b)` is a regular pair on `T`,
`p₁ a = p₂ a` (`a` comes from the base `S`), and `T` is étale over `D(a)` and over `D(b)`. If there
is a prime `Q` of the completion `R^` of `R` along `ker μ` lying over the maximal ideal of `O`
(through `p₂`) with `p₁ b ∉ Q`, then `T` is étale over `O`
(`RingTheory.DepthTwo.etale_of_diagonal`).

Proof. The two pullbacks `T' = R ⊗_{p₁} T` and `T'' = R ⊗_{p₂} T` agree along the diagonal. Since
`T'` is étale over `D(a) ∪ D(p₁ b)` and `(a, p₁ b)` is a regular pair on every `T'' / Iⁿ T''`,
the identification `T' / I T' = T = T'' / I T''` lifts uniquely to `T' → T''^`
(as in `RingTheory.DepthTwo.exists_liftAlgHom`); symmetrically (exchanging the roles through `τ`)
it lifts to `T'' → T'^`, and by uniqueness of lifts the two lifts are inverse isomorphisms
`R^ ⊗ T' ≅ R^ ⊗ T''`. At `Q` the left side is étale (as `p₁ b` is invertible), hence so is
`R^_Q ⊗_O T`, and `T` is étale over `O` by faithfully flat descent along `O → R^_Q`.

This is the key step of purity for normal covers of a scheme smooth over a normal base
(`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace RingTheory.DepthTwo

section Swap

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra R O]

lemma le_comap_ker_algebraMap {τ : R ≃+* R} (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r) :
    RingHom.ker (algebraMap R O) ≤ (RingHom.ker (algebraMap R O)).comap τ.toRingHom := by
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    hτμ]
  exact hr

lemma sub_mem_ker_algebraMap {τ : R ≃+* R} (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r)
    (r : R) : τ r - r ∈ RingHom.ker (algebraMap R O) := by
  rw [RingHom.mem_ker, map_sub, hτμ, sub_self]

/-- The involution of the completion of `R` along the kernel of `R → O` induced by an involution
`τ` of `R` compatible with `R → O`. -/
noncomputable def completionSwap (τ : R ≃+* R) (hτ : ∀ r, τ (τ r) = r)
    (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r) :
    AdicCompletion (RingHom.ker (algebraMap R O)) R ≃+*
      AdicCompletion (RingHom.ker (algebraMap R O)) R :=
  RingEquiv.ofRingHom (adicCompletionMap _ τ.toRingHom (le_comap_ker_algebraMap hτμ))
    (adicCompletionMap _ τ.toRingHom (le_comap_ker_algebraMap hτμ))
    (RingHom.ext fun x ↦ adicCompletionMap_adicCompletionMap _ hτ x)
    (RingHom.ext fun x ↦ adicCompletionMap_adicCompletionMap _ hτ x)

lemma completionSwap_algebraMap (τ : R ≃+* R) (hτ : ∀ r, τ (τ r) = r)
    (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r) (r : R) :
    completionSwap τ hτ hτμ (algebraMap R _ r) = algebraMap R _ (τ r) :=
  adicCompletionMap_algebraMap τ.toRingHom (le_comap_ker_algebraMap hτμ) r

lemma completionSwap_sub_mem (τ : R ≃+* R) (hτ : ∀ r, τ (τ r) = r)
    (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r) [IsNoetherianRing R]
    (x : AdicCompletion (RingHom.ker (algebraMap R O)) R) :
    completionSwap τ hτ hτμ x - x ∈ (RingHom.ker (algebraMap R O)).map
      (algebraMap R (AdicCompletion (RingHom.ker (algebraMap R O)) R)) := by
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ (IsNoetherian.noetherian _), RingHom.mem_ker,
    map_sub, sub_eq_zero]
  exact evalOneₐ_adicCompletionMap (le_comap_ker_algebraMap hτμ) (sub_mem_ker_algebraMap hτμ) x


lemma completionSwap_completionSwap (τ : R ≃+* R) (hτ : ∀ r, τ (τ r) = r)
    (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r)
    (x : AdicCompletion (RingHom.ker (algebraMap R O)) R) :
    completionSwap τ hτ hτμ (completionSwap τ hτ hτμ x) = x :=
  adicCompletionMap_adicCompletionMap (le_comap_ker_algebraMap hτμ) hτ x
end Swap

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] [Algebra R O]
  [IsScalarTower O R O] [IsLocalRing O] [IsNoetherianRing O] [IsLocalRing R] [IsNoetherianRing R]
  [Algebra.FormallySmooth O R] [Module.Flat O R]

omit [IsNoetherianRing O] [IsLocalRing R] [Module.Flat O R] in
variable (O R) in
/-- The infinitesimal neighbourhoods of the section in the completion are flat. -/
lemma flat_quotient_pow_map_adicCompletion (n : ℕ) :
    Module.Flat O (AdicCompletion (RingHom.ker (algebraMap R O)) R ⧸
      ((RingHom.ker (algebraMap R O)).map
        (algebraMap R (AdicCompletion (RingHom.ker (algebraMap R O)) R))) ^ n) := by
  set I := RingHom.ker (algebraMap R O)
  set Rh := AdicCompletion I R
  have := Algebra.FormallySmooth.flat_quotient_pow_ker O R n
  let e₁ : (Rh ⧸ (I.map (algebraMap R Rh)) ^ n) ≃ₐ[Rh] Rh ⧸ (I ^ n).map (algebraMap R Rh) :=
    Ideal.quotientEquivAlgOfEq Rh (Ideal.map_pow _ _ _).symm
  let e₂ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot Rh (I ^ n)
  let e₃ := TensorProduct.comm R Rh (R ⧸ I ^ n)
  let e : (Rh ⧸ (I.map (algebraMap R Rh)) ^ n) ≃ₗ[O] (R ⧸ I ^ n) ⊗[R] Rh :=
    ((e₁.trans e₂).restrictScalars O).toLinearEquiv.trans (e₃.restrictScalars O)
  have : Module.Flat O ((R ⧸ I ^ n) ⊗[R] Rh) := Module.Flat.trans O (R ⧸ I ^ n) _
  exact Module.Flat.of_linearEquiv e

omit [IsNoetherianRing O] [IsLocalRing R] [Module.Flat O R] in
/-- The regularity of `(p₁ a, p₁ b)` on the quotients of `R^ ⊗_{p₂} T` by the powers of the ideal
of the diagonal. -/
lemma isRegularPair_quotient_pow {τ : R ≃+* R}
    (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r)
    {T : Type*} [CommRing T] [Algebra O T] {a b : O}
    (ha : τ (algebraMap O R a) = algebraMap O R a) (hT : IsRegularPair a b T) (n : ℕ) :
    IsRegularPair
      (algebraMap (AdicCompletion (RingHom.ker (algebraMap R O)) R)
        (AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T)
        (algebraMap R _ (τ (algebraMap O R a))))
      (algebraMap (AdicCompletion (RingHom.ker (algebraMap R O)) R)
        (AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T)
        (algebraMap R _ (τ (algebraMap O R b))))
      ((AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T) ⧸
        (((RingHom.ker (algebraMap R O)).map
          (algebraMap R (AdicCompletion (RingHom.ker (algebraMap R O)) R))).map
          (algebraMap (AdicCompletion (RingHom.ker (algebraMap R O)) R)
            (AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T))) ^ n) := by
  set I := RingHom.ker (algebraMap R O)
  set Rh := AdicCompletion I R
  set D := Rh ⊗[O] T
  set J := (I.map (algebraMap R Rh)).map (algebraMap Rh D)
  have h1 : IsRegularPair a b (D ⧸ J ^ n) := by
    have := flat_quotient_pow_map_adicCompletion O R n
    refine (hT.lTensor (Rh ⧸ (I.map (algebraMap R Rh)) ^ n)).of_linearEquiv ?_
    exact ((Algebra.TensorProduct.quotientTensorEquiv (R := O) O T Rh _).trans
      (Ideal.quotientEquivAlgOfEq O (Ideal.map_pow _ _ _))).toLinearEquiv
  have h2 := isRegularPair_algebraMap (A := D) h1
  have hpa : algebraMap Rh D (algebraMap R Rh (τ (algebraMap O R a))) = algebraMap O D a := by
    rw [ha, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨j, hj, hpb⟩ : ∃ j ∈ J, algebraMap Rh D (algebraMap R Rh (τ (algebraMap O R b))) =
      algebraMap O D b + j := by
    refine ⟨_, Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _
      (sub_mem_ker_algebraMap hτμ (algebraMap O R b))), ?_⟩
    rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply O R Rh,
      ← IsScalarTower.algebraMap_apply O Rh D]
    ring
  rw [hpa, hpb]
  refine h2.add_right (k := n) fun m ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hj n)

omit [IsScalarTower O R O] [IsLocalRing O] [IsNoetherianRing O] [IsLocalRing R]
  [Algebra.FormallySmooth O R]
  [Module.Flat O R] in
/-- `R^ ⊗ T` is complete along the ideal of the diagonal, for a finite `O`-algebra `T`. -/
lemma isAdicComplete_tensor (T : Type*) [CommRing T] [Algebra O T] [Module.Finite O T] :
    IsAdicComplete
      (((RingHom.ker (algebraMap R O)).map
          (algebraMap R (AdicCompletion (RingHom.ker (algebraMap R O)) R))).map
          (algebraMap (AdicCompletion (RingHom.ker (algebraMap R O)) R)
            (AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T)))
      (AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T) := by
  set I := RingHom.ker (algebraMap R O)
  set Rh := AdicCompletion I R
  have := AdicCompletion.isAdicComplete_self I (IsNoetherian.noetherian I)
  have := AdicCompletion.isNoetherianRing I
  have : IsAdicComplete (I.map (algebraMap R Rh)) (Rh ⊗[O] T) :=
    finite_module_complete_over_complete_noetherian Rh _ _
  exact (IsAdicComplete.map_algebraMap_iff _ _).2 this

omit [IsNoetherianRing O] [IsLocalRing R] [Module.Flat O R] in
/-- **The two pullbacks of `T` agree over the completion along the diagonal.** There is a ring
automorphism of `R^ ⊗_{p₂} T` which is semilinear with respect to the involution of `R^` induced
by `τ`; equivalently, an `R^`-algebra isomorphism `R^ ⊗_{p₁} T ≅ R^ ⊗_{p₂} T`. -/
theorem exists_semilinear_ringEquiv (τ : R ≃+* R) (hτ : ∀ r, τ (τ r) = r)
    (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r)
    {T : Type*} [CommRing T] [Algebra O T] [Module.Finite O T] {a b : O}
    (ha : τ (algebraMap O R a) = algebraMap O R a) (hT : IsRegularPair a b T)
    [Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[O] T)]
    [Algebra.Etale (Localization.Away b) (Localization.Away b ⊗[O] T)] :
    ∃ σ : AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T ≃+*
        AdicCompletion (RingHom.ker (algebraMap R O)) R ⊗[O] T,
      ∀ x, σ (algebraMap _ _ x) = algebraMap _ _ (completionSwap τ hτ hτμ x) := by
  set I := RingHom.ker (algebraMap R O)
  set Rh := AdicCompletion I R
  set D := Rh ⊗[O] T
  set f := algebraMap Rh D
  set Ih := I.map (algebraMap R Rh)
  set J := Ih.map f
  set θ := completionSwap τ hτ hτμ
  let p₁ : O →+* Rh := (algebraMap R Rh).comp (τ.toRingHom.comp (algebraMap O R))
  have hθ (x : O) : θ (algebraMap O Rh x) = p₁ x := by
    rw [IsScalarTower.algebraMap_apply O R Rh, completionSwap_algebraMap]
    rfl
  have : IsAdicComplete J D := isAdicComplete_tensor T
  have : Algebra.FormallyEtale O (Localization.Away a) := .of_isLocalization (Submonoid.powers a)
  have : Algebra.FormallyEtale O (Localization.Away b) := .of_isLocalization (Submonoid.powers b)
  have : Algebra.FormallyEtale O (Localization.Away a ⊗[O] T) := .comp O (Localization.Away a) _
  have : Algebra.FormallyEtale O (Localization.Away b ⊗[O] T) := .comp O (Localization.Away b) _
  have hJ (x : Rh) : Ideal.Quotient.mk J (f (θ x)) = Ideal.Quotient.mk J (f x) := by
    rw [Ideal.Quotient.eq, ← map_sub]
    exact Ideal.mem_map_of_mem _ (completionSwap_sub_mem τ hτ hτμ x)
  let iT : T →+* D := (Algebra.TensorProduct.includeRight : T →ₐ[O] D).toRingHom
  have hiT (t : T) : iT t = 1 ⊗ₜ t := rfl
  let φ₀ : T →+* D ⧸ J := (Ideal.Quotient.mk J).comp iT
  obtain ⟨ψ, hψ, hψφ⟩ := exists_ringHom_lift_of_isAdicComplete (f.comp p₁) J a b
    (fun n ↦ isRegularPair_quotient_pow hτμ ha hT n) φ₀ (by
      refine RingHom.ext fun x ↦ ?_
      have hx : iT (algebraMap O T x) = algebraMap O D x :=
        Algebra.TensorProduct.includeRight.commutes x
      simp only [φ₀, RingHom.comp_apply]
      rw [hx, ← hθ, hJ, ← IsScalarTower.algebraMap_apply])
  let σ₀ : D →+* D := tensorLift (f.comp θ.toRingHom) ψ fun x ↦ by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hθ,
      ← RingHom.comp_apply ψ, hψ]
    rfl
  have hσ₀f (r : Rh) : σ₀ (f r) = f (θ r) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      tensorLift_tmul, map_one, mul_one]
    rfl
  have hσ₀J : (Ideal.Quotient.mk J).comp σ₀ = Ideal.Quotient.mk J := by
    refine ringHom_ext_tmul fun r t ↦ ?_
    rw [RingHom.comp_apply, tensorLift_tmul, map_mul, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hJ,
      ← RingHom.comp_apply (Ideal.Quotient.mk J) ψ, hψφ, RingHom.comp_apply, ← map_mul, hiT,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let g : D →ₗ[Rh] D :=
    { toFun := fun x ↦ σ₀ (σ₀ x)
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_smul' := fun r x ↦ by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, RingHom.id_apply, hσ₀f, hσ₀f,
          completionSwap_completionSwap] }
  have hg (x : D) : x - g x ∈ Ih • (⊤ : Submodule Rh D) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← Ideal.Quotient.eq]
    exact ((RingHom.congr_fun hσ₀J (σ₀ x)).trans (RingHom.congr_fun hσ₀J x)).symm
  have := AdicCompletion.isAdicComplete_self I (IsNoetherian.noetherian I)
  have hbij := bijective_of_sub_mem_smul_top (IsAdicComplete.le_jacobson_bot Ih) g hg
  have hσ₀ : Function.Bijective σ₀ :=
    ⟨fun x y h ↦ hbij.1 (by simp only [g, LinearMap.coe_mk, AddHom.coe_mk, h]),
      fun y ↦ ⟨σ₀ (hbij.2 y).choose, (hbij.2 y).choose_spec⟩⟩
  exact ⟨RingEquiv.ofBijective σ₀ hσ₀, hσ₀f⟩

end RingTheory.DepthTwo
