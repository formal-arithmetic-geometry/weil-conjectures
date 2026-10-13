/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Sheaf.Algebra.TorDimensionShiftNatural
import Sheaf.Paper.TorLongExactFirstVariable
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Tor against ideal-power quotients is strictly pro-zero

Source: Stacks Project, More on Algebra, Lemma Tag 0911 (lemma-tor-strictly-pro-zero)
(blueprint: lem-weil-pbc-tor-strictly-pro-zero).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat


-- The boundary embeds Tor one into K ⊗ R/J and commutes with quotient reduction.
open scoped TensorProduct in
open CategoryTheory.Limits in
private theorem tor_one_reduction_zero
    {R : Type u} [CommRing R] (F X : ModuleCat.{u} R) [Module.Free R F]
    (q : F →ₗ[R] X) (hq : Function.Surjective q)
    (J J' : Ideal R) (hJJ' : J ≤ J')
    (hK : J • (⊤ : Submodule R F) ⊓ LinearMap.ker q ≤ J' • LinearMap.ker q) :
    ((Tor' (ModuleCat.{u} R) 1).obj X).map
      (ofHom (Submodule.factor hJJ')) = 0 := by
  let K := LinearMap.ker q
  obtain ⟨δ, hδ, hnat⟩ := tor_long_exact_first_variable K.subtype q
    K.injective_subtype hq (LinearMap.exact_subtype_ker_map q)
  have hinj (N : Type u) [AddCommGroup N] [Module R N] :
      Function.Injective (δ N) := by
    have hz := ModuleCat.subsingleton_of_isZero
      (isZero_Tor'_succ_of_projective (ModuleCat.{u} R) F (of R N) 0)
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro t ht
    obtain ⟨z, rfl⟩ := ((hδ N).1 t).mp ht
    rw [hz.elim z 0, map_zero]
  ext t
  apply hinj (R ⧸ J')
  change (δ (R ⧸ J')).hom _ = (δ (R ⧸ J')).hom 0
  rw [map_zero]
  have hn := DFunLike.congr_fun (hnat (R ⧸ J) (R ⧸ J') (Submodule.factor hJJ')) t
  change _ = (δ (R ⧸ J')) _ at hn
  rw [← hn]
  let e := TensorProduct.tensorQuotEquivQuotSMul K J
  obtain ⟨k, hk⟩ := (J • (⊤ : Submodule R K)).mkQ_surjective (e ((δ (R ⧸ J)) t))
  have ht : (δ (R ⧸ J)) t = k ⊗ₜ[R] (1 : R ⧸ J) := by
    apply e.injective
    rw [← hk]
    change Submodule.Quotient.mk k =
      TensorProduct.tensorQuotEquivQuotSMul K J (k ⊗ₜ[R] Ideal.Quotient.mk J 1)
    rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul]
  have hzero : K.subtype.rTensor (R ⧸ J) ((δ (R ⧸ J)) t) = 0 :=
    ((hδ (R ⧸ J)).2.1 _).mpr ⟨t, rfl⟩
  have hkJ : (k : F) ∈ J • (⊤ : Submodule R F) := by
    rw [ht] at hzero
    change (k : F) ⊗ₜ[R] Ideal.Quotient.mk J 1 = 0 at hzero
    have hh := congrArg (TensorProduct.tensorQuotEquivQuotSMul F J) hzero
    rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero] at hh
    exact (Submodule.Quotient.mk_eq_zero _).mp hh
  have hkJ' : k ∈ J' • (⊤ : Submodule R K) := by
    have hm : (k : F) ∈ (J' • (⊤ : Submodule R K)).map K.subtype := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
      exact hK ⟨hkJ, k.property⟩
    obtain ⟨k', hk', he⟩ := hm
    exact (K.injective_subtype he) ▸ hk'
  change (TensorProduct.map (LinearMap.id : K →ₗ[R] K)
    (Submodule.factor hJJ')) ((δ (R ⧸ J)) t) = 0
  rw [ht]
  change k ⊗ₜ[R] (Submodule.factor hJJ' (1 : R ⧸ J)) = 0
  have hone : Submodule.factor hJJ' (1 : R ⧸ J) = (1 : R ⧸ J') := rfl
  rw [hone]
  apply (TensorProduct.tensorQuotEquivQuotSMul K J').injective
  change TensorProduct.tensorQuotEquivQuotSMul K J'
    (k ⊗ₜ[R] Ideal.Quotient.mk J' 1) = _
  rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hkJ'

open CategoryTheory.Limits in
private theorem tor_pow_zero_same_universe
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (p : ℕ) (hp : 0 < p) (X : ModuleCat.{u} R) [Module.Finite R X] :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor' (ModuleCat.{u} R) p).obj X).map
        (ofHom (Submodule.factor (Ideal.pow_le_pow_right (I := I) (Nat.sub_le n c)))) = 0 := by
  induction p using Nat.case_strong_induction_on generalizing X with
  | hz => omega
  | hi p ih =>
    obtain ⟨t, q, hq⟩ := Module.Finite.exists_fin' R X
    let F := ModuleCat.of R (Fin t → R)
    let K := LinearMap.ker q
    by_cases hp : p = 0
    · subst p
      obtain ⟨c₀, hc₀⟩ := I.exists_pow_inf_eq_pow_smul K
      refine ⟨max c₀ 1, by omega, ?_⟩
      intro n hn
      apply tor_one_reduction_zero F X q hq
      rw [hc₀ n (by omega)]
      exact (smul_mono_right _ inf_le_right).trans
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))
    · let S := ModuleCat.shortComplexOfCompEqZero K.subtype q
        (by ext x; exact x.property)
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (LinearMap.exact_subtype_ker_map q) K.injective_subtype hq
      obtain ⟨θ, hθ⟩ := tor_dimension_shift_natural S hS p (by omega)
      obtain ⟨c, hc, hvan⟩ := ih p (by omega) (by omega) (of R K)
      refine ⟨c, hc, ?_⟩
      intro n hn
      apply (cancel_mono (θ (of R (R ⧸ I ^ (n - c)))).hom).mp
      rw [zero_comp, hθ, hvan n hn, comp_zero]

private noncomputable def liftQuotientEquiv
    {A : Type u} [CommRing A] (I : Ideal A) (J : Ideal (ULift.{v} A))
    (hI : I = J.map ULift.ringEquiv.toRingHom) :
    (ULift.{v} A ⧸ J) ≃ₗ[ULift.{v} A] ULift.{v} (A ⧸ I) := by
  let e := Ideal.quotientEquiv J I ULift.ringEquiv hI
  exact
    { toFun := fun x ↦ ULift.up (e x)
      invFun := fun x ↦ e.symm x.down
      left_inv := fun x ↦ e.symm_apply_apply x
      right_inv := fun x ↦ by cases x; simp
      map_add' := fun x y ↦ congrArg ULift.up (e.map_add x y)
      map_smul' := by
        intro a x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        apply ULift.ext
        change e (Ideal.Quotient.mk _ (a * b)) =
          a.down • e (Ideal.Quotient.mk _ b)
        rw [map_mul]
        rfl }

/-- For a finite module over a Noetherian ring, each positive-degree Tor system against
ideal-power quotients has uniformly vanishing sufficiently long transition maps.
Source: Stacks Project, More on Algebra, Lemma Tag 0911 (lemma-tor-strictly-pro-zero)
(blueprint: lem-weil-pbc-tor-strictly-pro-zero).

The lifts only place the two modules in the same universe. `Submodule.factor` is the
canonical quotient reduction, conjugated by `ULift.moduleEquiv`; `Tor'` derives in the
first variable, as in def-weil-pbc-tor-modules. Ideal powers include `I ^ 0 = ⊤`.

Proof, following Stacks Tag 0911:
1. Choose a finite free surjection `q : Rᵗ → M` using `Module.Finite.exists_fin'`.
   Its kernel `K` is finite because `R` is Noetherian.
2. The low-degree Tor exact sequence in the first variable gives an injective
   boundary `Tor₁(M,N) → K ⊗ N`, natural in `N`, because `Rᵗ` is projective.
   For `N = R/J`, tensor/quotient equivalence represents the boundary by `k ⊗ 1`.
   Exactness says `k ∈ K ∩ JRᵗ`. If this intersection lies in `J'K`, reduction to
   `R/J'` kills the boundary and hence the Tor map.
3. Artin–Rees gives `c₀` such that `IⁿRᵗ ∩ K ⊆ I^(n-c₀)K` for `n ≥ c₀`.
   Take `c = max c₀ 1`; monotonicity of ideal powers gives the base case uniformly
   for all `n ≥ c`.
4. Induct over positive degrees and all finite modules. The natural dimension shift
   `Tor_(p+1)(M,-) ≅ Tor_p(K,-)` transfers the inductive vanishing to `M`.
5. Apply this argument over `ULift A`. Explicit quotient equivalences identify
   `(ULift A)/(I.map ULift.up)^n` with `ULift (A/Iⁿ)` and commute with reductions,
   giving exactly the conjugated transition map in the statement. -/
theorem tor_quotient_pow_strictly_pro_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor' (ModuleCat (ULift.{v} A)) p).obj
        (ModuleCat.of (ULift.{v} A) (ULift.{u} M))).map
        (ModuleCat.ofHom
          (((ULift.moduleEquiv : ULift.{v} (A ⧸ I ^ (n - c)) ≃ₗ[ULift.{v} A]
              A ⧸ I ^ (n - c)).symm.toLinearMap).comp
            (((Submodule.factor (Ideal.pow_le_pow_right (Nat.sub_le n c)) :
              (A ⧸ I ^ n) →ₗ[A] (A ⧸ I ^ (n - c))).restrictScalars (ULift.{v} A)).comp
              (ULift.moduleEquiv : ULift.{v} (A ⧸ I ^ n) ≃ₗ[ULift.{v} A]
                A ⧸ I ^ n).toLinearMap))) = 0 := by
  let R := ULift.{v} A
  let f : A ≃+* R := ULift.ringEquiv.symm
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv A f
  have : Module.Finite R (ULift.{u} M) := by
    let l : M →ₛₗ[f.toRingHom] ULift.{u} M :=
      { toFun := ULift.up
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact Module.Finite.of_surjective l (fun x ↦ ⟨x.down, by cases x; rfl⟩)
  let J := I.map f.toRingHom
  let e (n : ℕ) : (R ⧸ J ^ n) ≃ₗ[R] ULift.{v} (A ⧸ I ^ n) := by
    apply liftQuotientEquiv (I ^ n) (J ^ n)
    rw [Ideal.map_pow]
    congr 1
    dsimp only [J]
    rw [Ideal.map_map]
    simp [f]
  obtain ⟨c, hc, hvan⟩ := tor_pow_zero_same_universe J p hp
    (of R (ULift.{u} M))
  refine ⟨c, hc, ?_⟩
  intro n hn
  let g : (A ⧸ I ^ n) →ₗ[A] (A ⧸ I ^ (n - c)) :=
    Submodule.factor (Ideal.pow_le_pow_right (Nat.sub_le n c))
  let gl : ULift.{v} (A ⧸ I ^ n) →ₗ[R] ULift.{v} (A ⧸ I ^ (n - c)) :=
    (ULift.moduleEquiv.symm.toLinearMap).comp
      ((g.restrictScalars R).comp ULift.moduleEquiv.toLinearMap)
  have hcomm : ofHom (Submodule.factor
      (Ideal.pow_le_pow_right (I := J) (Nat.sub_le n c))) ≫ (e (n - c)).toModuleIso.hom =
      (e n).toModuleIso.hom ≫ ofHom gl := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  change ((Tor' (ModuleCat R) p).obj (of R (ULift.{u} M))).map (ofHom gl) = 0
  let T := (Tor' (ModuleCat R) p).obj (of R (ULift.{u} M))
  apply (cancel_epi (T.map (e n).toModuleIso.hom)).mp
  rw [Limits.comp_zero, ← T.map_comp, ← hcomm, T.map_comp, hvan n hn, Limits.zero_comp]

end ModuleCat
