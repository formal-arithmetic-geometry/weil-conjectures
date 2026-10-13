/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Algebra.Module.QuotientPrimaryComponentNoTorsion
import WeilConjectures.Paper.TorsionModuleFlatBaseChangeIso

/-!
# Flat base change of an ideal-power torsion submodule

Source: More on Algebra, Lemma 05EC, part (1)
(blueprint: lem-weil-pbc-torsion-submodule-flat-base-change-iso).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- For a flat ring map inducing an isomorphism modulo a finitely generated ideal,
base change identifies the ideal-power torsion submodule.

Source: More on Algebra, Lemma 05EC, part (1)
(blueprint: lem-weil-pbc-torsion-submodule-flat-base-change-iso).
Proof (the seven blueprint steps):
Mathlib writes scalar extension as `S ⊗[R] M` (the convention of `LinearMap.baseChange`,
the recorded declaration of def-weil-module-base-change); tensor symmetry identifies it
with the source's `M ⊗_R S`, and `m ↦ m ⊗ 1` becomes `m ↦ 1 ⊗ m`.
1. Scalar compatibility of `m ↦ 1 ⊗ m` (def-weil-module-base-change) sends every
   element annihilated by a power of I to one annihilated by the same power;
   `Ideal.primaryComponent.map` is precisely this restriction.
2. Put T = M[I^∞] and M' = M/T. The finitely generated ideal hypothesis gives
   M'[I] = 0 (lem-weil-pbc-quotient-by-power-torsion-no-torsion). Induct on n:
   if I^n x = 0, each element of I^(n-1) x is killed by I, hence is zero;
   induction then gives x = 0. Thus M'[I^∞] = 0.
3. Write I = (f₁, …, fₜ). For n > 0 the map x ↦ (fₖ^n x)ₖ on M' is injective:
   its kernel is annihilated by I^(t(n-1)+1), since every monomial of that degree
   has some exponent at least n. If t = 0, I = 0 and M' = 0.
4. Flatness (def-weil-pbc-flat-ring-map) preserves this injection after tensoring.
   Tensoring commutes with the finite product (lem-weil-pbc-tensor-finite-product),
   so the resulting injection is y ↦ (fₖ^n y)ₖ. Any I-power torsion element of
   M' ⊗ S is in its kernel, hence is zero.
5. Tensor the exact sequence 0 → T → M → M' → 0. Flatness preserves the first
   injection; right exactness (lem-weil-pbc-tensor-right-exact) gives exactness
   of 0 → T ⊗ S → M ⊗ S → M' ⊗ S → 0.
6. Since T is I-power torsion, T → T ⊗ S is bijective by
   lem-weil-pbc-torsion-module-flat-base-change-iso, using flatness and the
   isomorphism R/I → S/IS.
7. The comparison is the composite of this bijection with the injection in step 5,
   so is injective. A torsion element y of M ⊗ S has zero image in M' ⊗ S by
   step 4. Exactness lifts it to T ⊗ S, and step 6 writes this lift as x ⊗ 1
   for x ∈ T. This proves surjectivity. -/
theorem Ideal.primaryComponent_baseChange_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R) (hI : I.FG)
    (hflat : RingHom.Flat (algebraMap R S))
    (hquot : Function.Bijective
      (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
        (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Bijective
      ((Ideal.primaryComponent.map I (TensorProduct.mk R S M 1)) :
        Ideal.primaryComponent M I →ₗ[R]
          Ideal.primaryComponent (S ⊗[R] M) I) := by
  classical
  have hflat' : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  set T := primaryComponent M I with hT
  -- Step 6: `T → S ⊗ T` is bijective.
  have hTbij : Function.Bijective (TensorProduct.mk R S T 1) := by
    have htors : ∀ x : T, ∃ n : ℕ, 0 < n ∧ ∀ y : R, y ∈ I ^ n → y • x = 0 := by
      intro x
      obtain ⟨n, hn⟩ := (primaryComponent_mem M I (x : M)).mp x.2
      refine ⟨n + 1, n.succ_pos, fun y hy ↦ Subtype.ext ?_⟩
      exact (Submodule.mem_torsionBySet_iff _ _).mp hn
        ⟨y, Ideal.pow_le_pow_right n.le_succ hy⟩
    have h := RingTheory.torsionModule_flat_baseChange_bijective (T := T) (algebraMap R S)
      hflat I ⟨RingEquiv.ofBijective _ hquot, fun r ↦ by
        simp [Ideal.quotientMap_mk]⟩ htors
    have hcomp : (Module.compHom S (algebraMap R S) : Module R S) = Algebra.toModule :=
      Module.ext' _ _ fun r s ↦ (Algebra.smul_def r s).symm
    rw [hcomp] at h
    have hfun : ⇑(TensorProduct.mk R S T 1) =
        (TensorProduct.comm R T S) ∘ fun x : T ↦ x ⊗ₜ[R] (1 : S) := by
      funext x; simp
    rw [hfun]
    exact (TensorProduct.comm R T S).bijective.comp h
  -- Step 5: `S ⊗ T → S ⊗ M` is injective by flatness.
  have hinj : Function.Injective (T.subtype.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ T.injective_subtype
  -- Steps 3–4: `S ⊗ (M ⧸ T)` has no `I`-torsion.
  have hnotors : ∀ y : S ⊗[R] (M ⧸ T), (∀ a ∈ I, a • y = 0) → y = 0 := by
    obtain ⟨s, hs⟩ := hI
    let ψ : (M ⧸ T) →ₗ[R] (s → M ⧸ T) := LinearMap.pi fun k ↦ (k : R) • LinearMap.id
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply eq_zero_of_annihilated_quotient_primaryComponent I ⟨s, hs⟩ x
      have hle : I ≤ LinearMap.ker (LinearMap.toSpanSingleton R _ x) := by
        rw [← hs, Ideal.span_le]
        intro k hk
        simpa [ψ] using congrFun hx ⟨k, hk⟩
      intro a ha
      simpa using hle ha
    have hψ' := Module.Flat.lTensor_preserves_injective_linearMap (M := S) ψ hψ
    have key : ∀ (k : s) (y : S ⊗[R] (M ⧸ T)),
        TensorProduct.piRight R R S (fun _ : s ↦ M ⧸ T) (ψ.lTensor S y) k = (k : R) • y := by
      intro k y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [ψ, TensorProduct.tmul_smul]
      | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb, smul_add]
    intro y hy
    apply hψ'
    apply (TensorProduct.piRight R R S (fun _ : s ↦ M ⧸ T)).injective
    rw [map_zero, map_zero]
    funext k
    rw [key, hy k (hs ▸ Ideal.subset_span k.2)]
    rfl
  have hnotors' : ∀ y : S ⊗[R] (M ⧸ T), y ∈ primaryComponent _ I → y = 0 := by
    intro y hy
    obtain ⟨n, hn⟩ := (primaryComponent_mem _ I y).mp hy
    clear hy
    induction n generalizing y with
    | zero => simpa using (Submodule.mem_torsionBySet_iff _ _).mp hn ⟨1, by simp⟩
    | succ n ih =>
      apply ih
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      apply hnotors
      intro b hb
      rw [smul_smul]
      exact (Submodule.mem_torsionBySet_iff _ _).mp hn
        ⟨b * a, by rw [pow_succ']; exact Ideal.mul_mem_mul hb ha⟩
  -- Step 7: conclude.
  constructor
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    exact hTbij.1 (hinj (by simpa using h))
  · rintro ⟨y, hy⟩
    have h0 : T.mkQ.lTensor S y = 0 := hnotors' _ (primaryComponent_map_mem I _ ⟨y, hy⟩)
    obtain ⟨z, rfl⟩ := (lTensor_exact S (LinearMap.exact_subtype_mkQ T) T.mkQ_surjective y).mp h0
    obtain ⟨t, rfl⟩ := hTbij.2 z
    exact ⟨t, Subtype.ext (by simp)⟩
