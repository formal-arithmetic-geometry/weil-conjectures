/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! # Differentials of a symmetric algebra

For an `R`-module `K`, the module of differentials of `Sym_R(K)` over `R` is
`Sym_R(K) ⊗[R] K`, with `d(ι k)` corresponding to `1 ⊗ k`
(`AlgebraicGeometry.symmetric_algebra_differentials`).

## Implementation details

An `R`-linear map `v : K → N` into a `Sym_R(K)`-module extends to a derivation by lifting
`k ↦ (ι k, v k)` to an algebra map into the square-zero extension `Sym_R(K) ⊕ N` and taking
its second component. The isomorphism is built from the derivation extending `k ↦ 1 ⊗ k` and
the scalar extension of `k ↦ d(ι k)`; both composites are checked on generators. No finiteness
or projectivity hypothesis on `K` is needed.

## References

* [Stacks, Tag 00DM]
* [Stacks, Tag 00RO]
* [Stacks, Tag 07M7]
-/

@[expose] public section

universe u
open scoped TensorProduct
namespace AlgebraicGeometry

private local instance symmetricOppositeModule (S N : Type u) [CommRing S] [AddCommGroup N]
    [Module S N] : Module Sᵐᵒᵖ N :=
  Module.compHom N ((RingHom.id S).fromOpposite fun a b => mul_comm a b)

private local instance symmetricCentralModule (S N : Type u) [CommRing S] [AddCommGroup N]
    [Module S N] : IsCentralScalar S N := ⟨fun _ _ => rfl⟩

private local instance symmetricOppositeTower (R S N : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] : IsScalarTower R Sᵐᵒᵖ N :=
  ⟨fun r s n => smul_assoc r (MulOpposite.unop s) n⟩

private noncomputable def symmetricDerivation
    (R K N : Type u) [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N] [Module (SymmetricAlgebra R K) N]
    [IsScalarTower R (SymmetricAlgebra R K) N] (v : K →ₗ[R] N) :
    Derivation R (SymmetricAlgebra R K) N := by
  let S := SymmetricAlgebra R K
  let f : S →ₐ[R] TrivSqZeroExt S N := SymmetricAlgebra.lift
    ((TrivSqZeroExt.inlAlgHom R S N).toLinearMap.comp (SymmetricAlgebra.ι R K) +
      ((TrivSqZeroExt.inrHom S N).restrictScalars R).comp v)
  have hf : (TrivSqZeroExt.fstHom R S N).comp f = AlgHom.id R S := by
    ext k
    simp [f]
    rfl
  have hf' (s : S) : (f s).fst = s := DFunLike.congr_fun hf s
  refine
    { toLinearMap := ((TrivSqZeroExt.sndHom S N).restrictScalars R).comp f.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := ?_ }
  intro a b
  change (f (a * b)).snd = a • (f b).snd + b • (f a).snd
  rw [map_mul, TrivSqZeroExt.snd_mul, hf', hf']
  simp

private theorem symmetricDerivation_ι
    (R K N : Type u) [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N] [Module (SymmetricAlgebra R K) N]
    [IsScalarTower R (SymmetricAlgebra R K) N] (v : K →ₗ[R] N) (k : K) :
    symmetricDerivation R K N v (SymmetricAlgebra.ι R K k) = v k := by
  simp [symmetricDerivation]

private theorem symmetricDerivation_ext
    (R K N : Type u) [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N] [Module (SymmetricAlgebra R K) N]
    [IsScalarTower R (SymmetricAlgebra R K) N]
    (d e : Derivation R (SymmetricAlgebra R K) N)
    (h : ∀ k, d (SymmetricAlgebra.ι R K k) = e (SymmetricAlgebra.ι R K k)) : d = e := by
  ext s
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι k => exact h k
  | mul a b ha hb => simp only [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The differentials of a symmetric algebra are the scalar extension of its
module of generators, without any finite generation or projectivity hypothesis: there is an
isomorphism `Ω[Sym_R(K)⁄R] ≃ Sym_R(K) ⊗[R] K` sending `d(ι k)` to `1 ⊗ k`. -/
theorem symmetric_algebra_differentials
    (R K : Type u) [CommRing R] [AddCommGroup K] [Module R K] :
    ∃ e : KaehlerDifferential R (SymmetricAlgebra R K) ≃ₗ[SymmetricAlgebra R K]
        (SymmetricAlgebra R K ⊗[R] K),
      ∀ k : K, e (KaehlerDifferential.D R (SymmetricAlgebra R K)
        (SymmetricAlgebra.ι R K k)) = 1 ⊗ₜ[R] k := by
  let S := SymmetricAlgebra R K
  let v : K →ₗ[R] S ⊗[R] K := TensorProduct.mk R S K 1
  let d := symmetricDerivation R K (S ⊗[R] K) v
  let f := d.liftKaehlerDifferential
  let g : S ⊗[R] K →ₗ[S] KaehlerDifferential R S :=
    ((KaehlerDifferential.D R S).toLinearMap.comp (SymmetricAlgebra.ι R K)).liftBaseChange S
  have hd (k : K) : d (SymmetricAlgebra.ι R K k) = 1 ⊗ₜ[R] k :=
    symmetricDerivation_ι R K _ v k
  have hgf : g.comp f = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply symmetricDerivation_ext R K _
    intro k
    simp [f, g, hd]
    rfl
  have hfg : f.comp g = LinearMap.id := by
    ext k
    change f (g (1 ⊗ₜ[R] k)) = 1 ⊗ₜ[R] k
    simp only [g, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply]
    change f (KaehlerDifferential.D R S (SymmetricAlgebra.ι R K k)) = _
    exact (Derivation.liftKaehlerDifferential_comp_D d _).trans (hd k)
  let e : KaehlerDifferential R S ≃ₗ[S] S ⊗[R] K :=
    { f with
      invFun := g
      left_inv := fun x => DFunLike.congr_fun hgf x
      right_inv := fun x => DFunLike.congr_fun hfg x }
  refine ⟨e, ?_⟩
  intro k
  exact (Derivation.liftKaehlerDifferential_comp_D d _).trans (hd k)

end AlgebraicGeometry
